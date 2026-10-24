From Stdlib Require Import Wf_nat PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Typing Require Import Definitions.
From Mctt.Algorithmic.Typing Require Export Functional.
From Mctt.Algorithmic.Subtyping Require Export Lemmas.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import Consequences.Rules.
From Mctt.Core.Consequences Require Import Consistency.
From Mctt.Core.Syntactic Require Import CoreInversions Corollaries Fresh.
From Mctt.Core.Syntactic.Levels Require Import LevelEq.
From Mctt.Core.Syntactic.Inductives Require Import IndCong IndConv.
From Mctt.Core.Syntactic.Levels Require Levels.
From Mctt.Algorithmic Require Import Strengthening.
From Mctt.Core.Syntactic.System.Global Require Import Modules Paths DescTyping LookupSound MemberWf.
From Mctt.Core.Semantic Require Import MemberWf Avoid.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
Import Domain_Notations Fixed_Notations Wk_Notations.

(** The universe premise of a [Π] rule, as its two cases: a large universe,
    or a small one at a level. *)
#[local]
Ltac destruct_univ :=
  repeat match goal with
         | HU : wf_is_univ _ _ _ ?U |- _ => is_var U; inversion HU; subst; clear HU
         end;
  repeat match goal with
         | H : context [exp_wk (a_typ ?i) ?φ] |- _ => change (exp_wk (a_typ i) φ) with (a_typ i) in H
         | H : context [exp_wk (a_univ ?L) ?φ] |- _ => change (exp_wk (a_univ L) φ) with (a_univ (exp_wk L φ)) in H
         | |- context [exp_wk (a_typ ?i) ?φ] => change (exp_wk (a_typ i) φ) with (a_typ i)
         | |- context [exp_wk (a_univ ?L) ?φ] => change (exp_wk (a_univ L) φ) with (a_univ (exp_wk L φ))
         end.

Section Fixed_GCtx.
  Context {GC : GCtx}.

#[local]
Hint Resolve functional_alg_type_infer : mctt.

End Fixed_GCtx.

(** The global context is well formed: a hypothesis says so, or a
    judgment in one of its contexts presupposes it. *)
Ltac gctx_wf_tac :=
  lazymatch goal with
  | |- wf_gstack ?T ?X =>
      first [ assumption
            | match goal with H : wf_ctx T X _ |- _ => exact (ctx_wf_gctx _ _ _ H) end
            | match goal with H : wf_exp T X _ _ _ |- _ => exact (ctx_wf_gctx _ _ _ (presup_exp_ctx H)) end
            | match goal with H : wf_modexp_eq T X _ _ _ |- _ => exact (ctx_wf_gctx _ _ _ (presup_modexp_eq_ctx H)) end
            | match goal with H : exists i, wf_exp T X _ _ _ |- _ =>
                let i := fresh "i" in let Hi := fresh "Hi" in
                destruct H as [i Hi]; exact (ctx_wf_gctx _ _ _ (presup_exp_ctx Hi)) end
            | solve [ mauto 3 ] ]
  end.

Ltac functional_alg_type_infer_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_alg_type_infer equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (?Γ ⊢a ?M ⟹ ?A1), H2 : (?Γ ⊢a ?M ⟹ ?A2) |- _ =>
      clean replace A2 with A1
        by first [ solve [ eapply functional_alg_type_infer; [| exact H1 | exact H2 ]; gctx_wf_tac ]
                 | solve [ eapply functional_alg_type_infer; [| exact H2 | exact H1 ]; gctx_wf_tac ]
                 | solve [ mauto 2 using functional_alg_type_infer ]
                 | tactic_error A2 A1 ];
      clear H2
  end.
Ltac functional_alg_type_infer_rewrite_clear := repeat functional_alg_type_infer_rewrite_clear1.

Section Fixed_GCtx.
  Context {GC : GCtx}.

(** ** Moving Levels Up the Sorts

    A level of a sort is a level of every larger sort ([wf_subtyp_level]). *)
Lemma wf_exp_level_up : forall {Γ M m n},
    m <= n ->
    Γ ⊢ M : Level@m ->
    Γ ⊢ M : Level@n.
Proof.
  intros * Hmn HM; assert (⊢ Γ) by (gen_presups; assumption).
  eapply wf_exp_subtyp'; [ exact HM | apply wf_subtyp_level; assumption ].
Qed.

Lemma wf_exp_eq_level_up : forall {Γ M M' m n},
    m <= n ->
    Γ ⊢ M ≈ M' : Level@m ->
    Γ ⊢ M ≈ M' : Level@n.
Proof.
  intros * Hmn HM; assert (⊢ Γ) by (gen_presups; assumption).
  eapply wf_exp_eq_subtyp'; [ exact HM | apply wf_subtyp_level; assumption ].
Qed.

(** ** Universe Normal Forms as Types

    The universe a type infers is a universe normal form [u]; as a term it is
    [unf_tm u], which is a small universe at a level term or a large one.
    The declarative rules ask for a large universe, which a small one is below
    ([wf_subtyp_small_large]): this is the cumulativity the algorithmic layer
    relies on. *)
Lemma wf_exp_unf_large : forall {Γ A} {u : unf},
    Γ ⊢ A : unf_tm u ->
    Γ ⊢ A : Typeω@(unf_large u).
Proof.
  intros * HA; destruct u as [L | n]; cbn in *; [| exact HA ].
  assert (exists k, Γ ⊢ Type⟨lvl_exp_of (fst L) (List.map atom_exp (snd L))⟩ : Typeω@k) as [k Hk]
    by (gen_presups; eauto 2).
  assert (⊢ Γ) by (gen_presups; assumption).
  destruct (wf_univ_lvl_inversion Hk) as [n Hn].
  eapply wf_exp_subtyp'; [ exact HA | eapply wf_subtyp_small_large; eassumption ].
Qed.

(** The normal form of a type is its own normal form. *)
Lemma nbe_ty_self : forall {Γ i A B},
    Γ ⊢ A : Typeω@i ->
    nbe_ty_f Γ A B ->
    nbe_ty_f Γ B B.
Proof.
  intros * HA Hn.
  assert (Γ ⊢ A ≈ B : Typeω@i) by (eapply soundness_ty'; eassumption).
  assert (HB : Γ ⊢ B : Typeω@i) by (gen_presups; assumption).
  destruct (soundness_ty HB) as (C & HC & _).
  assert (B = C) as <- by (exact (idempotent_nbe_ty HA Hn HC)).
  exact HC.
Qed.

(** A universe normal form whose level is a canonical level of a sort its
    level term has, each atom a level of its own sort: what the normal form
    of a universe is ([univ_nf_ws]). *)
Definition unf_ws (Γ : ctx) (u : unf) : Prop :=
  match u with
  | uns L => exists n, Γ ⊢ lvl_exp_of (fst L) (List.map atom_exp (snd L)) : Level@n /\
                    fst (fst L) <= n /\ @la_ws gc_deps gc_stack n Γ (snd L)
  | unl _ => True
  end.

Lemma unf_ws_of_nbe : forall {Γ u i},
    Γ ⊢ unf_tm u : Typeω@i ->
    nbe_ty_f Γ (unf_tm u) (univ_nf u) ->
    unf_ws Γ u.
Proof.
  intros * Hu Hn; destruct u as [[c xs] | j]; cbn in *; [| exact I ].
  exact (univ_nf_ws Hu Hn).
Qed.

(** The universe of a [Π] ([unf_pi_tm]).  Two small universes join in the
    small tier, the codomain's level bounded under the binder
    ([lvl_bound]): the bound, weakened back, is above the codomain's level
    ([lvl_bound_above]) and mentions no bound variable, so it is the weakening
    of a level of [Γ] ([level_nf_strengthen]); both parts are moved up to the
    join.  Otherwise the [Π] is at the large join. *)
Lemma wf_pi_unf_pi : forall {Γ A B} {u v : unf},
    Γ ⊢ A : unf_tm u ->
    Γ ▹ A ⊢ B : unf_tm v ->
    unf_ws (Γ ▹ A) v ->
    Γ ⊢ Π A B : unf_pi_tm u v.
Proof.
  intros * HA HB Hv.
  assert (⊢ Γ) by (gen_presups; assumption).
  assert (HAl : Γ ⊢ A : Typeω@(unf_large u)) by (apply wf_exp_unf_large; exact HA).
  assert (HBl : Γ ▹ A ⊢ B : Typeω@(unf_large v)) by (apply wf_exp_unf_large; exact HB).
  assert (HΓA : ⊢ Γ ▹ A) by mauto 2.
  destruct u as [[c xs] | i], v as [[d ys] | j]; cbn [unf_pi_tm unf_max unf_tm unf_large fst snd] in *.
  - (** The small join. *)
    destruct Hv as (nB & HLB0 & Hd & Hys); cbn [fst snd] in *.
    unfold lvl_bound; cbn [fst snd].
    set (LA := lvl_exp_of c (List.map atom_exp xs)) in *.
    set (cb := omax d (la_open_bound 0 ys)) in *.
    set (fp := la_fresh_part 0 ys) in *.
    set (LBs := lvl_exp_of cb (List.map atom_exp (List.map (map_level_atom (ne_unwk 0)) fp))).
    assert (exists nA, Γ ⊢ LA : Level@nA) as [nA HLA0]
      by (assert (exists k, Γ ⊢ Type⟨LA⟩ : Typeω@k) as [k Hk] by (gen_presups; eauto 2);
          eapply wf_univ_lvl_inversion; exact Hk).
    set (N := S (Nat.max nA nB)).
    assert (Hcb : fst cb <= N)
      by (subst cb N; apply omax_fst_le;
          [ lia | eapply Nat.le_trans; [ apply la_open_bound_fst; eapply la_ws_sorts; exact Hys | lia ] ]).
    assert (HysN : @la_ws gc_deps gc_stack N (Γ ▹ A) ys) by (eapply la_ws_mono; [| exact Hys ]; lia).
    assert (HfpN : @la_ws gc_deps gc_stack N (Γ ▹ A) fp) by (apply la_ws_fresh_part; exact HysN).
    assert (HLB : Γ ▹ A ⊢ lvl_exp_of d (List.map atom_exp ys) : Level@N) by (eapply wf_exp_level_up; [| exact HLB0 ]; lia).
    (** The bound, weakened back, is the level of its fresh atoms. *)
    assert (Hfresh : lvl_exp_of cb (List.map atom_exp fp) = LBs[↑]ʷ)
      by exact (nf_fresh_unwk 0 (nf_lvl cb fp) (la_fresh_part_fresh 0 ys)).
    assert (HLBl : Γ ▹ A ⊢ LBs[↑]ʷ : Level@N)
      by (rewrite <- Hfresh; apply lvl_exp_of_wf; [ exact Hcb | exact HΓA | apply la_ws_wf; exact HfpN ]).
    assert (Habove : Γ ▹ A ⊢ maxl (lvl_exp_of d (List.map atom_exp ys)) LBs[↑]ʷ ≈ LBs[↑]ʷ : Level@N).
    { rewrite <- Hfresh.
      apply lvl_exp_of_le; [ lia | exact Hcb | exact HΓA | exact HysN | exact HfpN |].
      exact (lvl_bound_above 0 (d, ys)). }
    assert (HLA : Γ ⊢ LA : Level@N) by (eapply wf_exp_level_up; [| exact HLA0 ]; lia).
    assert (HLBs : Γ ⊢ LBs : Level@N)
      by exact (level_nf_strengthen Γ A _ (nf_lvl cb (List.map (map_level_atom (ne_unwk 0)) fp)) HΓA HLBl).
    assert (Ht : Γ ⊢ maxl LA LBs : Level@N) by mauto 3.
    assert (Hw : Γ ▹ A ⊢ʷ ↑ : Γ) by mauto 2.
    eapply wf_pi_lvl; [ exact Ht | |].
    + eapply wf_exp_subtyp'; [ exact HA |].
      eapply wf_subtyp_suniv; [ assumption | exact HLA | exact Ht | apply lvl_sub_maxl_l; assumption ].
    + eapply wf_exp_subtyp'; [ exact HB |].
      assert (Hsub : Γ ⊢ Type⟨LBs⟩ ⊆ Type⟨maxl LA LBs⟩)
        by (eapply wf_subtyp_suniv; [ assumption | exact HLBs | exact Ht | apply lvl_sub_maxl_r; assumption ]).
      etransitivity; [| exact (wk_preserves_subtyp _ _ _ _ _ _ _ Hsub Hw) ].
      eapply wf_subtyp_suniv; [ exact HΓA | exact HLB | exact HLBl | exact Habove ].
  - destruct xs; cbn [unf_tm]; (apply wf_pi_large; [ eapply lift_exp_ge; [| exact HAl ]; lia | assumption ]).
  - destruct ys; cbn [unf_tm]; (apply wf_pi_large; [ assumption | eapply lift_exp_ge; [| exact HBl ]; lia ]).
  - apply wf_pi_large; [ eapply lift_exp_ge; [| exact HAl ]; lia | eapply lift_exp_ge; [| exact HBl ]; lia ].
Qed.

(** The universe of a [Π] is a type. *)
Lemma wf_unf_pi_tm : forall {Γ A B} {u v : unf},
    Γ ⊢ A : unf_tm u ->
    Γ ▹ A ⊢ B : unf_tm v ->
    unf_ws (Γ ▹ A) v ->
    exists k, Γ ⊢ unf_pi_tm u v : Typeω@k.
Proof.
  intros * HA HB Hv.
  pose proof (wf_pi_unf_pi HA HB Hv) as H.
  gen_presups; eauto 2.
Qed.

(** A premise [⟹ UA] with [is_univ_nf UA u] is sound as a typing at
    [unf_tm u], while the declarative rules ask for a large universe: such a
    hypothesis is lifted to [Typeω@(unf_large u)] ([wf_exp_unf_large]).
    [is_univ_nf_eq] turns the side condition into the shape of [UA]. *)
#[local] Tactic Notation "lift_univ_at" constr(Δ) constr(A) constr(u) :=
  repeat match goal with Hi : is_univ_nf ?UA u |- _ =>
    assert_fails (constr_eq UA (univ_nf u));
    rewrite (is_univ_nf_eq _ _ Hi) in * end;
  assert (Δ ⊢ A : unf_tm u)
    by (rewrite <- nf_to_exp_univ_nf; mauto 2);
  assert (Δ ⊢ A : a_typ (unf_large u))
    by (apply wf_exp_unf_large; eassumption).

(** Terms with, position by position, the normal forms of terms at the
    instances of a telescope are, position by position, equal to them. *)
Lemma nfs_agree_sound : forall Δ Γ0 Γ σ σ' Ms Rs,
    tele_ass Δ -> ⊢ (Δ ++ Γ0)%list -> Γ ⊢ˢ σ ≈ σ' : Γ0 ->
    List.length Ms = List.length Δ -> List.length Rs = List.length Δ ->
    (forall j N T, List.nth_error Ms j = Some N -> List.nth_error (tele_insts Δ σ Ms) j = Some T -> Γ ⊢ N : T) ->
    (forall j N T, List.nth_error Rs j = Some N -> List.nth_error (tele_insts Δ σ' Rs) j = Some T -> Γ ⊢ N : T) ->
    nfs_agree Γ Ms Rs (tele_insts Δ σ Ms) ->
    forall j N R T, List.nth_error Ms j = Some N -> List.nth_error Rs j = Some R ->
      List.nth_error (tele_insts Δ σ Ms) j = Some T -> Γ ⊢ N ≈ R : T.
Proof.
  induction Δ as [| e Δ IH] using List.rev_ind; intros * Hass HΔ Hσ HMl HRl HMs HRs Hag j N R T HN HR HT.
  - destruct Ms; [ destruct j; discriminate | discriminate ].
  - unfold tele_ass in Hass; apply List.Forall_app in Hass as [Hass He]; apply List.Forall_cons_iff in He as [[A0 ->] _].
    rewrite List.length_app in HMl, HRl; cbn in HMl, HRl.
    destruct Ms as [| M0 Ms]; [ cbn in HMl; lia |]; destruct Rs as [| R0 Rs]; [ cbn in HRl; lia |].
    rewrite tele_insts_snoc in HMs, HRs, Hag, HT.
    rewrite <- List.app_assoc in HΔ; cbn [List.app] in HΔ.
    destruct (ctx_decomp (ctx_app_wf_tail _ _ _ _ HΔ)) as [HΓ0 [k HA0]].
    inversion Hag as [| ? ? ? W ? ? ? HMW HRW Hag']; subst.
    assert (HM0 : Γ ⊢ M0 : A0[σ]) by (apply (HMs 0); reflexivity).
    assert (HR0' : Γ ⊢ R0 : A0[σ']) by (apply (HRs 0); reflexivity).
    assert (HAA : Γ ⊢ A0[σ] ≈ A0[σ'] : Typeω@k) by (eapply sub_eq_preserves_typ; [ exact HA0 | exact Hσ ]).
    assert (HR0 : Γ ⊢ R0 : A0[σ]) by (eapply wf_conv'; [ exact HR0' | symmetry; exact HAA ]).
    assert (HMR : Γ ⊢ M0 ≈ R0 : A0[σ])
      by (etransitivity; [ eapply soundness'; eassumption | symmetry; eapply soundness'; eassumption ]).
    destruct j as [| j]; cbn in HN, HR, HT.
    + injection HN as <-; injection HR as <-; injection HT as <-; exact HMR.
    + eapply (IH _ _ _ _ Ms Rs); [ exact Hass | exact HΔ | | cbn in HMl; lia | cbn in HRl; lia | | | exact Hag' | exact HN | exact HR | exact HT ].
      * eapply wf_sub_eq_extend; [ exact Hσ | exact HA0 | exact HM0 | exact HR0' | exact HMR ].
      * intros j' N' T' HN' HT'; apply (HMs (S j')); [ exact HN' | exact HT' ].
      * intros j' N' T' HN' HT'; apply (HRs (S j')); [ exact HN' | exact HT' ].
Qed.

(** The eliminator: its uniform parameters are typed, and the uniform
    arguments of its member's type at them are equal to those of the type
    its scrutinee infers ([nfs_agree_sound]), so the scrutinee is of the
    member's type ([mty_params_conv]); the blocks are typed at the uniform
    parameters, by the induction hypotheses.  The eliminator is of the
    motive's instance, before that is normalised. *)
Lemma alg_elim_typed : forall Γ M pc k Rs p D oq m Mm Dq Mk bm Bks Us Ns i,
    ⊢ Γ -> Γ ⊢ M : apps (a_ind pc k) (List.map nf_to_exp Rs) ->
    ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm ->
    im_ref p m Mm = (pc, k) -> ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length (List.map nf_to_exp Rs) = im_np Dq Mk ->
    List.nth_error Bks m = Some bm -> List.length Bks = List.length (ind_members D) ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
       ⊢ Γ -> forall i, Γ ⊢ T : Typeω@i -> Γ ⊢ U : T) ->
    nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) ->
    Ns = List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ->
    blocks_nm_ok D Bks ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list -> forall i',
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Typeω@i : Typeω@i' ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Z : Typeω@i) ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z
         (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ⊢ (elim_mctx p D j Mj Us ++ Γ)%list -> forall i', (elim_mctx p D j Mj Us ++ Γ)%list ⊢ Typeω@i : Typeω@i' ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ eb_motive b : Typeω@i) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       ⊢ (elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)%list -> forall i',
       (elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ elim_bty p j Mj c gs (eb_motive b) Us : Typeω@i' ->
       (elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ B : elim_bty p j Mj c gs (eb_motive b) Us) ->
    Γ ⊢ a_elim oq Us m Bks M : (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)].
Proof.
  intros * HΓ HM Hl Hg Hm Hr Hlq Hk HRl Hb HBl HUl HUs Hag -> HBnm HZt HZc HAt HBn HBa HBt.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hgw; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  (** The uniform parameters. *)
  assert (HUt : forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T -> Γ ⊢ U : T).
  { eapply tele_insts_typed_all; [ exact (dc_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓ) | apply wf_sub_id, HΓ |].
    intros j U X HU HX [iT HXt]; exact (HUs _ _ _ HU HX HΓ _ HXt). }
  (** The scrutinee, of the member's type. *)
  assert (exists kk, Γ ⊢ apps (a_ind pc k) (List.map nf_to_exp Rs) : Typeω@kk) as [kk Hkk] by (gen_presups; eauto).
  pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk Hkk HRl) as HRt.
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq HUl HUt) as [HPl HPt].
  destruct (params_typed_split _ _ Dq Hcq _ _ _ _ Hk HRl HRt) as [HRu _].
  assert (HRl' : List.length (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) = ind_nu Dq)
    by (rewrite List.length_firstn; unfold im_np in HRl; lia).
  assert (HPR : forall j N R X, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error (List.map nf_to_exp Rs) j = Some R ->
             List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some X -> Γ ⊢ N ≈ R : X).
  { intros j N R X HN HR HX.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPl; apply List.nth_error_Some; congruence).
    eapply (nfs_agree_sound (ind_uparams Dq) Γ Γ Id Id); [ exact (dc_ass _ Hcq) | exact (wf_uparams_app _ _ _ HDq Hcq _ HΓ)
           | apply wf_sub_eq_refl, wf_sub_id, HΓ | rewrite HPl; reflexivity | rewrite HRl'; reflexivity
           | exact HPt | exact HRu | exact Hag | exact HN | | exact HX ].
    rewrite List.nth_error_firstn; destruct (Nat.ltb_spec j (ind_nu Dq)); [ exact HR | lia ]. }
  destruct (mty_params_conv _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq Hk HUl HUt HRl HRt HPR) as [HNl HNt [iE HE]].
  assert (HM' : Γ ⊢ M : ind_mty p D m Us (List.skipn (ind_nu Dq) (List.map nf_to_exp Rs))) by (eapply wf_conv'; [ exact HM | exact HE ]).
  clear HPR HRu HPt HRt Hkk HE Hag HUs HRl' HPl HM.
  set (Ns := List.skipn (ind_nu Dq) (List.map nf_to_exp Rs)) in *.
  (** The blocks. *)
  assert (HUt' : forall j Mj, ind_member D j = Some Mj -> ⊢ (elim_mctx p D j Mj Us ++ Γ)%list)
    by (intros; eapply elim_mctx_wf; eassumption).
  assert (HBmot : forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
             (elim_mctx p D j Mj Us ++ Γ)%list ⊢ eb_motive b : Typeω@i)
    by (intros j Mj b Hj Hb0; exact (HAt _ _ _ Hj Hb0 (HUt' _ _ Hj) _ (wf_typ _ _ _ _ (HUt' _ _ Hj)))).
  assert (HAs : motives_typed gc_deps gc_stack Γ p D Us (blocks_motives Bks) i).
  { intros j Mj Hj; destruct (blocks_nth _ _ _ _ HBl Hj) as [b Hb0].
    rewrite (blocks_motives_nth _ _ _ Hb0); exact (HBmot _ _ _ Hj Hb0). }
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUt) as Hσ.
  assert (HBts : blocks_typed gc_deps gc_stack Γ p D Us Bks i).
  { constructor; [ exact HBl | exact HBnm | | exact HBmot | | exact HBn | | exact HBa | ].
    - intros j Mj b Z Hj Hb0 HZ.
      pose proof (HUt' _ _ Hj) as HC; unfold elim_mctx in HC; cbn [List.app] in HC.
      destruct (ctx_decomp HC) as [HΨ [jH HH]].
      pose proof (HZt _ _ _ _ Hj Hb0 HZ HΨ _ (wf_typ _ _ _ _ HΨ)) as HZi.
      destruct (HZc _ _ _ _ Hj Hb0 HZ) as (W & HZW & HHW).
      assert (HZH : (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list
                      ⊢ Z ≈ ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj))
                      : Typeω@(max i jH)).
      { etransitivity; [ eapply lift_exp_eq_max_left; eapply soundness_ty'; eassumption
                       | symmetry; eapply lift_exp_eq_max_right; eapply soundness_ty'; eassumption ]. }
      unfold elim_mctx.
      assert (Hext : gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ tele_sub (im_nparams Mj) (sb_of_list Id Us)
                                                ≈ tele_sub (im_nparams Mj) (sb_of_list Id Us))
        by (apply ctx_ext_refl; [ apply tele_ass_sub; exact (decl_closed_nparams_ass _ Hc _ _ Hj) | exact HΨ ]).
      eapply wf_ext_eq_ass; [ exact Hext | eapply lift_exp_max_left; exact HZi | exact HZH | eapply lift_exp_max_right; exact HH ].
    - intros j Mj Hj; apply ctx_ext_refl; [ exact (elim_mctx_ass _ _ _ _ _ Hc Hj) | exact (HUt' _ _ Hj) ].
    - intros j Mj c gs Hj Hcon; apply ctx_ext_refl; [ exact (elim_bctx_ass _ _ _ _ _ _ _ Hc Hj) | eapply elim_bctx_wf; eassumption ].
    - intros j Mj b c gs n B Hj Hb0 Hcon Hin.
      pose proof (wf_bty_sub _ _ _ _ _ _ _ _ _ _ _ _ Hgw HDs Hl Hj HΓ HUl HUt HUt' HAs Hcon) as Hbs.
      eapply HBt; [ exact Hj | exact Hb0 | exact Hcon | exact Hin | eapply elim_bctx_wf; eassumption
                  | exact (sub_preserves_exp _ _ _ _ _ _ _ (HBmot _ _ _ Hj Hb0) Hbs) ]. }
  exact (wf_elim_blocks _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hl Hg Hm Hb HBts HUl HUt HNl HNt HM').
Qed.

(** The eliminator is of the normal form of the motive's instance. *)
Lemma alg_elim_sound : forall Γ M pc k Rs p D oq m Mm Dq Mk bm Bks Us Ns i T,
    ⊢ Γ -> Γ ⊢ M : apps (a_ind pc k) (List.map nf_to_exp Rs) ->
    ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm ->
    im_ref p m Mm = (pc, k) -> ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
    List.length (List.map nf_to_exp Rs) = im_np Dq Mk ->
    List.nth_error Bks m = Some bm -> List.length Bks = List.length (ind_members D) ->
    List.length Us = ind_nu D ->
    (forall j U T, List.nth_error Us j = Some U -> List.nth_error (tele_insts (ind_uparams D) Id Us) j = Some T ->
       ⊢ Γ -> forall i, Γ ⊢ T : Typeω@i -> Γ ⊢ U : T) ->
    nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) ->
    Ns = List.skipn (ind_nu Dq) (List.map nf_to_exp Rs) ->
    blocks_nm_ok D Bks ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list -> forall i',
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Typeω@i : Typeω@i' ->
       (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢ Z : Typeω@i) ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       alg_ty_conv (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z
         (ind_mty p D j (List.map (fun U => U[wk_shiftn (im_nn Mj)]ʷ) Us) (vars_from 0 (im_nn Mj)))) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ⊢ (elim_mctx p D j Mj Us ++ Γ)%list -> forall i', (elim_mctx p D j Mj Us ++ Γ)%list ⊢ Typeω@i : Typeω@i' ->
       (elim_mctx p D j Mj Us ++ Γ)%list ⊢ eb_motive b : Typeω@i) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> brs_names (im_cons Mj) (eb_brs b)) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       n = (im_nn Mj + List.length gs + cargs_nrec gs)%nat) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       ⊢ (elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)%list -> forall i',
       (elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ elim_bty p j Mj c gs (eb_motive b) Us : Typeω@i' ->
       (elim_bctx p D Mj gs (blocks_motives Bks) Us ++ Γ)%list ⊢ B : elim_bty p j Mj c gs (eb_motive b) Us) ->
    nbe_ty_f Γ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] T ->
    Γ ⊢ a_elim oq Us m Bks M : T /\ exists j, Γ ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] : Typeω@j.
Proof.
  intros * HΓ HM Hl Hg Hm Hr Hlq Hk HRl Hb HBl HUl HUs Hag HNs HBnm HZt HZc HAt HBn HBa HBt HT.
  pose proof (alg_elim_typed _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΓ HM Hl Hg Hm Hr Hlq Hk HRl Hb HBl HUl HUs Hag HNs
                HBnm HZt HZc HAt HBn HBa HBt) as Hel.
  destruct (presup_exp_typ Hel) as [j Hj].
  split; [ eapply wf_conv'; [ exact Hel | eapply soundness_ty'; eassumption ] | exists j; exact Hj ].
Qed.

(** What a checked body is: the body, read in an extension [Ψ] of [Γ0], is
    its expansion, which extends [Ψ], and the targets of its opens are
    well-formed modules where they stand. *)
Record abody_ok (Γ0 Ψ Γ : ctx) (Φ Φx : gmod) : Prop := mk_abody_ok
  { abo_xp : body_xp gc_deps gc_stack Γ Φ Φx
  ; abo_ext : gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ body_ctx Φx ++ Ψ ≈ body_ctx Φx ++ Ψ
  ; abo_opens : forall k Ψo H, List.nth_error (body_opens Φ Φx) k = Some (Ψo, H) -> gc_deps ⍮ gc_stack ⍮ Ψo ++ Γ ⊢ᵐ H ≈ H }.

Definition alg_body_sound (Γ : ctx) (Φ Φx : gmod) : Prop :=
  forall Γ0 Ψ, Γ = Ψ ++ Γ0 -> ⊢ Γ0 -> gc_deps ⍮ gc_stack ⍮ Γ0 ⊢ˣ Ψ ≈ Ψ -> abody_ok Γ0 Ψ Γ Φ Φx.

Lemma abody_nil_sound : forall Γ, alg_body_sound Γ gm_nil gm_nil.
Proof.
  intros Γ Γ0 Ψ -> HΓ0 HΨ; constructor; [ constructor | exact HΨ |].
  intros [| k] * Hk; discriminate.
Qed.

Lemma abody_def_sound : forall Γ Φ Φx x b pv A M i,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ A : Typeω@i) ->
    (⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ M : A) ->
    alg_body_sound Γ (gm_ext Φ x (ge_def b pv A (Some M))) (gm_ext Φx x (ge_def b pv A (Some M))).
Proof.
  intros * IH HA HM Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HA HC); specialize (HM HC); rewrite List.app_assoc in HA, HM.
  constructor; [ constructor; exact Hbx | | exact Ho ].
  cbn [body_ctx List.app].
  eapply wf_ext_eq_def; [ exact HX | exact HA | apply wf_exp_eq_refl; exact HA | exact HM | apply wf_exp_eq_refl; exact HM
                        | exact HA | exact HM ].
Qed.

Lemma abody_mod_sound : forall Γ Φ Φx x pm U,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Γ ⊢ᵘ U ≈ U) ->
    alg_body_sound Γ (gm_ext Φ x (ge_mod pm U)) (gm_ext Φx x (ge_mod pm U)).
Proof.
  intros * IH HU Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HU HC); rewrite List.app_assoc in HU.
  constructor; [ constructor; exact Hbx | | exact Ho ].
  cbn [body_ctx List.app]; apply wf_ext_eq_mod; [ exact HX | exact HU | exact HU ].
Qed.

Lemma abody_open_sound : forall Γ Φ Φx H R Rm its gs,
    alg_body_sound Γ Φ Φx ->
    (⊢ body_ctx Φx ++ Γ -> gc_deps ⍮ gc_stack ⍮ body_ctx Φx ++ Γ ⊢ᵐ H ≈ H) ->
    mdenote gc_deps gc_stack (body_ctx Φx ++ Γ) H R ->
    ds_mod gc_deps gc_stack R = Some Rm ->
    items_gen gc_deps gc_stack false (body_ctx Φx ++ Γ) H its gs ->
    items_ok its ->
    alg_body_sound Γ (gm_open Φ H its) (gens_append Φx 0 gs).
Proof.
  intros * IH HH HR HRm Hg Hok Γ0 Ψ -> HΓ0 HΨ.
  destruct (IH _ _ eq_refl HΓ0 HΨ) as [Hbx HX Ho].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  specialize (HH HC).
  constructor; [ econstructor; eassumption | exact (gens_ext_wf _ _ _ _ _ _ Hg HH HX) |].
  cbn [body_opens]; rewrite <- (items_gen_length _ _ _ _ _ _ _ Hg), gm_dropn_gens_append.
  intros [| k] * Hk; cbn in Hk; [ injection Hk as <- <-; exact HH | exact (Ho _ _ _ Hk) ].
Qed.

(** A body: its parameters, its expansion, and the targets of its opens are
    well-formed, so it is a unit ([unit_full_body]). *)
Lemma aunit_body_sound : forall Γ Δ Φ Φx,
    (⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Δ ≈ Δ) -> tele_ass Δ -> alg_body_sound (Δ ++ Γ) Φ Φx ->
    body_shape Φ Φ -> body_shape Φx Φx -> List.NoDup (gm_names Φ) ->
    ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ gu_open Δ Φ ≈ gu_open Δ Φ.
Proof.
  intros * HΔ Ht HB Hs Hsx Hn HΓ.
  destruct (HB _ _ eq_refl HΓ (HΔ HΓ)) as [Hbx HX Ho].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite <- List.app_assoc in HC.
  exact (unit_eq_of_full _ _ _ _ (unit_full_body _ _ _ _ _ _ Hbx HC Ho Ht Hs Hsx Hn)).
Qed.

(** A tuple whose annotation normalises to a record type at [Rs], its
    fields checked at their types at [Rs]: of that normal form. *)
Lemma alg_tuple_sound : forall Γ T (fs : list (String.string * exp)) p Rs R i,
    ⊢ Γ -> Γ ⊢ T : Typeω@i -> nbe_ty_f Γ T (nf_record p Rs) -> record_lookup gc_deps gc_stack p = Some R ->
    List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       ⊢ Γ -> forall i, Γ ⊢ U[sb_of_list Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))] : Typeω@i ->
       Γ ⊢ M : U[sb_of_list Id (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs))]) ->
    Γ ⊢ a_tuple T fs : nf_record p Rs.
Proof.
  intros * HΓ HT Hn Hl Hfs HMs.
  assert (HTR : Γ ⊢ T ≈ nf_record p Rs : Typeω@i) by (eapply soundness_ty'; eassumption).
  cbn [nf_to_exp] in HTR |- *.
  assert (HRa : Γ ⊢ apps (a_record p) (List.map nf_to_exp Rs) : Typeω@i) by (gen_presups; assumption).
  pose proof (wf_record_apps_len _ _ _ _ _ Hl HRa) as HRl.
  pose proof (wf_record_apps_inv _ _ _ _ _ Hl HRa HRl) as HRt.
  destruct (record_former_typed _ _ _ HΓ Hl) as [j [Hrt _]].
  pose proof (tuple_fields_typed_seq _ _ _ _ _ Hrt Hl HRl Hfs HRt
                ltac:(intros * Hk Hfk [i' Hi']; exact (HMs _ _ _ _ Hk Hfk HΓ _ Hi'))) as HFt.
  eapply wf_conv'; [ eapply wf_tuple; [ exact HT | exact HTR | exact Hrt | exact Hl | exact HRl | exact HRt | exact Hfs | exact HFt ]
                   | exact HTR ].
Qed.

(** A projection of an element of a record type at [Rs]: of its field's
    type at [Rs] and the projections before it, which is a type. *)
Lemma alg_proj_typed : forall Γ M p Rs R f k U,
    ⊢ Γ -> Γ ⊢ M : nf_record p Rs -> record_lookup gc_deps gc_stack p = Some R ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    exists m, Γ ⊢ U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)] : Typeω@m /\
      Γ ⊢ a_proj f M : U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)].
Proof.
  intros * HΓ HM Hl Hfk; cbn [nf_to_exp] in HM.
  assert (exists i, Γ ⊢ apps (a_record p) (List.map nf_to_exp Rs) : Typeω@i) as [i HRa] by (gen_presups; eauto 2).
  pose proof (wf_record_apps_len _ _ _ _ _ Hl HRa) as HRl.
  pose proof (wf_record_apps_inv _ _ _ _ _ Hl HRa HRl) as HRt.
  destruct (record_former_typed _ _ _ HΓ Hl) as [j [Hrt _]].
  destruct (record_sort_large _ _ _ _ _ _ Hrt Hl HRl HRt) as [m Hm].
  destruct (record_proj_cong_at _ _ _ M M p R _ m k f U (wf_exp_eq_refl HM) Hrt Hl HRl HRt Hm Hfk) as [HUU Hpp].
  exists m; split; gen_presups; assumption.
Qed.

(** So it is of the normal form of that type. *)
Lemma alg_proj_sound : forall Γ M p Rs R f k U W,
    ⊢ Γ -> Γ ⊢ M : nf_record p Rs -> record_lookup gc_deps gc_stack p = Some R ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    nbe_ty_f Γ U[sb_of_list Id (List.map nf_to_exp Rs ++ record_pre R k M)] W ->
    Γ ⊢ a_proj f M : W.
Proof.
  intros * HΓ HM Hl Hfk Hn.
  destruct (alg_proj_typed _ _ _ _ _ _ _ _ HΓ HM Hl Hfk) as (m & HUt & Hp).
  eapply wf_conv'; [ exact Hp | eapply soundness_ty'; eassumption ].
Qed.

Lemma alg_type_sound :
  (forall {Γ A M}, Γ ⊢a M ⟸ A -> ⊢ Γ -> forall i, Γ ⊢ A : Typeω@i -> Γ ⊢ M : A) /\
    (forall {Γ A M}, Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A) /\
    (forall {Γ Ψ}, Γ ⊢aˣ Ψ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ) /\
    (forall {Γ U}, Γ ⊢aᵘ U -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) /\
    (forall {Γ Φ Φx}, Γ ⊢aᵇ Φ ⇝ Φx -> alg_body_sound Γ Φ Φx) /\
    (forall {Γ H}, Γ ⊢aᵐ H -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H).
Proof.
  (** Every premise that asks for a type is [⟹ univ_nf u], so its soundness
      is a typing at [unf_tm u]. *)
  apply alg_type_mut_ind; intros; simpl_univ_nf; destruct_let_ann; simpl_let_guards;
    cbn [unf_tm] in *;
    (** Bodies, by their own lemmas. *)
    try solve [ apply abody_nil_sound | eapply abody_mod_sound; eassumption | eapply abody_open_sound; eassumption
              | eapply aunit_body_sound; eassumption ];
    (** The eliminator has its own lemma ([alg_elim_sound]). *)
    try lazymatch goal with |- _ ⊢ a_elim _ _ _ _ _ : _ => fail | _ => mautosolve 4 end.
  (** The cases below are dispatched on the shape of the goal rather than by
      position: a new rule would silently renumber positional selectors. *)
  all: lazymatch goal with
  (** An unannotated [let]: the type its body infers is a type. *)
  | |- _ ⊢ ℓ ≔ _ in _ : _ =>
      rename W into A;
      assert (HM : Γ ⊢ M : A) by eauto;
      assert (exists i, Γ ⊢ (A : exp) : Typeω@i) as [i HA] by (gen_presups; eauto 2);
      assert (⊢ Γ ▸ (A : exp) ≔ M) by mauto 3;
      assert (Γ ▸ (A : exp) ≔ M ⊢ B : C) by eauto;
      assert (exists j, Γ ▸ (A : exp) ≔ M ⊢ C : Typeω@j) as [j HCj] by (gen_presups; eauto 2);
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCj (wf_sub_single_def _ _ _ _ _ _ HA HM)) as HCs;
      assert (Γ ⊢ C[Id,,M] ≈ D : Typeω@j) as <- by mauto 3 using soundness_ty';
      eapply wf_let; [ exact HA | exact HM | eassumption | solve_let_ann ]
  (** The type former, a constructor and the eliminator. *)
  | |- _ ⊢ a_ind _ _ : _ =>
      match goal with Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, HΓ : ⊢ ?G |- _ =>
        destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc];
        destruct (ind_ty_typed _ _ _ _ _ _ HD Hc Hk HΓ) as [j Hj];
        eapply wf_conv'; [ eapply wf_ind; eassumption | eapply soundness_ty'; eassumption ] end
  | |- _ ⊢ a_con _ _ _ : _ =>
      match goal with Hl : ind_lookup _ _ _ = Some ?D, Hk : ind_member ?D _ = Some _, Hcon : ind_con _ _ = Some ?gs,
                      HΓ : ⊢ ?G |- _ =>
        destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) (decls_of_ctx _ _ _ HΓ) Hl Hk Hcon HΓ) as [j Hj];
        eapply wf_conv'; [ eapply wf_con_closed; eassumption | eapply soundness_ty'; eassumption ] end
  | |- _ ⊢ a_elim _ _ _ _ _ : _ =>
      match goal with
      | HM : ⊢ ?G -> ?G ⊢ ?M : _, HΓ : ⊢ ?G, Hg : elim_grp ?D ?oq ?p ?m |- ?G ⊢ a_elim ?oq _ ?m _ ?M : _ =>
          eapply proj1; eapply (alg_elim_sound G M _ _ _ p D oq m); first [ exact HΓ | exact (HM HΓ) | eassumption ]
      end
  (** A record's type former, a tuple and a projection. *)
  | |- _ ⊢ a_record _ : _ =>
      match goal with Hl : record_lookup _ _ _ = Some _, HΓ : ⊢ ?G |- _ =>
        let j := fresh "j" in let Hrt := fresh "Hrt" in let Hj := fresh "Hj" in
        destruct (record_former_typed _ _ _ HΓ Hl) as [j [Hrt Hj]];
        eapply wf_conv'; [ exact Hrt | eapply soundness_ty'; eassumption ] end
  | |- _ ⊢ a_tuple ?T _ : _ =>
      match goal with Hu : is_univ_nf _ ?u, HΓ : ⊢ ?G |- _ =>
        lift_univ_at G T u;
        eapply alg_tuple_sound; [ exact HΓ | eassumption | eassumption | eassumption | eassumption | intros; eauto ] end
  | |- _ ⊢ a_proj _ ?M : _ =>
      match goal with HM : ⊢ ?G -> ?G ⊢ M : _, HΓ : ⊢ ?G, Hfk : List.nth_error (record_fields _) _ = Some _ |- _ =>
        eapply alg_proj_sound; [ exact HΓ | exact (HM HΓ) | eassumption | exact Hfk | eassumption ] end
  (** A module [let]. *)
  | |- _ ⊢ ℓₘ _ in _ : _ =>
      assert (HU : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) by eauto;
      assert (⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU);
      assert (Γ ▹ₘ U ⊢ B : C) by eauto;
      assert (exists j, Γ ▹ₘ U ⊢ C : Typeω@j) as [j HCj] by (gen_presups; eauto 2);
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCj (wf_sub_single_mod _ _ _ _ HU)) as HCs;
      assert (Γ ⊢ C[Id ,,ₘ me_lit U] ≈ D : Typeω@j) as <- by mauto 3 using soundness_ty';
      eapply wf_let_mod; eauto
  (** A member, at the normal form of the type its module's description
      reads. *)
  | Hm : mdenote _ _ _ (me_mem ?H0 ?x0) _, Ht : ds_ty _ _ _ = Some _ |- _ ⊢ a_mem _ _ : _ =>
      assert (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H0 ≈ H0) by eauto;
      destruct (member_wf _ _ _ _ _ HH Hm Ht) as ([i HA] & _ & HMt);
      assert (Γ ⊢ A ≈ B : Typeω@i) as <- by mauto 3 using soundness_ty';
      exact HMt
  (** An extension by an assumption, a definition or a module. *)
  | |- wf_ext_eq _ _ _ (_ ▹ _) _ =>
      match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
        pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end;
      lift_univ_at (Ψ ++ Γ) A u;
      eapply wf_ext_eq_ass; [ eauto | eauto | eapply wf_exp_eq_refl; eauto | eauto ]
  | |- wf_ext_eq _ _ _ (_ ▸ _ ≔ _) _ =>
      match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
        pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end;
      lift_univ_at (Ψ ++ Γ) A u;
      assert (Ψ ++ Γ ⊢ M : A) by eauto;
      eapply wf_ext_eq_def;
        [ eauto | eauto | eapply wf_exp_eq_refl; eauto | eauto
        | eapply wf_exp_eq_refl; eauto | eauto | eauto ]
  | |- wf_ext_eq _ _ _ (_ ▹ₘ _) _ =>
      match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
        pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end;
      eapply wf_ext_eq_mod; eauto
  (** A unit that is an alias. *)
  | |- wf_unit_eq _ _ _ _ _ =>
      match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
        pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end;
      eapply wf_unit_eq_alias; eauto
  (** A module expression applied. *)
  | Hm : mdenote _ _ _ ?H0 _, Htl : ds_mtele _ _ _ = Some _, Hv : tele_view _ = Some _
    |- wf_modexp_eq _ _ _ (me_app _ _) _ =>
      assert (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H0 ≈ H0) by eauto;
      destruct (mtele_head_wf _ _ _ _ _ _ HH Hm Htl Hv) as [i HB];
      assert (Γ ⊢ N : B) by eauto;
      eapply wf_me_app; eauto using wf_exp_eq_refl
  (** A selection that is a module. *)
  | Hm : mdenote _ _ _ (me_mem ?H0 _) _, Htl : ds_mtele _ _ _ = Some _ |- wf_modexp_eq _ _ _ _ _ =>
      assert (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H0 ≈ H0) by eauto;
      eapply wf_me_mem; eassumption
  (** A loaded unit. *)
  | Hm : mdenote _ _ _ (me_unit _) _ |- wf_modexp_eq _ _ _ _ _ =>
      let Hu := fresh "Hu" in
      destruct (mdenote_unit_inv _ _ ltac:(eapply ctx_wf_gctx; eassumption) _ _ _ Hm) as (? & ? & Hu & _);
      eapply wf_me_unit; [ eauto | exact Hu ]
  | _ => idtac
  end.
  (** The join of two levels: both arguments move to the larger sort. *)
  all: try match goal with
    | HM : ⊢ ?G -> ?G ⊢ ?M : _, HN : ⊢ ?G -> ?G ⊢ ?N : _, HG : ⊢ ?G |- ?G ⊢ maxl ?M ?N : _ =>
        pose proof (HM HG) as HMl; pose proof (HN HG) as HNl; cbn [nf_to_exp] in HMl, HNl |- *;
        match type of HMl with _ ⊢ _ : Level@?m => match type of HNl with _ ⊢ _ : Level@?n =>
          apply wf_maxl; [ apply (wf_exp_level_up (m := m)); [ lia | exact HMl ]
                         | apply (wf_exp_level_up (m := n)); [ lia | exact HNl ] ] end end
    end.
  (** A small universe: its level is a level, and the universe above is the
      normal form of [Type⟨succl M⟩]. *)
  all: try match goal with
    | Hn : nbe_ty_f _ (a_univ (succl ?M)) ?W, HM : ⊢ ?G -> ?G ⊢ ?M : _, HG : ⊢ ?G |- ?G ⊢ a_univ ?M : _ =>
        pose proof (HM HG) as HMl; cbn [nf_to_exp] in HMl;
        assert (Γ ⊢ Type⟨succl M⟩ : Typeω@0)
          by (eapply wf_univ_large_tm; [ assumption | eapply wf_succl; exact HMl ]);
        assert (Γ ⊢ Type⟨succl M⟩ ≈ W : Typeω@0) as <- by mauto 3 using soundness_ty';
        eapply wf_univ; exact HMl
    end.
  - assert (Γ ⊢ M : A) by mauto 3.
    assert (exists i, Γ ⊢ A : Typeω@i) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Typeω@(max i j)) by mauto 3 using lift_exp_max_right.
    assert (Γ ⊢ B : Typeω@(max i j)) by mauto 3 using lift_exp_max_left.
    assert (Γ ⊢ A ⊆ B) by mauto 2 using alg_subtyping_sound.
    mauto 3.
  - assert (Γ ⊢ ⊥ : Typeω@0) by mauto 2.
    assert (⊢ Γ ▹ ⊥) by mauto 2.
    lift_univ_at (Γ ▹ ⊥) A u.
    assert (Γ ⊢ M : ⊥) by mauto 2.
    assert (Γ ⊢ A[Id,,M] : Typeω@(unf_large u)) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ B : Typeω@(unf_large u)) as <- by mauto 4 using soundness_ty'.
    mauto 4.
  (** A [Π] is at the normal form of the join of the universes of its
      parts. *)
  - lift_univ_at Γ A u.
    assert (⊢ Γ ▹ A) by mauto 3.
    (** The codomain's universe, normalised: a type of it is a type of its
        normal form, whose level's atoms are of the sorts they carry. *)
    assert (HBU : Γ ▹ A ⊢ B : UB) by mauto 2.
    assert (exists k, Γ ▹ A ⊢ (UB : exp) : Typeω@k) as [kB HUB] by (gen_presups; eauto 2).
    match goal with HnB : nbe_ty_f (Γ ▹ A) (nf_to_exp UB) ?UB' |- _ =>
      assert (Γ ▹ A ⊢ (UB : exp) ≈ UB' : Typeω@kB) by (eapply soundness_ty'; eassumption);
      pose proof (nbe_ty_self HUB HnB) as HnB' end.
    match goal with HB : is_univ_nf ?UB' v |- _ => rewrite (is_univ_nf_eq _ _ HB) in * end.
    assert (HB' : Γ ▹ A ⊢ B : unf_tm v)
      by (rewrite <- nf_to_exp_univ_nf; eapply wf_conv; [ exact HBU | gen_presups; eassumption | eassumption ]).
    assert (Hv : unf_ws (Γ ▹ A) v)
      by (eapply unf_ws_of_nbe; [ rewrite <- nf_to_exp_univ_nf; gen_presups; eassumption
                                | rewrite <- nf_to_exp_univ_nf; exact HnB' ]).
    match goal with HA : Γ ⊢ A : unf_tm u |- _ => pose proof (wf_pi_unf_pi HA HB' Hv) as HPi end.
    assert (exists k, Γ ⊢ unf_pi_tm u v : Typeω@k) as [k Hk] by (gen_presups; eauto 2).
    assert (Γ ⊢ unf_pi_tm u v ≈ W : Typeω@k) by (eapply soundness_ty'; eassumption).
    eapply wf_exp_subtyp'; [ exact HPi | eapply wf_subtyp_refl'; eassumption ].
  (** [λ]: the annotation is a type, so the function is of the [Π] of its
      normal form and the body's type. *)
  - lift_univ_at Γ A u.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ⊢ A ≈ C : Typeω@(unf_large u)) by mauto 2 using soundness_ty'.
    assert (Γ ▹ A ⊢ M : B) by mauto 2.
    assert (exists j, Γ ▹ A ⊢ B : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ Π A B ≈ Π C B : Typeω@(max (unf_large u) j)) as <- by mauto 3.
    mauto 3.
  - assert (Γ ⊢ M : Π A B) by mauto 2.
    assert (exists i, Γ ⊢ Π A B : Typeω@i) as [i] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Typeω@i /\ Γ ▹ (A : exp) ⊢ B : Typeω@i) as [] by mauto 3.
    assert (Γ ⊢ N : A) by mauto 2.
    assert (Γ ⊢ B[Id,,N] ≈ C : Typeω@i) as <- by mauto 4 using soundness_ty'.
    mauto 3.
  - lift_univ_at Γ A u.
    assert (Γ ⊢ M : A) by mauto 2.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢ B : C) by mauto 2.
    assert (exists j, Γ ▸ A ≔ M ⊢ C : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ C[Id,,M] : Typeω@j) by mauto 3.
    assert (Γ ⊢ C[Id,,M] ≈ D : Typeω@j) as <- by mauto 3 using soundness_ty'.
    mauto 3.
  - assert (Γ ⊢ #x : A) by mauto 2.
    assert (exists i, Γ ⊢ A : Typeω@i) as [i] by mauto 2.
    assert (Γ ⊢ A ≈ B : Typeω@i) as <- by mauto 2 using soundness_ty'.
    mauto 3.
  (** A definition of a body. *)
  - match goal with
    | IH : alg_body_sound _ _ _, Hu : is_univ_nf ?UA ?u |- _ =>
        rewrite (is_univ_nf_eq _ _ Hu) in *;
        match goal with
        | HA : ⊢ _ -> _ ⊢ ?A : _, HM : ⊢ _ -> forall i, _ ⊢ ?A : _ -> _ ⊢ ?M : ?A |- _ =>
            let HA' := fresh "HA'" in
            assert (HA' : ⊢ body_ctx Φx ++ Γ -> body_ctx Φx ++ Γ ⊢ A : Typeω@(unf_large u))
              by (intros HC; apply wf_exp_unf_large; rewrite <- nf_to_exp_univ_nf; exact (HA HC));
            eapply (abody_def_sound _ _ _ _ _ _ _ _ (unf_large u)); [ exact IH | exact HA' | intros HC; exact (HM HC _ (HA' HC)) ]
        end
    end.
Qed.

Lemma alg_type_check_sound : forall {Γ i A M},
    Γ ⊢a M ⟸ A ->
    ⊢ Γ ->
    Γ ⊢ A : Typeω@i ->
    Γ ⊢ M : A.
Proof.
  intros; eapply (proj1 alg_type_sound); eassumption.
Qed.

Lemma alg_type_infer_sound : forall {Γ A M},
    Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A.
Proof.
  intros; eapply (proj1 (proj2 alg_type_sound)); eassumption.
Qed.

Lemma alg_ext_sound : forall {Γ Ψ}, Γ ⊢aˣ Ψ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ.
Proof. intros; eapply (proj1 (proj2 (proj2 alg_type_sound))); eassumption. Qed.

Lemma alg_unit_sound : forall {Γ U}, Γ ⊢aᵘ U -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U.
Proof. intros; eapply (proj1 (proj2 (proj2 (proj2 alg_type_sound)))); eassumption. Qed.

Lemma alg_modexp_sound : forall {Γ H}, Γ ⊢aᵐ H -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H.
Proof. intros; eapply (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_sound))))); eassumption. Qed.

(** A checked body is read in a well-formed context, past its expansion. *)
Lemma alg_body_ctx : forall {Γ Φ Φx}, ⊢ Γ -> Γ ⊢aᵇ Φ ⇝ Φx -> ⊢ body_ctx Φx ++ Γ.
Proof.
  intros * HΓ HB.
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 alg_type_sound)))) _ _ _ HB Γ nil eq_refl HΓ
              ltac:(apply wf_ext_eq_nil; exact HΓ)) as [_ HX _].
  pose proof (ext_eq_ctx_left _ _ _ _ _ HX) as HC; rewrite List.app_nil_r in HC; exact HC.
Qed.

(** A body checks to one expansion. *)
Lemma alg_body_functional : forall {Γ Φ Φx Φx'}, ⊢ᵍ gc_deps ⍮ gc_stack ->
    Γ ⊢aᵇ Φ ⇝ Φx -> Γ ⊢aᵇ Φ ⇝ Φx' -> Φx = Φx'.
Proof.
  intros * Hg Hb1; revert Φx'; induction Hb1; intros Φx' Hb2; inversion Hb2; subst;
    try match goal with IH : forall Φx', _ ⊢aᵇ ?Φ ⇝ Φx' -> _ = Φx', Hb : _ ⊢aᵇ ?Φ ⇝ ?Y |- _ =>
      pose proof (IH _ Hb); subst Y end; try reflexivity.
  f_equal; eapply (proj2 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg))))); eassumption.
Qed.

(** The parts of a [Π] the algorithm infers: the domain at its universe, the
    codomain at the normal form of its universe, whose level's atoms are of
    the sorts they carry. *)
Lemma alg_pi_parts_sound : forall {Γ A B UA UB UB' u v},
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_univ_nf UA u ->
    Γ ▹ A ⊢a B ⟹ UB ->
    nbe_ty_f (Γ ▹ A) UB UB' ->
    is_univ_nf UB' v ->
    Γ ⊢ A : unf_tm u /\ Γ ▹ A ⊢ B : unf_tm v /\ unf_ws (Γ ▹ A) v.
Proof.
  intros * HΓ HAi Hu HBi HnB Hv.
  assert (HA : Γ ⊢ A : unf_tm u)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu); eapply alg_type_infer_sound; eassumption).
  assert (⊢ Γ ▹ A) by (eapply wf_ctx_extend, wf_exp_unf_large; exact HA).
  assert (HBU : Γ ▹ A ⊢ B : UB) by (eapply alg_type_infer_sound; eassumption).
  assert (exists k, Γ ▹ A ⊢ (UB : exp) : Typeω@k) as [kB HUB] by (gen_presups; eauto 2).
  assert (Γ ▹ A ⊢ (UB : exp) ≈ UB' : Typeω@kB) by (eapply soundness_ty'; eassumption).
  pose proof (nbe_ty_self HUB HnB) as HnB'.
  rewrite (is_univ_nf_eq _ _ Hv) in *.
  split; [ exact HA | split ].
  - rewrite <- nf_to_exp_univ_nf; eapply wf_conv; [ exact HBU | gen_presups; eassumption | eassumption ].
  - eapply unf_ws_of_nbe; [ rewrite <- nf_to_exp_univ_nf; gen_presups; eassumption
                          | rewrite <- nf_to_exp_univ_nf; exact HnB' ].
Qed.

(** The same after soundness, where the typing comes from the derivation
    rather than from an induction hypothesis. *)
#[local] Tactic Notation "lift_univ_sound" constr(Δ) constr(A) constr(u) :=
  repeat match goal with Hi : is_univ_nf ?UA u |- _ =>
    assert_fails (constr_eq UA (univ_nf u));
    rewrite (is_univ_nf_eq _ _ Hi) in * end;
  assert (Δ ⊢ A : unf_tm u)
    by (rewrite <- nf_to_exp_univ_nf; mauto 3 using alg_type_infer_sound);
  assert (Δ ⊢ A : a_typ (unf_large u))
    by (apply wf_exp_unf_large; eassumption).



Lemma alg_type_infer_normal : forall {Γ A A' M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    nbe_ty_f Γ A A' ->
    A = A'.
Proof.
  intros * ? Hinfer Hnbe. gen A'.
  assert (Γ ⊢ M : A) by mauto 3 using alg_type_infer_sound.
  induction Hinfer; intros;
    try (symmetry; eapply nbe_ty_suniv_lit; eassumption);
    try (dir_inversion_clear_by_head nbe_ty;
         dir_inversion_by_head eval_exp; subst;
         dir_inversion_by_head read_typ; subst;
         reflexivity).
  (** A small universe infers the normal form of [Type⟨succl M⟩], which
      normalises to itself. *)
  - match goal with HMi : Γ ⊢a M ⟹ Levelⁿ@?k |- _ =>
      assert (HMl : Γ ⊢ M : Level@k) by (exact (alg_type_infer_sound HMi ltac:(assumption))) end.
    assert (Γ ⊢ Type⟨succl M⟩ : Typeω@0)
      by (eapply wf_univ_large_tm; [ assumption | eapply wf_succl; exact HMl ]).
    eapply idempotent_nbe_ty; eassumption.
  - assert (Γ ⊢ ⊥ : Typeω@0) by mauto 3.
    assert (Γ ⊢ M : ⊥) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▹ ⊥) by mauto 3.
    lift_univ_sound (Γ ▹ ⊥) A u.
    f_equiv; mautosolve 4.
  (** The forms of inductive types: the normal forms of types. *)
  - destruct (decl_of_lookup _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)) as [HD Hc].
    destruct (ind_ty_typed _ _ _ _ _ _ HD Hc ltac:(eassumption) ltac:(eassumption)) as [j Hj].
    eapply idempotent_nbe_ty; eassumption.
  - match goal with HΓ : ⊢ Γ |- _ =>
      destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ) (decls_of_ctx _ _ _ HΓ)
                  ltac:(eassumption) ltac:(eassumption) ltac:(eassumption) HΓ) as [j Hj] end.
    eapply idempotent_nbe_ty; eassumption.
  - match goal with HΓ : ⊢ Γ, HMi : Γ ⊢a ?N ⟹ nf_indty _ _ _, Hg : elim_grp ?D ?oq ?p ?m,
                    HnT : nbe_ty_f Γ (eb_motive ?bm)[sb_of_list Id (?Ns ++ ?N :: nil)] _ |- _ =>
      assert (exists j, Γ ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ N :: nil)] : Typeω@j) as [j Hj]
        by (eapply proj2; eapply (alg_elim_sound Γ N _ _ _ p D oq m);
            first [ exact HΓ | exact (alg_type_infer_sound HMi HΓ) | eassumption
                  | intros; eapply alg_type_check_sound; eauto ]) end.
    eapply idempotent_nbe_ty; eassumption.
  (** [Π]: the universe it infers is a normal form, which normalises to
      itself. *)
  - match goal with
    | HG : ⊢ Γ, HAi : Γ ⊢a A ⟹ ?UA, Hu : is_univ_nf ?UA u, HBi : Γ ▹ A ⊢a B ⟹ ?UB,
      HnB : nbe_ty_f (Γ ▹ A) (nf_to_exp ?UB) ?UB', Hv : is_univ_nf ?UB' v |- _ =>
        destruct (alg_pi_parts_sound HG HAi Hu HBi HnB Hv) as (HA' & HB' & Hvw)
    end.
    destruct (wf_unf_pi_tm HA' HB' Hvw) as [k Hk].
    eapply idempotent_nbe_ty; eassumption.
  - lift_univ_sound Γ A u.
    assert (Γ ⊢ A ≈ C : Typeω@(unf_large u)) by mauto 3 using soundness_ty'.
    assert (Γ ▹ A ⊢ M : B) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ A ⊢ B : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (⊨ Γ ▹ (C : exp) ≈ Γ ▹ A) by mauto 3.
    dir_inversion_clear_by_head nbe_ty.
    simplify_evals.
    dir_inversion_by_head read_typ; subst.
    functional_initial_env_rewrite_clear.
    assert (initial_env_f (Γ ▹ (C : exp)) (ρ ↦ ⇑! a (length Γ))) by mauto 3.
    assert (nbe_ty_f Γ A C) by mauto 3.
    assert (nbe_ty_f Γ C A0) by mauto 3.
    replace A0 with C by mauto 3.
    assert (nbe_ty_f (Γ ▹ (C : exp)) B B') by mauto 3.
    assert (nbe_ty_f (Γ ▹ A) B B') by mauto 4 using ctxeq_nbe_ty_eq'; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ M : Πⁿ A B) by mauto 3 using alg_type_infer_sound.
    assert (exists i, Γ ⊢ Π A B : Typeω@i) as [i] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Typeω@i /\ Γ ▹ (A : exp) ⊢ B : Typeω@i) as [] by mauto 3.
    assert (Γ ⊢ N : A) by mauto 3 using alg_type_check_sound.
    assert (Γ ⊢ B[Id,,N] : Typeω@i) by mauto 3; (f_equiv; mautosolve 4).
  (** [let], without an annotation and with one. *)
  - destruct_let_ann; simpl_let_guards.
    + rename W into A.
      assert (Γ ⊢ M : A) by mauto 3 using alg_type_infer_sound.
      assert (exists i, Γ ⊢ (A : exp) : Typeω@i) as [i] by (gen_presups; eauto 2).
      assert (⊢ Γ ▸ (A : exp) ≔ M) by mauto 2.
      assert (Γ ▸ (A : exp) ≔ M ⊢ B : C) by mauto 3 using alg_type_infer_sound.
      assert (exists j, Γ ▸ (A : exp) ≔ M ⊢ C : Typeω@j) as [j] by (gen_presups; eauto 2).
      assert (Γ ⊢ C[Id,,M] : Typeω@j) by mauto 3; (f_equiv; mautosolve 4).
    + lift_univ_sound Γ A u.
      assert (Γ ⊢ M : A) by mauto 3 using alg_type_check_sound.
      assert (⊢ Γ ▸ A ≔ M) by mauto 2.
      assert (Γ ▸ A ≔ M ⊢ B : C) by mauto 3 using alg_type_infer_sound.
      assert (exists j, Γ ▸ A ≔ M ⊢ C : Typeω@j) as [j] by (gen_presups; eauto 2).
      assert (Γ ⊢ C[Id,,M] : Typeω@j) by mauto 3; (f_equiv; mautosolve 4).
  - assert (HU : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
    assert (Γ ▹ₘ U ⊢ B : C) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ₘ U ⊢ C : Typeω@j) as [j HCj] by (gen_presups; eauto 2).
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCj (wf_sub_single_mod _ _ _ _ HU)); (f_equiv; mautosolve 4).
  (** A member infers the normal form of the type its module's description
      reads, a type ([member_wf]). *)
  - match goal with Hm : mdenote _ _ _ (me_mem _ _) _, Ht : ds_ty _ _ _ = Some _ |- _ =>
      destruct (member_wf _ _ _ _ _ ltac:(eapply alg_modexp_sound; eassumption) Hm Ht) as ([i HA] & _) end.
    (f_equiv; mautosolve 4).
  - assert (exists i, Γ ⊢ A : Typeω@i) as [i] by mauto 2; (f_equiv; mautosolve 4).
  (** A record's type former, a tuple and a projection: the normal forms of
      types. *)
  - destruct (record_former_typed _ _ _ ltac:(eassumption) ltac:(eassumption)) as [j [_ Hj]].
    eapply idempotent_nbe_ty; eassumption.
  - lift_univ_sound Γ T u.
    eapply idempotent_nbe_ty; eassumption.
  - match goal with HΓ : ⊢ Γ, HMi : Γ ⊢a ?N ⟹ nf_record _ _ |- _ =>
      destruct (alg_proj_typed _ _ _ _ _ _ _ _ HΓ (alg_type_infer_sound HMi HΓ) ltac:(eassumption) ltac:(eassumption))
        as (m & HUt & _) end.
    eapply idempotent_nbe_ty; eassumption.
Qed.

Hint Resolve alg_type_infer_normal : mctt.

(** An inferred type is its own normal form. *)
Lemma alg_type_infer_self : forall {Γ A M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    nbe_ty_f Γ A A.
Proof.
  intros * HΓ Hi.
  assert (Γ ⊢ M : A) by (eapply alg_type_infer_sound; eassumption).
  assert (exists k, Γ ⊢ (A : exp) : Typeω@k) as [k Hk] by (gen_presups; eauto 2).
  destruct (soundness_ty Hk) as (C & HC & _).
  assert (A = C) as <- by (eapply alg_type_infer_normal; eassumption).
  exact HC.
Qed.

(** A type checked against a large universe infers a universe at an index
    below it: with the small tier that index need not be a large one. *)
Lemma alg_type_check_typ_implies_alg_type_infer_typ : forall {Γ A i},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Typeω@i ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i).
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [ contradiction | |].
  - exists Typeωⁿ@i0, (unl i0); split; [ exact Hinfer | split; [ constructor | cbn; assumption ] ].
  - exists (univⁿ c xs), (uns (c, xs)); split; [ exact Hinfer | split; [ constructor | exact I ] ].
Qed.

Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.

Lemma alg_type_check_pi_implies_alg_type_infer_pi : forall {Γ M A B i},
    ⊢ Γ ->
    Γ ⊢ Π A B : Typeω@i ->
    Γ ⊢a M ⟸ Π A B ->
    exists A' B', Γ ⊢a M ⟹ Πⁿ A' B' /\ Γ ⊢ A' ≈ A : Typeω@i /\ Γ ▹ A ⊢a B' ⊆ B.
Proof.
  intros * ? ? Hcheck.
  assert (Γ ⊢ A : Typeω@i /\ Γ ▹ A ⊢ B : Typeω@i) as [] by mauto 3.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' C Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  inversion Hnbe1; subst.
  functional_initial_env_rewrite_clear.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  simpl in *.
  assert (Γ ⊢ M : Πⁿ A0 B0) by mauto 3 using alg_type_infer_sound.
  assert (exists j, Γ ⊢ Π A0 B0 : Typeω@j) as [j] by (gen_presups; eauto 2).
  assert (Γ ⊢ A0 : Typeω@j /\ Γ ▹ (A0 : exp) ⊢ B0 : Typeω@j) as [] by mauto 3.
  do 2 eexists.
  assert (nbe_ty_f Γ A A0) by mauto 3.
  assert (Γ ⊢ A ≈ A0 : Typeω@i) by mauto 3 using soundness_ty'.
  repeat split; mauto 3.
  assert (initial_env_f (Γ ▹ A) (ρ ↦ ⇑! a (length Γ))) by mauto 3.
  assert (nbe_ty_f (Γ ▹ A) B B') by mauto 3.
  assert (initial_env_f (Γ ▹ (A0 : exp)) (ρ ↦ ⇑! a0 (length Γ))) by mauto 3.
  assert (nbe_ty_f (Γ ▹ (A0 : exp)) B0 B0) by mauto 3.
  assert (⊨ Γ ▹ (A0 : exp) ≈ Γ ▹ A) by mauto 3.
  assert (nbe_ty_f (Γ ▹ A) B0 B0) by mauto 4 using ctxeq_nbe_ty_eq'.
  mauto 3.
Qed.

Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mctt.

Lemma alg_type_check_subtyp : forall {Γ A A' M},
    Γ ⊢a M ⟸ A ->
    Γ ⊢ A ⊆ A' ->
    Γ ⊢a M ⟸ A'.
Proof.
  intros * [] **.
  assert (Γ0 ⊢a B ⊆ A') by mauto 3 using alg_subtyping_complete.
  mauto 3 using alg_subtyping_trans.
Qed.

Hint Resolve alg_type_check_subtyp : mctt.

Corollary alg_type_check_conv : forall {Γ i A A' M},
    Γ ⊢a M ⟸ A ->
    Γ ⊢ A ≈ A' : Typeω@i ->
    Γ ⊢a M ⟸ A'.
Proof.
  mauto 3.
Qed.

Hint Resolve alg_type_check_conv : mctt.

(** ** Unannotated Definitions

    The number of unannotated [let]s in a term, the measure of the outer
    induction of completeness: the body of an unannotated [let] is checked in
    a context refined to the type its definiens infers, by a derivation which
    is not a subderivation, but whose subject has fewer of them.  The
    eliminators and the module expressions a term, a unit or a body reads are
    counted too: the motive and the branches of an eliminator are typed at the
    parameters the scrutinee infers, and a module expression is well-formed
    by a derivation that may go through its δ- and β-reducts, so its parts are
    reached by generation ([modexp_gen]), not as subderivations. *)
Fixpoint exp_lets (M : exp) : nat :=
  match M with
  | a_succl M | a_univ M => exp_lets M
  | a_maxl M N => exp_lets M + exp_lets N
  | a_exfalso A M => exp_lets A + exp_lets M
  | a_elim _ Us _ Bks M =>
      S ((fix us_lets (Us : list exp) : nat :=
            match Us with
            | nil => 0
            | U :: Us' => exp_lets U + us_lets Us'
            end) Us +
         (fix blocks_lets (Bks : list eblock) : nat :=
            match Bks with
            | nil => 0
            | eb_mk _ oZ A Bs :: Bks' =>
                match oZ with Some Z => exp_lets Z | None => 0 end + exp_lets A +
                (fix brs_lets (Bs : list (String.string * nat * exp)) : nat :=
                   match Bs with
                   | nil => 0
                   | b :: Bs' => exp_lets (snd b) + brs_lets Bs'
                   end) Bs + blocks_lets Bks'
            end) Bks + exp_lets M)
  | a_pi A B => exp_lets A + exp_lets B
  | a_fn A M => exp_lets A + exp_lets M
  | a_app M N => exp_lets M + exp_lets N
  | a_let b B => bnd_lets b + exp_lets B
  | a_mem H _ => S (modexp_lets H)
  | a_tuple T fs =>
      exp_lets T +
      (fix fields_lets (fs : list (String.string * exp)) : nat :=
         match fs with
         | nil => 0
         | f :: fs' => exp_lets (snd f) + fields_lets fs'
         end) fs
  | a_proj _ M => exp_lets M
  | _ => 0
  end
with modexp_lets (H : modexp) : nat :=
  match H with
  | me_mem H _ => modexp_lets H
  | me_app H N => modexp_lets H + exp_lets N
  | me_lit U => gunit_lets U
  | _ => 0
  end
with bnd_lets (b : bnd) : nat :=
  match b with
  | b_def (Some A) M => exp_lets A + exp_lets M
  | b_def None M => S (exp_lets M)
  | b_mod U => gunit_lets U
  end
with gunit_lets (U : gunit) : nat :=
  match U with
  | gu_mk Δ D =>
      (fix tele_lets (Δ : list centry) : nat :=
         match Δ with
         | nil => 0
         | e :: Δ' => centry_lets e + tele_lets Δ'
         end) Δ + moddef_lets D
  end
with moddef_lets (D : moddef) : nat :=
  match D with
  | md_body sm Φ => gmod_lets Φ
  | md_alias E => S (modexp_lets E)
  end
with gmod_lets (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ _ E => gmod_lets Φ + gentry_lets E
  | gm_open Φ H _ => gmod_lets Φ + S (modexp_lets H)
  end
with gentry_lets (E : gentry) : nat :=
  match E with
  | ge_def _ _ A B => exp_lets A + match B with Some M => exp_lets M | None => 0 end
  | ge_mod _ U => gunit_lets U
  | ge_ind _ _ _ _ Φ => gmod_lets Φ
  | ge_def_mod _ _ _ _ => 0
  | ge_record _ _ _ Φ => gmod_lets Φ
  end
with centry_lets (e : centry) : nat :=
  match e with
  | ce_ass A => exp_lets A
  | ce_def A M => exp_lets A + exp_lets M
  | ce_mod U => gunit_lets U
  end.

Fixpoint ctx_lets (Γ : ctx) : nat :=
  match Γ with
  | nil => 0
  | e :: Γ' => centry_lets e + ctx_lets Γ'
  end.

Lemma gunit_lets_mk : forall Δ D, gunit_lets (gu_mk Δ D) = ctx_lets Δ + moddef_lets D.
Proof. intros; cbn; f_equal; induction Δ; cbn; congruence. Qed.

Lemma ctx_lets_app : forall Ψ Γ, ctx_lets (Ψ ++ Γ) = ctx_lets Ψ + ctx_lets Γ.
Proof. induction Ψ; intros; cbn; [| rewrite IHΨ ]; lia. Qed.

Lemma body_ctx_lets : forall Φ, ctx_lets (body_ctx Φ) <= gmod_lets Φ.
Proof.
  induction Φ as [| Φ IH x [b pv A [M |] | pm U | ? ? ? | ? ? ? ? | ? ? ?] | Φ IH c its ]; cbn; rewrite ?ctx_lets_app; [ lia .. |].
  enough (ctx_lets (List.repeat (ce_ass a_True) (List.length its)) = 0) by lia.
  induction (List.length its); cbn; auto.
Qed.

Lemma exp_lets_apps : forall M args,
    exp_lets (apps M args) = exp_lets M + List.fold_right (fun N n => exp_lets N + n) 0 args.
Proof. intros M args; revert M; induction args; intros; cbn; [ lia | rewrite IHargs; cbn; lia ]. Qed.

Ltac lets_bound :=
  repeat first
    [ progress rewrite ?gunit_lets_mk, ?ctx_lets_app in *
    | progress cbn [exp_lets modexp_lets bnd_lets moddef_lets gmod_lets
                    gentry_lets centry_lets ctx_lets] in * ];
  repeat match goal with
         | Φ : gmod |- _ =>
             lazymatch goal with
             | _ : ctx_lets (body_ctx Φ) <= gmod_lets Φ |- _ => fail
             | _ => pose proof (body_ctx_lets Φ)
             end
         end;
  lia.

(** A term that infers a universe checks against every universe above it: the
    algorithmic counterpart of the universe subtyping rules, against a large
    universe and against a small one at a literal level. *)
Lemma alg_type_check_typ_of : forall Γ A UA (u : unf) i,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_univ_nf UA u ->
    unf_le u (unl i) ->
    Γ ⊢a A ⟸ Typeω@i.
Proof.
  intros * HΓ Hi Hu Hle.
  assert (HA : Γ ⊢ A : UA) by (eapply alg_type_infer_sound; eassumption).
  econstructor; [ exact Hi |].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf in *.
  apply alg_subtyping_complete.
  destruct u as [L | j]; cbn [unf_tm unf_le] in *.
  - assert (exists k, Γ ⊢ Type⟨lvl_exp_of (fst L) (List.map atom_exp (snd L))⟩ : Typeω@k) as [k Hk]
      by (gen_presups; eauto 2).
    destruct (wf_univ_lvl_inversion Hk) as [n Hn].
    eapply wf_subtyp_small_large; eassumption.
  - apply wf_subtyp_ge; [ assumption | lia ].
Qed.

Lemma alg_type_check_suniv : forall Γ A UA (u : unf) m,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    is_univ_nf UA u ->
    unf_le u (unf_lit m) ->
    Γ ⊢a A ⟸ Type⟨𝕃ᵒ m⟩.
Proof.
  intros * HΓ Hi Hu Hle.
  destruct u as [[c xs] | j]; cbn [unf_le unf_lit] in Hle; [| contradiction ].
  (** The inferred universe is a normal form, so its level's atoms are of the
      sorts they carry, below the literal's tier ([lvl_le_lit_sorts]). *)
  assert (HA : Γ ⊢ A : UA) by (eapply alg_type_infer_sound; eassumption).
  pose proof (alg_type_infer_self HΓ Hi) as HnA.
  rewrite (is_univ_nf_eq _ _ Hu) in HA, HnA; cbn [univ_nf nf_univ_of fst snd nf_to_exp] in HA, HnA.
  assert (exists k, Γ ⊢ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ : Typeω@k) as [k Hk] by (gen_presups; eauto 2).
  destruct (univ_nf_ws Hk HnA) as (nA & HLA & Hc & Hxs).
  set (N := Nat.max nA (fst m)).
  econstructor; [ exact Hi |].
  rewrite (is_univ_nf_eq _ _ Hu), nf_to_exp_univ_nf.
  apply alg_subtyping_complete.
  cbn [unf_tm fst snd].
  eapply (wf_subtyp_suniv _ _ _ N);
    [ exact HΓ | eapply wf_exp_level_up; [| exact HLA ]; subst N; lia
    | apply wf_llit; [ subst N; lia | exact HΓ ] |].
  assert (HcN : fst c <= N) by (subst N; lia).
  assert (HmN : fst m <= N) by (subst N; lia).
  assert (HxsN : @la_ws gc_deps gc_stack N Γ xs) by (eapply la_ws_mono; [| exact Hxs ]; subst N; lia).
  exact (lvl_exp_of_le (n := N) c xs m nil HcN HmN HΓ HxsN I Hle).
Qed.

(** A type checked against a small universe infers a small universe, at a canonical
    level below the one [Type⟨t⟩] normalizes to. *)
Lemma alg_type_check_suniv_tm_implies_alg_type_infer_univ : forall {Γ A t},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Type⟨t⟩ ->
    exists L L', Γ ⊢a A ⟹ nf_univ_of L /\ nbe_ty_f Γ Type⟨t⟩ (nf_univ_of L') /\ lvl_le L L'.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' B' Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  pose proof Hnbe2 as Hn.
  inversion Hn; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  destruct L as [d ys]; unfold nf_univ_of in *; cbn [fst snd] in *.
  inversion Hnfsub; subst; [ contradiction |].
  exists (c, xs), (d, ys); split; [ exact Hinfer | split; [ exact Hnbe2 | assumption ] ].
Qed.

(** A term checked against a type of levels infers a type of levels of a
    smaller sort: the only normal forms below [Levelⁿ@n] are the [Levelⁿ@m]
    with [m <= n]. *)
Lemma alg_type_check_level_infer : forall {Γ M n},
    ⊢ Γ ->
    Γ ⊢a M ⟸ Level@n ->
    exists m, Γ ⊢a M ⟹ Levelⁿ@m /\ m <= n.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [ contradiction |].
  eexists; split; [ exact Hinfer | assumption ].
Qed.

(** Conversely, a term that infers a type of levels checks against every
    type of levels of a larger sort. *)
Lemma alg_type_check_level_of : forall {Γ M m n},
    ⊢ Γ ->
    Γ ⊢a M ⟹ Levelⁿ@m ->
    m <= n ->
    Γ ⊢a M ⟸ Level@n.
Proof.
  intros * HΓ Hi Hmn.
  econstructor; [ exact Hi |].
  apply alg_subtyping_complete; cbn [nf_to_exp].
  apply wf_subtyp_level; assumption.
Qed.

(** ** Completeness of the [Π] Rule

    A [Π] whose parts infer universes checks against every type its
    universe ([unf_pi_tm]) is below. *)
Lemma alg_pi_check_of_infer : forall Γ A B UA UB (u v : unf) T k,
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    Γ ▹ A ⊢a B ⟹ UB ->
    is_univ_nf UA u ->
    is_univ_nf UB v ->
    Γ ⊢ T : Typeω@k ->
    Γ ⊢ unf_pi_tm u v ⊆ T ->
    Γ ⊢a Π A B ⟸ T.
Proof.
  intros * HΓ HAi HBi Hu Hv HT Hsub.
  assert (HA : Γ ⊢ A : unf_tm u)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu); eapply alg_type_infer_sound; eassumption).
  assert (⊢ Γ ▹ A) by (eapply wf_ctx_extend, wf_exp_unf_large; exact HA).
  assert (HB : Γ ▹ A ⊢ B : unf_tm v)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hv); eapply alg_type_infer_sound; eassumption).
  assert (HnB : nbe_ty_f (Γ ▹ A) UB UB) by (eapply alg_type_infer_self; eassumption).
  assert (exists k, Γ ▹ A ⊢ unf_tm v : Typeω@k) as [kv Hkv] by (gen_presups; eauto 2).
  assert (Hvws : unf_ws (Γ ▹ A) v)
    by (rewrite (is_univ_nf_eq _ _ Hv) in HnB; eapply unf_ws_of_nbe;
        [ exact Hkv | rewrite <- nf_to_exp_univ_nf; exact HnB ]).
  destruct (wf_unf_pi_tm HA HB Hvws) as [j Hj].
  destruct (soundness_ty Hj) as [W [HW HeqW]].
  econstructor; [ eapply ati_pi; [ eassumption | eassumption | eassumption | exact HnB | exact Hv | eassumption ] |].
  apply alg_subtyping_complete.
  etransitivity; [| exact Hsub ].
  eapply wf_subtyp_refl'; symmetry; exact HeqW.
Qed.

(** The universe a [Π] infers is a universe normal form: [unf_pi_tm] is a
    universe term, which reads back as one. *)
Lemma nbe_ty_unf_pi_tm_univ : forall Γ (u v : unf) W,
    nbe_ty_f Γ (unf_pi_tm u v) W ->
    exists w, is_univ_nf W w.
Proof.
  intros * Hn.
  destruct u as [[c xs] | i], v as [[d ys] | j]; cbn [unf_pi_tm unf_max unf_tm fst snd] in Hn;
    [ | destruct xs | destruct ys |];
    cbn [unf_tm] in Hn;
    dir_inversion_clear_by_head nbe_ty; dir_inversion_by_head eval_exp; subst;
    dir_inversion_by_head read_typ; subst;
    eexists; first [ constructor | match goal with |- is_univ_nf (nf_univ_of ?L) _ => destruct L; constructor end ].
Qed.

(** A [Π] whose parts infer universes infers one. *)
Lemma alg_pi_infer_univ : forall Γ A B UA UB (u v : unf),
    ⊢ Γ ->
    Γ ⊢a A ⟹ UA ->
    Γ ▹ A ⊢a B ⟹ UB ->
    is_univ_nf UA u ->
    is_univ_nf UB v ->
    exists W w, Γ ⊢a Π A B ⟹ W /\ is_univ_nf W w /\ nbe_ty_f Γ (unf_pi_tm u v) W.
Proof.
  intros * HΓ HAi HBi Hu Hv.
  assert (HA : Γ ⊢ A : unf_tm u)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hu); eapply alg_type_infer_sound; eassumption).
  assert (⊢ Γ ▹ A) by (eapply wf_ctx_extend, wf_exp_unf_large; exact HA).
  assert (HB : Γ ▹ A ⊢ B : unf_tm v)
    by (rewrite <- nf_to_exp_univ_nf, <- (is_univ_nf_eq _ _ Hv); eapply alg_type_infer_sound; eassumption).
  assert (HnB : nbe_ty_f (Γ ▹ A) UB UB) by (eapply alg_type_infer_self; eassumption).
  assert (exists k, Γ ▹ A ⊢ unf_tm v : Typeω@k) as [kv Hkv] by (gen_presups; eauto 2).
  assert (Hvws : unf_ws (Γ ▹ A) v)
    by (rewrite (is_univ_nf_eq _ _ Hv) in HnB; eapply unf_ws_of_nbe;
        [ exact Hkv | rewrite <- nf_to_exp_univ_nf; exact HnB ]).
  destruct (wf_unf_pi_tm HA HB Hvws) as [j Hj].
  destruct (soundness_ty Hj) as [W [HW _]].
  destruct (nbe_ty_unf_pi_tm_univ _ _ _ _ HW) as [w Hw].
  exists W, w; split; [ eapply ati_pi; [ eassumption | eassumption | eassumption | exact HnB | exact Hv | eassumption ] | split; assumption ].
Qed.

(** The universe of a [Π] of two types below a large universe is below it. *)
Lemma unf_pi_tm_large : forall Γ (u v : unf) i k,
    ⊢ Γ ->
    Γ ⊢ unf_pi_tm u v : Typeω@k ->
    unf_le u (unl i) ->
    unf_le v (unl i) ->
    Γ ⊢ unf_pi_tm u v ⊆ Typeω@i.
Proof.
  intros * HΓ Hk Hu Hv.
  destruct u as [[c xs] | i1], v as [[d ys] | j1]; cbn [unf_pi_tm unf_le fst snd] in *.
  - destruct (wf_univ_lvl_inversion Hk) as [? ?]; eapply wf_subtyp_small_large; eassumption.
  - destruct xs; cbn [unf_max unf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia | exact HΓ | lia ].
  - destruct ys; cbn [unf_max unf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia | exact HΓ | lia ].
  - cbn [unf_max unf_tm]; apply wf_subtyp_ge; [ exact HΓ | lia ].
Qed.

(** The small [Π] at a level term.  The codomain's universe is below the
    normal form of the weakened level, which is fresh ([nbe_ty_wk_fresh]), so
    the bound of the codomain's level under the binder is below it too
    ([lvl_le_bound_wk]), and the [Π] is at a level below [L]: the domain's is
    below [L] in [Γ], and the codomain's bound below [L[↑]ʷ] in [Γ ▹ A],
    which strengthens.  Every level here is a normal form or an inferred
    universe's level, so its atoms are of the sorts they carry
    ([univ_nf_ws], [soundness_lvl_ws]). *)
Lemma alg_pi_small_complete : forall Γ L A B n,
    Γ ⊢ L : Level@n ->
    Γ ⊢ A : Type⟨L⟩ ->
    Γ ▹ A ⊢ B : Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a A ⟸ Type⟨L⟩ ->
    Γ ▹ A ⊢a B ⟸ Type⟨L[↑]ʷ⟩ ->
    Γ ⊢a Π A B ⟸ Type⟨L⟩.
Proof.
  intros * HL0 HA HB HAc HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  assert (HΓA : ⊢ Γ ▹ A) by (gen_presups; assumption).
  destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HΓ HAc) as (LA & Lt & HAi & HnL & HLA).
  destruct (alg_type_check_suniv_tm_implies_alg_type_infer_univ HΓA HBc) as (LB & L' & HBi & HnL' & HLB).
  assert (HfL' : all_list (fun a => ne_fresh 0 (atom_level a)) (snd L'))
    by exact (nbe_ty_wk_fresh _ _ Γ A Type⟨L⟩ _ HnL').
  pose proof (lvl_le_bound_wk 0 _ _ HLB HfL') as HbLB.
  destruct LA as [c xs], LB as [d ys], Lt as [e zs], L' as [f ws]; cbn [fst snd] in *.
  eapply (alg_pi_check_of_infer _ _ _ _ _ (uns (c, xs)) (uns (d, ys)) _ 0);
    [ exact HΓ | exact HAi | exact HBi | constructor | constructor | eapply wf_univ_large_tm; eassumption |].
  cbn [unf_pi_tm fst snd]; unfold lvl_bound; cbn [fst snd].
  (** The levels and their atoms, each at its own sort. *)
  assert (HAi' : Γ ⊢ A : Type⟨lvl_exp_of c (List.map atom_exp xs)⟩) by (eapply alg_type_infer_sound in HAi; eassumption).
  assert (HBi' : Γ ▹ A ⊢ B : Type⟨lvl_exp_of d (List.map atom_exp ys)⟩) by (eapply alg_type_infer_sound in HBi; eassumption).
  assert (exists k, Γ ⊢ Type⟨lvl_exp_of c (List.map atom_exp xs)⟩ : Typeω@k) as [kA HkA] by (gen_presups; eauto 2).
  assert (exists k, Γ ▹ A ⊢ Type⟨lvl_exp_of d (List.map atom_exp ys)⟩ : Typeω@k) as [kB HkB] by (gen_presups; eauto 2).
  destruct (univ_nf_ws HkA (alg_type_infer_self HΓ HAi)) as (nA & HLAe0 & Hc & Hxs).
  destruct (univ_nf_ws HkB (alg_type_infer_self HΓA HBi)) as (nB & HLBe0 & Hd & Hys).
  assert (HL1 : Γ ▹ A ⊢ L[↑]ʷ : Level@n) by (eapply (wk_preserves_exp _ _ _ _ Level@n); [ exact HL0 | mauto 2 ]).
  pose proof (soundness_lvl_ws HL0 (nbe_ty_univ_level (L := (e, zs)) (n := n) HnL)) as [He Hzs].
  pose proof (soundness_lvl_ws HL1 (nbe_ty_univ_level (L := (f, ws)) (n := n) HnL')) as [Hf Hws].
  cbn [fst snd] in He, Hzs, Hf, Hws.
  assert (HTt : Γ ⊢ Type⟨L⟩ ≈ (nf_univ_of (e, zs) : exp) : Typeω@0)
    by (eapply soundness_ty'; [ eapply wf_univ_large_tm; eassumption | exact HnL ]).
  assert (HTt' : Γ ▹ A ⊢ Type⟨L[↑]ʷ⟩ ≈ (nf_univ_of (f, ws) : exp) : Typeω@0)
    by (eapply soundness_ty'; [ eapply wf_univ_large_tm; eassumption | exact HnL' ]).
  cbn [nf_to_exp nf_univ_of fst snd] in HTt, HTt'.
  apply exp_eq_suniv_tm_inj in HTt as [nT HTt0], HTt' as [nT' HTt'0].
  (** All of them move to the largest of the sorts, one above the
      codomain's, where the bound of its open atoms lives. *)
  set (cb := omax d (la_open_bound 0 ys)) in *.
  set (fp := la_fresh_part 0 ys) in *.
  set (N := S (Nat.max (Nat.max n (Nat.max nA nB)) (Nat.max nT nT'))).
  assert (Hcb : fst cb <= N)
    by (subst cb N; apply omax_fst_le;
        [ lia | eapply Nat.le_trans; [ apply la_open_bound_fst; eapply la_ws_sorts; exact Hys | lia ] ]).
  assert (HxsN : @la_ws gc_deps gc_stack N Γ xs) by (eapply la_ws_mono; [| exact Hxs ]; subst N; lia).
  assert (HzsN : @la_ws gc_deps gc_stack N Γ zs) by (eapply la_ws_mono; [| exact Hzs ]; subst N; lia).
  assert (HwsN : @la_ws gc_deps gc_stack N (Γ ▹ A) ws) by (eapply la_ws_mono; [| exact Hws ]; subst N; lia).
  assert (HfpN : @la_ws gc_deps gc_stack N (Γ ▹ A) fp)
    by (apply la_ws_fresh_part; eapply la_ws_mono; [| exact Hys ]; subst N; lia).
  assert (HL : Γ ⊢ L : Level@N) by (eapply wf_exp_level_up; [| exact HL0 ]; subst N; lia).
  assert (HLAe : Γ ⊢ lvl_exp_of c (List.map atom_exp xs) : Level@N) by (eapply wf_exp_level_up; [| exact HLAe0 ]; subst N; lia).
  assert (HTt : Γ ⊢ L ≈ lvl_exp_of e (List.map atom_exp zs) : Level@N) by (eapply wf_exp_eq_level_up; [| exact HTt0 ]; subst N; lia).
  assert (HTt' : Γ ▹ A ⊢ L[↑]ʷ ≈ lvl_exp_of f (List.map atom_exp ws) : Level@N)
    by (eapply wf_exp_eq_level_up; [| exact HTt'0 ]; subst N; lia).
  clear HL0 HLAe0 HTt0 HTt'0.
  set (LAe := lvl_exp_of c (List.map atom_exp xs)) in *.
  set (LBs := lvl_exp_of cb (List.map atom_exp (List.map (map_level_atom (ne_unwk 0)) fp))).
  assert (Hfresh : lvl_exp_of cb (List.map atom_exp fp) = LBs[↑]ʷ)
    by exact (nf_fresh_unwk 0 (nf_lvl cb fp) (la_fresh_part_fresh 0 ys)).
  assert (HLBl : Γ ▹ A ⊢ LBs[↑]ʷ : Level@N)
    by (rewrite <- Hfresh; apply lvl_exp_of_wf; [ exact Hcb | exact HΓA | apply la_ws_wf; exact HfpN ]).
  assert (HLBs : Γ ⊢ LBs : Level@N) by exact (level_nf_strengthen Γ A N (nf_lvl cb (List.map (map_level_atom (ne_unwk 0)) fp)) HΓA HLBl).
  eapply wf_subtyp_suniv; [ exact HΓ | apply wf_maxl; eassumption | exact HL |].
  apply lvl_sub_maxl_lub; [ exact HLAe | exact HLBs | exact HL | |].
  - (** The domain's level is below [L]. *)
    unfold lvl_sub.
    assert (HcN : fst c <= N) by (subst N; lia).
    assert (HeN : fst e <= N) by (subst N; lia).
    pose proof (lvl_exp_of_le (n := N) c xs e zs HcN HeN HΓ HxsN HzsN HLA) as Hle.
    transitivity (maxl LAe (lvl_exp_of e (List.map atom_exp zs)));
      [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HTt ] |].
    transitivity (lvl_exp_of e (List.map atom_exp zs)); [ exact Hle | symmetry; exact HTt ].
  - (** The codomain's bound, below [L[↑]ʷ] in [Γ ▹ A], strengthened. *)
    unfold lvl_sub.
    assert (HfN : fst f <= N) by (subst N; lia).
    pose proof (lvl_exp_of_le (n := N) cb fp f ws Hcb HfN HΓA HfpN HwsN HbLB) as Hle.
    rewrite Hfresh in Hle.
    assert (Hlong : Γ ▹ A ⊢ maxl LBs[↑]ʷ L[↑]ʷ ≈ L[↑]ʷ : Level@N).
    { transitivity (maxl LBs[↑]ʷ (lvl_exp_of f (List.map atom_exp ws)));
        [ apply wf_exp_eq_maxl_cong; [ mauto 3 | exact HTt' ] |].
      transitivity (lvl_exp_of f (List.map atom_exp ws)); [ exact Hle | symmetry; exact HTt' ]. }
    exact (exp_eq_strengthen nil Γ A (maxl LBs L) L Level@N ltac:(constructor) HΓA ltac:(mauto 3) HL Hlong).
Qed.

(** Completeness, for terms and for the module judgments at once, since a
    unit's body holds terms and a term may hold a unit.  The global context is
    an index of the judgments, so it is fixed for the induction, as in
    [subtyp_spec]. *)
(** The parts of an eliminator have fewer [let]s than it. *)
Lemma elim_lets_parts : forall oq Us m Bks M,
    (forall U, List.In U Us -> exp_lets U < exp_lets (a_elim oq Us m Bks M)) /\
    (forall b Z, List.In b Bks -> eb_ann b = Some Z -> exp_lets Z < exp_lets (a_elim oq Us m Bks M)) /\
    (forall b, List.In b Bks -> exp_lets (eb_motive b) < exp_lets (a_elim oq Us m Bks M)) /\
    (forall b br, List.In b Bks -> List.In br (eb_brs b) -> exp_lets (snd br) < exp_lets (a_elim oq Us m Bks M)) /\
    exp_lets M < exp_lets (a_elim oq Us m Bks M).
Proof.
  intros; cbn [exp_lets].
  set (ul := (fix us_lets (Us : list exp) : nat :=
                match Us with nil => 0 | U :: Us' => exp_lets U + us_lets Us' end) Us).
  set (brl := fix brs_lets (Bs : list (String.string * nat * exp)) : nat :=
                match Bs with nil => 0 | b :: Bs' => exp_lets (snd b) + brs_lets Bs' end).
  set (bl := (fix blocks_lets (Bks : list eblock) : nat :=
                match Bks with
                | nil => 0
                | eb_mk _ oZ A Bs :: Bks' =>
                    match oZ with Some Z => exp_lets Z | None => 0 end + exp_lets A + brl Bs + blocks_lets Bks'
                end) Bks).
  assert (HU : forall U, List.In U Us -> exp_lets U <= ul).
  { unfold ul; clear; induction Us as [| U' Us IH]; intros U HU; cbn in HU |- *; [ contradiction |].
    destruct HU as [-> | HU]; [ lia | specialize (IH _ HU); lia ]. }
  assert (Hbr : forall Bs br, List.In br Bs -> exp_lets (snd br) <= brl Bs).
  { induction Bs as [| br' Bs IH]; intros br Hin; cbn in Hin |- *; [ contradiction |].
    destruct Hin as [-> | Hin]; [ lia | specialize (IH _ Hin); lia ]. }
  assert (HB : forall b, List.In b Bks ->
             match eb_ann b with Some Z => exp_lets Z | None => 0 end + exp_lets (eb_motive b) + brl (eb_brs b) <= bl).
  { unfold bl; clear -Hbr; induction Bks as [| [nm oZ A Bs] Bks IH]; intros b Hb; cbn in Hb |- *; [ contradiction |].
    destruct Hb as [<- | Hb]; cbn; [ lia | specialize (IH _ Hb); lia ]. }
  split; [ intros U HU'; specialize (HU _ HU'); lia | split; [| split; [| split ] ] ].
  - intros b Z Hb HZ; specialize (HB _ Hb); rewrite HZ in HB; lia.
  - intros b Hb; specialize (HB _ Hb); lia.
  - intros b br Hb Hbr'; specialize (HB _ Hb); specialize (Hbr _ _ Hbr'); lia.
  - lia.
Qed.

(** A monotone property with a witness below each [j < n] has one witness
    for them all. *)
Lemma nat_bound_upto : forall (Q : nat -> nat -> Prop) n,
    (forall j, j < n -> exists l, Q j l) -> (forall j l l', l <= l' -> Q j l -> Q j l') ->
    exists L, forall j, j < n -> Q j L.
Proof.
  intros Q n; induction n as [| n IH]; intros Hex Hmon; [ exists 0; intros; lia |].
  destruct IH as [L HL]; [ intros j Hj; apply Hex; lia | exact Hmon |].
  destruct (Hex n ltac:(lia)) as [l Hl].
  exists (max L l); intros j Hj.
  destruct (Nat.eq_dec j n) as [-> | Hne]; [ eapply Hmon; [| exact Hl ]; lia | eapply Hmon; [| apply HL; lia ]; lia ].
Qed.

(** Normal forms, position by position, give [nfs_agree]. *)
Lemma nfs_agree_of_nth : forall Γ Ms Rs Ts,
    List.length Ms = List.length Ts -> List.length Rs = List.length Ts ->
    (forall j M R T, List.nth_error Ms j = Some M -> List.nth_error Rs j = Some R -> List.nth_error Ts j = Some T ->
       exists W, nbe_f Γ M T W /\ nbe_f Γ R T W) ->
    nfs_agree Γ Ms Rs Ts.
Proof.
  induction Ms as [| M Ms IH]; intros [| R Rs] [| T Ts] HMl HRl H; cbn in HMl, HRl; try discriminate; [ constructor |].
  destruct (H 0 M R T eq_refl eq_refl eq_refl) as (W & HMW & HRW).
  econstructor; [ exact HMW | exact HRW |].
  apply IH; [ lia | lia | intros j M' R' T' HM' HR' HT'; exact (H (S j) M' R' T' HM' HR' HT') ].
Qed.

(** The eliminator, from the derivation's premises at the parameters [Ps]
    and the algorithm's for its parts: the scrutinee infers the type former
    the member's type is headed by, at parameters equal to the
    derivation's ([subtyp_ind_nf]), whose uniform ones the member's
    uniform arguments normalize to, and whose others are the member's
    non-uniform ones ([mty_params_conv], [mty_params_inj]); the annotations
    and the motives are checked at one universe above them all
    ([nat_bound_upto]). *)
Lemma alg_elim_complete : forall Γ p D oq m Mm bm Bks Ps M i,
    ind_lookup gc_deps gc_stack p = Some D -> elim_grp D oq p m -> ind_member D m = Some Mm ->
    List.nth_error Bks m = Some bm ->
    List.length Ps = im_np D Mm ->
    (forall j P T, List.nth_error Ps j = Some P -> List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Γ ⊢ P : T) ->
    Γ ⊢ M : ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    Γ ⊢a M ⟸ ind_mty p D m (List.firstn (ind_nu D) Ps) (List.skipn (ind_nu D) Ps) ->
    blocks_typed gc_deps gc_stack Γ p D (List.firstn (ind_nu D) Ps) Bks i ->
    (forall j U T, List.nth_error (List.firstn (ind_nu D) Ps) j = Some U ->
       List.nth_error (tele_insts (ind_uparams D) Id (List.firstn (ind_nu D) Ps)) j = Some T -> Γ ⊢a U ⟸ T) ->
    (forall j Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b -> eb_ann b = Some Z ->
       exists UA u, tele_sub (im_nparams Mj) (sb_of_list Id (List.firstn (ind_nu D) Ps)) ++ Γ ⊢a Z ⟹ UA /\ is_univ_nf UA u) ->
    (forall j Mj b, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       elim_mctx p D j Mj (List.firstn (ind_nu D) Ps) ++ Γ ⊢a eb_motive b ⟸ Typeω@i) ->
    (forall j Mj b c gs n B, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
       ind_con Mj c = Some gs -> List.In (c, n, B) (eb_brs b) ->
       elim_bctx p D Mj gs (blocks_motives Bks) (List.firstn (ind_nu D) Ps) ++ Γ
         ⊢a B ⟸ elim_bty p j Mj c gs (eb_motive b) (List.firstn (ind_nu D) Ps)) ->
    Γ ⊢a a_elim oq (List.firstn (ind_nu D) Ps) m Bks M
       ⟸ (eb_motive bm)[sb_of_list Id (List.skipn (ind_nu D) Ps ++ M :: nil)].
Proof.
  intros * Hl Hg Hm Hb HPl HPt HMe HMc HBt HUc HZc HAc HBc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hgw; pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  set (Us := List.firstn (ind_nu D) Ps) in *; set (NsP := List.skipn (ind_nu D) Ps) in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; unfold im_np in HPl; lia).
  assert (HNPl : List.length NsP = im_nn Mm) by (unfold NsP; rewrite List.length_skipn; unfold im_np in HPl; lia).
  destruct (params_typed_split _ _ D Hc _ _ _ Ps Hm HPl HPt) as [HUt HNPt]; fold Us NsP in HUt, HNPt.
  destruct (im_ref p m Mm) as [pc k] eqn:Hr.
  destruct (im_ref_lookup _ _ _ _ _ _ _ HΓ Hl Hm Hr) as [Dq Hlq].
  destruct (im_ref_member _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq) as [Mk Hk].
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hlq) as [HDq Hcq].
  assert (Emty : forall Us' Ns', ind_mty p D m Us' Ns' = apps (a_ind pc k) (im_pre Mm Us' ++ Ns'))
    by (intros; unfold ind_mty; rewrite Hm; unfold im_ty_at; rewrite Hr; reflexivity).
  destruct (im_pre_params_typed _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq Hk HUl HUt HNPl HNPt) as [HXl HXt].
  destruct (im_pre_typed _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq HUl HUt) as [HPrl HPrt].
  (** The scrutinee infers the type former at parameters equal to the
      derivation's. *)
  inversion HMc as [? W ? ? HMi HMs]; subst.
  pose proof (alg_type_infer_sound HMi HΓ) as HMW.
  assert (exists kW, Γ ⊢ (W : exp) : Typeω@kW) as [kW HWt] by (gen_presups; eauto 2).
  assert (exists kP, Γ ⊢ ind_mty p D m Us NsP : Typeω@kP) as [kP HPs] by (gen_presups; eauto 2).
  assert (HWs : Γ ⊢ (W : exp) ⊆ ind_mty p D m Us NsP)
    by (eapply alg_subtyping_sound; [ exact HMs | eapply lift_exp_max_left; exact HWt | eapply lift_exp_max_right; exact HPs ]).
  rewrite Emty in HWs.
  pose proof (alg_type_infer_self HΓ HMi) as HWW.
  destruct (subtyp_ind_nf HWs Hlq Hk HXl HXt HWW) as (Rs & -> & HRl & HXR).
  assert (Hti : tele_insts (im_params Dq Mk) Id (im_pre Mm Us ++ NsP)
               = tele_insts (ind_uparams Dq) Id (im_pre Mm Us) ++ tele_insts (im_nparams Mk) (sb_of_list Id (im_pre Mm Us)) NsP)
    by (unfold im_params; apply tele_insts_app; [ exact (dc_ass _ Hcq) | exact HPrl ]).
  assert (Hl1 : List.length (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) = ind_nu Dq)
    by (rewrite length_tele_insts by exact (dc_ass _ Hcq); rewrite HPrl; unfold ind_nu in *; lia).
  assert (HPR : forall j N R T, List.nth_error (im_pre Mm Us) j = Some N -> List.nth_error (List.map nf_to_exp Rs) j = Some R ->
             List.nth_error (tele_insts (ind_uparams Dq) Id (im_pre Mm Us)) j = Some T -> Γ ⊢ N ≈ R : T).
  { intros j N R T HN HR HT.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPrl; apply List.nth_error_Some; congruence).
    apply (HXR j); [ rewrite List.nth_error_app1 by lia; exact HN | exact HR | rewrite Hti, List.nth_error_app1 by lia; exact HT ]. }
  assert (Hag : nfs_agree Γ (im_pre Mm Us) (List.firstn (ind_nu Dq) (List.map nf_to_exp Rs)) (tele_insts (ind_uparams Dq) Id (im_pre Mm Us))).
  { apply nfs_agree_of_nth; [ lia | rewrite List.length_firstn; unfold im_np in HRl; lia |].
    intros j N R T HN HR HT.
    assert (Hj : j < ind_nu Dq) by (rewrite <- HPrl; apply List.nth_error_Some; congruence).
    rewrite List.nth_error_firstn in HR; destruct (Nat.ltb_spec j (ind_nu Dq)); [| discriminate ].
    exact (completeness (HPR _ _ _ _ HN HR HT)). }
  (** The rest of the inferred parameters are the member's non-uniform
      ones, equal to the derivation's. *)
  pose proof (wf_ind_apps_inv _ _ _ _ _ _ _ Hlq Hk HWt HRl) as HRt.
  destruct (mty_params_conv _ _ _ _ _ _ _ _ _ _ _ HΓ Hl Hm Hr Hlq Hk HUl HUt HRl HRt HPR) as [HNl HNt [iE HE]].
  set (Ns := List.skipn (ind_nu Dq) (List.map nf_to_exp Rs)) in *.
  destruct (subtyp_ind_inv HWs) as [kk HeqR].
  rewrite <- Emty in HeqR.
  assert (HmE : Γ ⊢ ind_mty p D m Us NsP ≈ ind_mty p D m Us Ns : Typeω@(max kk iE))
    by (etransitivity; [ symmetry; eapply lift_exp_eq_max_left; exact HeqR | eapply lift_exp_eq_max_right; exact HE ]).
  pose proof (mty_params_inj _ _ _ _ _ _ _ _ _ Hl Hm HUl HUt HNPl HNl HNPt HNt HmE) as HNN.
  clear HmE HeqR HE HWs HMs HWW HXR HPR Hti Hl1 HXt HXl HRt HMW HWt HPs.
  pose proof (params_typed_join _ _ D Hc _ _ _ Us Ns Hm HUl HUt HNt) as HPt'.
  assert (HPl' : List.length (Us ++ Ns) = im_np D Mm) by (rewrite List.length_app, HUl, HNl; unfold im_np; lia).
  assert (HPP : forall j P P' T, List.nth_error Ps j = Some P -> List.nth_error (Us ++ Ns) j = Some P' ->
             List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T -> Γ ⊢ P ≈ P' : T).
  { intros j P P' T HP HP' HT.
    assert (EPs : Ps = Us ++ NsP) by (unfold Us, NsP; symmetry; apply List.firstn_skipn).
    rewrite EPs in HP, HT.
    unfold im_params in HT; rewrite tele_insts_app in HT by (try exact (dc_ass _ Hc); exact HUl).
    assert (Hl1 : List.length (tele_insts (ind_uparams D) Id Us) = ind_nu D)
      by (rewrite length_tele_insts by exact (dc_ass _ Hc); rewrite HUl; unfold ind_nu in *; lia).
    destruct (Nat.lt_ge_cases j (ind_nu D)) as [Hj | Hj].
    - rewrite List.nth_error_app1 in HP, HP', HT by lia; rewrite HP in HP'; injection HP' as <-.
      apply wf_exp_eq_refl; exact (HUt _ _ _ HP HT).
    - rewrite List.nth_error_app2 in HP, HP', HT by lia; rewrite HUl in HP, HP'; rewrite Hl1 in HT.
      exact (HNN _ _ _ _ HP HP' HT). }
  (** So the motive's instance is the derivation's. *)
  destruct (wf_elim_params_conv _ _ _ _ _ _ _ _ _ _ i Hl Hm Hb HPl HPt HPl' HPt' HPP HMe HBt) as (_ & _ & Hmot).
  rewrite skipn_app_len in Hmot by exact HUl; fold NsP in Hmot.
  clear HPP HPt' HNN.
  (** One universe for the annotations and the motives. *)
  assert (HΨ : forall j Mj, ind_member D j = Some Mj -> ⊢ (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list).
  { intros j Mj Hj; pose proof (ext_eq_ctx_left _ _ _ _ _ (bt_mctx _ _ _ _ _ _ _ _ HBt _ _ Hj)) as HC.
    unfold elim_mctx in HC; cbn [List.app] in HC; exact (proj1 (ctx_decomp HC)). }
  assert (Hmono : forall Δ A l l', ⊢ Δ -> l <= l' -> Δ ⊢a A ⟸ Typeω@l -> Δ ⊢a A ⟸ Typeω@l').
  { intros Δ A l l' HΔ Hll HA; destruct (Nat.eq_dec l l') as [<- | Hne]; [ exact HA |].
    eapply alg_type_check_subtyp; [ exact HA | apply wf_subtyp_univ; [ exact HΔ | lia ] ]. }
  destruct (nat_bound_upto (fun j l => forall Mj b Z, ind_member D j = Some Mj -> List.nth_error Bks j = Some b ->
              eb_ann b = Some Z -> (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ)%list ⊢a Z ⟸ Typeω@l)
              (List.length Bks)) as [L HL].
  { intros j _.
    destruct (ind_member D j) as [Mj |] eqn:Hj; [| exists 0; intros; discriminate ].
    destruct (List.nth_error Bks j) as [b |] eqn:Hbj; [| exists 0; intros; discriminate ].
    destruct (eb_ann b) as [Z |] eqn:HZ; [| exists 0; intros; congruence ].
    destruct (HZc _ _ _ _ Hj Hbj HZ) as (UA & u & HZi & Hu).
    exists (unf_large u); intros Mj' b' Z' Hj' Hb' HZ'.
    assert (Mj' = Mj) as -> by congruence; assert (b' = b) as -> by congruence; assert (Z' = Z) as -> by congruence.
    eapply alg_type_check_typ_of; [ exact (HΨ _ _ Hj) | exact HZi | exact Hu | apply unf_le_large ]. }
  { intros j l l' Hll HQ Mj b Z Hj Hbj HZ; eapply Hmono; [ exact (HΨ _ _ Hj) | exact Hll | exact (HQ _ _ _ Hj Hbj HZ) ]. }
  set (i' := max i L).
  (** The type, the normal form of the motive's instance. *)
  assert (exists jT, Γ ⊢ (eb_motive bm)[sb_of_list Id (Ns ++ M :: nil)] : Typeω@jT) as [jT HTt] by (gen_presups; eauto).
  destruct (soundness_ty HTt) as (T & HnT & HTe).
  econstructor.
  - eapply ati_elim with (p := p) (D := D) (Mm := Mm) (Dq := Dq) (Mk := Mk) (bm := bm) (i := i'); try eassumption; try reflexivity.
    + exact (bt_len _ _ _ _ _ _ _ _ HBt).
    + exact (bt_nm _ _ _ _ _ _ _ _ HBt).
    + intros j Mj b Z Hj Hbj HZ.
      assert (Hjl : j < List.length Bks) by (rewrite (bt_len _ _ _ _ _ _ _ _ HBt); exact (ind_member_lt _ _ _ Hj)).
      eapply (Hmono _ _ L); [ exact (HΨ _ _ Hj) | unfold i'; lia | exact (HL j Hjl _ _ _ Hj Hbj HZ) ].
    + intros j Mj b Z Hj Hbj HZ.
      destruct (ext_eq_ass_inv _ _ _ _ _ _ _ (bt_ann _ _ _ _ _ _ _ _ HBt _ _ _ _ Hj Hbj HZ)) as (jZ & _ & _ & HZH & _).
      exact (completeness_ty HZH).
    + intros j Mj b Hj Hbj; eapply (Hmono _ _ i);
        [ exact (ext_eq_ctx_left _ _ _ _ _ (bt_mctx _ _ _ _ _ _ _ _ HBt _ _ Hj)) | unfold i'; lia | exact (HAc _ _ _ Hj Hbj) ].
    + exact (bt_names _ _ _ _ _ _ _ _ HBt).
    + exact (bt_counts _ _ _ _ _ _ _ _ HBt).
  - apply alg_subtyping_complete; eapply wf_subtyp_refl'.
    eapply exp_eq_trans_typ_max; [ symmetry; exact HTe | symmetry; exact Hmot ].
Qed.

(** ** Extensions Entry by Entry

    Completeness for an extension is stated for each of its entries, under
    the bound on that entry's lets: a body's expansion has entries its local
    opens generate, whose types are the targets' member types, which the
    body's own lets do not bound; the algorithm does not check them again. *)

Definition alg_entry (Γ : ctx) (e : centry) : Prop :=
  match e with
  | ce_ass A => exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u
  | ce_def A M => (exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u) /\ Γ ⊢a M ⟸ A
  | ce_mod U => Γ ⊢aᵘ U
  end.

Definition ext_entries (n : nat) (Γ Ψ : ctx) : Prop :=
  forall Ψ2 e Ψ1, Ψ = Ψ2 ++ e :: Ψ1 -> centry_lets e <= n -> alg_entry (Ψ1 ++ Γ) e.

Lemma ext_entries_nil : forall n Γ, ext_entries n Γ nil.
Proof. intros n Γ [| ? ?] * H; discriminate. Qed.

Lemma ext_entries_cons : forall n Γ Ψ e, ext_entries n Γ Ψ ->
    (centry_lets e <= n -> alg_entry (Ψ ++ Γ) e) -> ext_entries n Γ (e :: Ψ).
Proof.
  intros * Ht He [| e2 Ψ2] e' Ψ1 Heq Hle; cbn in Heq; injection Heq as -> Heq; [ subst; exact (He Hle) |].
  exact (Ht _ _ _ Heq Hle).
Qed.

Lemma ext_entries_app_r : forall n Γ Ψ2 Ψ, ext_entries n Γ (Ψ2 ++ Ψ) -> ext_entries n Γ Ψ.
Proof. intros * Hx Ψ3 e Ψ1 -> Hle; apply (Hx (Ψ2 ++ Ψ3)); [ rewrite <- List.app_assoc; reflexivity | exact Hle ]. Qed.

Lemma ext_entries_head : forall n Γ Ψ e, ext_entries n Γ (e :: Ψ) -> centry_lets e <= n -> alg_entry (Ψ ++ Γ) e.
Proof. intros * Hx Hle; exact (Hx nil e Ψ eq_refl Hle). Qed.

Lemma ext_entries_alg : forall n Γ Ψ, ext_entries n Γ Ψ -> ctx_lets Ψ <= n -> Γ ⊢aˣ Ψ.
Proof.
  intros n Γ; induction Ψ as [| e Ψ IH]; intros Hx Hl; [ constructor |]; cbn [ctx_lets] in Hl.
  pose proof (ext_entries_head _ _ _ _ Hx ltac:(lia)) as He.
  pose proof (IH (ext_entries_app_r _ _ (e :: nil) _ Hx) ltac:(lia)) as Ht.
  destruct e; cbn [alg_entry] in He; destruct_all; econstructor; eauto.
Qed.

(** A body checked from its expansion's entries: its own entries are
    bounded by its lets; those its opens generate are not looked at. *)
Lemma alg_body_of_entries : forall n Γ0 Δ Φ Φx, body_xp gc_deps gc_stack (Δ ++ Γ0) Φ Φx ->
    ext_entries n Γ0 (body_ctx Φx ++ Δ) -> gmod_lets Φ <= n -> body_shape Φ Φ ->
    (forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> S (modexp_lets H) <= n -> Ψ ++ Δ ++ Γ0 ⊢aᵐ H) ->
    Δ ++ Γ0 ⊢aᵇ Φ ⇝ Φx.
Proof.
  intros * Hx; remember (Δ ++ Γ0) as G eqn:HG; revert HG.
  induction Hx as [G | G Φ Φx x E Hx IH | G Φ Φx H its R Rm gs Hx IH HR HRm Hg Hok]; intros -> HE Hl Hs Ho; cbn [gmod_lets] in Hl.
  - constructor.
  - cbn [body_shape] in Hs; destruct Hs as (Hs & _ & HsE).
    assert (HEt : ext_entries n Γ0 (body_ctx Φx ++ Δ)).
    { destruct E as [? ? ? [] | | | | ]; cbn [body_ctx List.app] in HE; exact (ext_entries_app_r _ _ (_ :: nil) _ HE). }
    specialize (IH eq_refl HEt ltac:(lia) Hs Ho).
    destruct E as [b pv A [M |] | pm U | ? ? ? | ? ? ? ? | ? ? ?]; cbn in HsE; try contradiction.
    + pose proof (ext_entries_head _ _ _ _ HE) as He; cbn [body_ctx List.app gentry_lets centry_lets alg_entry] in He, Hl.
      rewrite <- List.app_assoc in He; destruct (He ltac:(lia)) as ((UA & u & HA & Hu) & HM).
      econstructor; eassumption.
    + pose proof (ext_entries_head _ _ _ _ HE) as He; cbn [body_ctx List.app gentry_lets centry_lets alg_entry] in He, Hl.
      rewrite <- List.app_assoc in He; specialize (He ltac:(lia)).
      econstructor; eassumption.
  - cbn [body_shape] in Hs; destruct Hs as [Hs _].
    cbn [body_opens] in Ho; rewrite <- (items_gen_length _ _ _ _ _ _ _ Hg), gm_dropn_gens_append in Ho.
    rewrite gens_body_ctx_base, <- List.app_assoc in HE.
    specialize (IH eq_refl (ext_entries_app_r _ _ _ _ HE) ltac:(lia) Hs (fun k => Ho (S k))).
    pose proof (Ho 0 _ _ eq_refl ltac:(lia)) as HH.
    econstructor; eassumption.
Qed.

(** A well-formed module expression checks, given that its arguments and
    its literals do: they are reached by generation ([modexp_gen]), whatever
    reducts its derivation goes through. *)
Lemma alg_modexp_of_wf : forall n,
    (forall Γ A M, gc_deps ⍮ gc_stack ⍮ Γ ⊢ M : A -> exp_lets M <= n -> Γ ⊢a M ⟸ A) ->
    (forall Γ U, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> gunit_lets U <= n -> Γ ⊢aᵘ U) ->
    forall H Γ, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> modexp_lets H <= n -> Γ ⊢aᵐ H.
Proof.
  intros n HM HU; induction H as [fp | x | H IH y | H IH N | U]; intros Γ HH Hl;
    pose proof (proj1 (modexp_gen _ _ _ _ _ HH)) as Hgen; cbn [gen_m modexp_lets] in Hgen, Hl.
  - destruct (me_mtele _ _ _ HH) as (R & T & Hm & Ht); econstructor; eassumption.
  - destruct (me_denotes _ _ _ _ _ HH) as (R & _ & Hm & _).
    inversion Hm; subst; try (unfold gc_unit in *; cbn in *; discriminate).
    econstructor; eassumption.
  - destruct (me_mtele _ _ _ HH) as (R & T & Hm & Ht).
    eapply amod_mem; [ apply IH; [ exact Hgen | lia ] | exact Hm | exact Ht ].
  - destruct Hgen as (HH0 & R & T & B & T1 & i & Hm & Ht & Hv & HB & HN).
    eapply amod_app; [ apply IH; [ exact HH0 | lia ] | exact Hm | exact Ht | exact Hv | apply HM; [ exact HN | lia ] ].
  - apply amod_lit, HU; [ exact (unit_eq_of_full _ _ _ _ Hgen) | exact Hl ].
Qed.

(** An extension of an extension is one extension. *)
Lemma alg_ext_app : forall Γ Δ Ψ, Γ ⊢aˣ Δ -> Δ ++ Γ ⊢aˣ Ψ -> Γ ⊢aˣ Ψ ++ Δ.
Proof.
  intros * HΔ HΨ; remember (Δ ++ Γ) as G eqn:HG; induction HΨ; subst; cbn [List.app];
    [ exact HΔ | .. ]; econstructor; rewrite <- ?List.app_assoc; eauto.
Qed.

(** A unit under parameters [Δ] is the unit over its own parameters and
    [Δ], the algorithmic counterpart of [wf_unit_eq_flatten]. *)
Lemma alg_unit_flatten : forall Γ Δ Δ' D,
    Γ ⊢aˣ Δ -> tele_ass Δ -> Δ ++ Γ ⊢aᵘ gu_mk Δ' D -> Γ ⊢aᵘ gu_mk (Δ' ++ Δ) D.
Proof.
  intros * HΔ Ha HU; inversion HU; subst.
  - eapply aunit_body; [ eapply alg_ext_app; eassumption | apply List.Forall_app; split; assumption
                       | rewrite <- List.app_assoc; eassumption | assumption .. ].
  - eapply aunit_alias; [ eapply alg_ext_app; eassumption | apply List.Forall_app; split; assumption
                        | rewrite <- List.app_assoc; eassumption ].
Qed.

(** ** Records, Algorithmically *)

(** A field of a tuple has at most the tuple's unannotated [let]s. *)
Lemma tuple_field_lets : forall T (fs : list (String.string * exp)) k f M,
    List.nth_error fs k = Some (f, M) -> exp_lets M <= exp_lets (a_tuple T fs).
Proof.
  intros T fs; cbn [exp_lets].
  enough (H : forall k f M, List.nth_error fs k = Some (f, M) ->
                exp_lets M <= (fix fields_lets (fs : list (String.string * exp)) : nat :=
                                 match fs with
                                 | nil => 0
                                 | f :: fs' => exp_lets (snd f) + fields_lets fs'
                                 end) fs) by (intros; pose proof (H _ _ _ ltac:(eassumption)); lia).
  induction fs as [| [g N] fs IH]; intros [| k] f M Hk; cbn in Hk |- *; try discriminate.
  - injection Hk as <- <-; lia.
  - pose proof (IH _ _ _ Hk); lia.
Qed.

(** A record's type former checks at its type. *)
Lemma alg_record_complete : forall Γ p R, ⊢ Γ -> record_lookup gc_deps gc_stack p = Some R ->
    Γ ⊢a a_record p ⟸ record_ty R.
Proof.
  intros * HΓ Hl.
  destruct (record_former_typed _ _ _ HΓ Hl) as [j [_ Hj]].
  destruct (soundness_ty Hj) as [W [HW HWe]].
  econstructor; [ eapply ati_record; eassumption | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
Qed.

(** A tuple checks at its annotation: the annotation normalises to the
    record type at the normal forms [Rs] of its parameters
    ([subtyp_record_nf]), and each field's type at them is its type at the
    parameters, where the field checks. *)
Lemma alg_tuple_complete : forall Γ T (fs : list (String.string * exp)) p R Ns i,
    Γ ⊢ T : Typeω@i -> Γ ⊢a T ⟸ Typeω@i ->
    Γ ⊢ T ≈ apps_exp (a_record p) Ns : Typeω@i ->
    Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A -> Γ ⊢ N : A) ->
    List.map fst fs = List.map fst (record_fields R) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       Γ ⊢ M : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
    (forall k f M U, List.nth_error fs k = Some (f, M) -> List.nth_error (record_fields R) k = Some (f, U) ->
       Γ ⊢a M ⟸ U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]) ->
    Γ ⊢a a_tuple T fs ⟸ T.
Proof.
  intros * HTt HTc HTeq Hrt Hl Hn HNs Hfs HMt HMc.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  destruct (alg_type_check_typ_implies_alg_type_infer_typ HΓ HTc) as (UT & u & HTi & Hu & _).
  destruct (soundness_ty HTt) as [W [HW HWe]].
  destruct (subtyp_record_nf (wf_subtyp_refl' _ _ _ _ _ _ HTeq) Hl Hn HNs HW) as (Rs & -> & HRl & HNR).
  assert (Hlf : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
  econstructor; [| apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
  eapply ati_tuple; [ exact HTi | exact Hu | exact HW | exact Hl | exact Hfs |].
  intros k f M U Hk Hfk.
  assert (Hkl : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
  pose proof (record_fields_insts_eq _ _ _ p R Ns (List.map nf_to_exp Rs) fs fs Hrt Hl Hn HRl HNR Hfs eq_refl
                ltac:(intros * HM HM' HU; rewrite HM in HM'; injection HM' as <-; apply wf_exp_eq_refl; eapply HMt; eassumption)
                k ltac:(lia)) as Hins.
  destruct (record_field_typ_cong _ _ _ R k f U (Ns ++ List.firstn k (List.map snd fs))
              (List.map nf_to_exp Rs ++ List.firstn k (List.map snd fs)) Hc Hass HF HΓ Hfk
              ltac:(rewrite ?List.length_app, ?List.length_firstn, ?List.length_map in *; lia)
              ltac:(rewrite ?List.length_app, ?List.length_firstn, ?List.length_map in *; lia) Hins) as [j HUU].
  eapply alg_type_check_conv; [ exact (HMc _ _ _ _ Hk Hfk) | exact HUU ].
Qed.

(** A projection checks at its field's type at the parameters of the
    element's type: the element infers the record type at the normal forms
    of its parameters ([subtyp_record_nf]), at which the field's type is
    equal to that one. *)
Lemma alg_proj_complete : forall Γ M p R Ns k f U i,
    Γ ⊢ M : apps_exp (a_record p) Ns -> Γ ⊢a M ⟸ apps_exp (a_record p) Ns ->
    Γ ⊢ a_record p : record_ty R -> record_lookup gc_deps gc_stack p = Some R ->
    List.length Ns = List.length (record_params R) ->
    (forall k N A, List.nth_error Ns k = Some N -> List.nth_error (tele_insts (record_params R) Id Ns) k = Some A -> Γ ⊢ N : A) ->
    List.nth_error (record_fields R) k = Some (f, U) ->
    Γ ⊢ U[sb_of_list Id (Ns ++ record_pre R k M)] : Typeω@i ->
    Γ ⊢a a_proj f M ⟸ U[sb_of_list Id (Ns ++ record_pre R k M)].
Proof.
  intros * HMt HMc Hrt Hl Hn HNs Hfk HUt.
  assert (HΓ : ⊢ Γ) by (gen_presups; assumption).
  destruct (wf_record_inversion Hrt) as [R0 Hl0 Hnd Hass i0 Hty HF HS HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  inversion HMc as [? W ? ? HMi HMs]; subst.
  pose proof (alg_type_infer_sound HMi HΓ) as HMW.
  assert (exists kW, Γ ⊢ (W : exp) : Typeω@kW) as [kW HWt] by (gen_presups; eauto 2).
  assert (exists kP, Γ ⊢ apps_exp (a_record p) Ns : Typeω@kP) as [kP HPs] by (gen_presups; eauto 2).
  assert (HWs : Γ ⊢ (W : exp) ⊆ apps_exp (a_record p) Ns)
    by (eapply alg_subtyping_sound; [ exact HMs | eapply lift_exp_max_left; exact HWt | eapply lift_exp_max_right; exact HPs ]).
  pose proof (alg_type_infer_self HΓ HMi) as HWW.
  destruct (subtyp_record_nf HWs Hl Hn HNs HWW) as (Rs & -> & HRl & HNR).
  destruct (alg_proj_typed _ _ _ _ _ _ _ _ HΓ HMW Hl Hfk) as (m & HUR & _).
  destruct (soundness_ty HUR) as [V [HV HVe]].
  destruct (record_sort_large _ _ _ _ _ _ Hrt Hl Hn HNs) as [n Hm].
  pose proof (record_field_params_cong _ _ _ M p R Ns (List.map nf_to_exp Rs) n k f U HMt Hrt Hl Hn HRl HNs HNR Hm Hfk) as HUU.
  econstructor; [ eapply ati_proj; [ exact HMi | exact Hl | exact (field_index_nth_nodup _ _ _ _ Hnd Hfk) | exact Hfk | exact HV ] |].
  apply alg_subtyping_complete; eapply wf_subtyp_refl'.
  eapply exp_eq_trans_typ_max; [ symmetry; exact HVe | symmetry; exact HUU ].
Qed.

(** The whole block, the universes included; [alg_type_complete_lets] below
    is the statement without them. *)
Lemma alg_type_complete_lets_all : forall n,
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M ->
     exp_lets M <= n -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ U, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack ->
     ext_entries n Γ Ψ /\ ext_entries n Γ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack ->
     (gunit_lets U <= n -> Γ ⊢aᵘ U) /\ (gunit_lets U' <= n -> Γ ⊢aᵘ U')) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> True).
Proof.
  intros n; induction n as [n IHn] using lt_wf_ind.
  (** A module expression, by generation, below the bound. *)
  assert (HmH : forall Γ' H0, gc_deps ⍮ gc_stack ⍮ Γ' ⊢ᵐ H0 ≈ H0 -> modexp_lets H0 < n -> Γ' ⊢aᵐ H0).
  { intros Γ' H0 HH0 Hlt; destruct (IHn _ Hlt) as (_ & IHt & _ & _ & _ & _ & IHu & _).
    eapply (alg_modexp_of_wf (modexp_lets H0)); [| | exact HH0 | lia ].
    - intros; eapply IHt; [ eassumption | reflexivity | reflexivity | apply user_exp_all | assumption ].
    - intros * HU0 HlU; exact (proj1 (IHu _ _ _ _ _ HU0 eq_refl eq_refl) HlU). }
  apply syntactic_wf_mut_ind; intros; try exact I; subst; destruct_let_ann; destruct_univ;
    repeat match goal with IH : ?x = ?x -> _ |- _ => specialize (IH eq_refl) end;
    repeat match goal with IH : user_exp ?M -> _ |- _ => specialize (IH (user_exp_all M)) end;
    try match goal with Hue : user_exp _ |- _ => clear Hue end;
    try match goal with |- (_ <= n -> _) /\ (_ <= n -> _) => split; intros end;
    repeat match goal with
           | IH : _ <= n -> _ |- _ => specialize (IH ltac:(lets_bound))
           | IH : (_ <= n -> ?P) /\ ?Q |- _ =>
               let H' := fresh in
               assert (H' : P /\ Q) by (split; [ apply (proj1 IH); lets_bound | exact (proj2 IH) ]);
               clear IH; rename H' into IH
           | IH : ?P /\ (_ <= n -> ?Q) |- _ =>
               let H' := fresh in
               assert (H' : P /\ Q) by (split; [ exact (proj1 IH) | apply (proj2 IH); lets_bound ]);
               clear IH; rename H' into IH
           end.
  (** Only the unannotated [let] needs the outer induction. *)
  all: try (lazymatch goal with |- _ ⊢a ℓ ≔ _ in _ ⟸ _ => fail | _ => clear IHn end).
  all: match goal with |- _ ⊢a a_elim _ _ _ _ _ ⟸ _ => idtac | |- _ ⊢a _ ⟸ _ =>
         gen_presups;
         (** A universe, [⊤] and [⊥] infer their own universe. *)
         try solve [ eapply alg_type_check_suniv;
                     [ assumption | mauto 3 | constructor | cbn; apply lvl_le_lit; lia ]
                   | eapply alg_type_check_typ_of;
                     [ assumption | mauto 3 | constructor | cbn; first [ exact I | lia ] ] ];
         (** A small universe at a level term infers the normal form of the
             universe above it. *)
         try match goal with
           | |- _ ⊢a a_univ ?M ⟸ a_univ (succl ?M) =>
               match goal with Hc : alg_type_check ?G (a_level _) M, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               assert (HSU : Γ ⊢ Type⟨succl M⟩ : Typeω@0)
                 by (eapply wf_univ_large_tm; [ assumption | eapply wf_succl; eassumption ]);
               destruct (soundness_ty HSU) as [W [HW HWe]];
               econstructor; [ eapply ati_suniv; eassumption |];
               apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe
           end;
         (** The level forms infer a type of levels below the one they are
             checked against. *)
         try solve [ lazymatch goal with
           | |- alg_type_check _ (a_level _) (a_llit _) =>
               eapply alg_type_check_level_of; [ assumption | constructor | lia ]
           | |- alg_type_check _ (a_level _) (a_succl ?M) =>
               match goal with Hc : alg_type_check ?G (a_level _) M, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               eapply alg_type_check_level_of; [ assumption | constructor; eassumption | lia ]
           | |- alg_type_check _ (a_level _) (a_maxl ?M ?N) =>
               match goal with Hc : alg_type_check ?G (a_level _) M, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               match goal with Hc : alg_type_check ?G (a_level _) N, HG : ⊢ ?G |- _ =>
                 destruct (alg_type_check_level_infer HG Hc) as (? & ? & ?) end;
               eapply alg_type_check_level_of; [ assumption | constructor; eassumption | lia ]
           end ];
         mauto 4 using alg_subtyping_complete, alg_type_check_subtyp | _ => idtac end.
  (** An unannotated [let].  The definiens infers [A'], a subtype of the [A]
      of the derivation, so the body's derivation is moved to [Γ ▸ A' ≔ M] by
      refinement.  That derivation is no subderivation, but its subject has
      fewer unannotated [let]s, which is what the outer induction is for. *)
  10:{ match goal with Hc : Γ ⊢a M ⟸ A |- _ => inversion Hc as [? A' ? ? HMi HMs]; subst end.
      assert (Γ ⊢ M : A') by mauto 3 using alg_type_infer_sound.
      assert (exists k, Γ ⊢ A' : Typeω@k) as [k HA'] by (gen_presups; eauto 2).
      assert (Γ ⊢ A' : Typeω@(max i k)) by mauto 3 using lift_exp_max_right.
      assert (Γ ⊢ A : Typeω@(max i k)) by mauto 3 using lift_exp_max_left.
      assert (Γ ⊢ A' ⊆ A) by mauto 3 using alg_subtyping_sound.
      assert (Γ ▸ A' ≔ M ⊢ˢ Id : Γ ▸ A ≔ M) by (eapply wf_sub_id_extend_def; mauto 3).
      assert (HB' : Γ ▸ A' ≔ M ⊢ B : C) by mauto 3.
      assert (HBa : Γ ▸ A' ≔ M ⊢a B ⟸ C).
      { destruct (IHn (exp_lets B) ltac:(lets_bound)) as (_ & IHt & _).
        eapply IHt; [ exact HB' | reflexivity | reflexivity | apply user_exp_all | lia ]. }
      clear IHn.
      inversion HBa as [? C' ? ? HBi HBs]; subst.
      assert (⊢ Γ ▸ A' ≔ M) by mauto 3.
      assert (Γ ▸ A' ≔ M ⊢ B : C') by mauto 3 using alg_type_infer_sound.
      assert (exists k, Γ ▸ A' ≔ M ⊢ C' : Typeω@k) as [k1] by (gen_presups; eauto 2).
      assert (exists k, Γ ▸ A ≔ M ⊢ C : Typeω@k) as [k2] by (gen_presups; eauto 2).
      assert (Γ ▸ A' ≔ M ⊢ C : Typeω@k2) by mauto 3.
      assert (Γ ▸ A' ≔ M ⊢ C' ⊆ C)
        by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
      assert (Γ ⊢ˢ Id,,M : Γ ▸ A' ≔ M) by (eapply wf_sub_single_def; eassumption).
      assert (Γ ⊢ C'[Id,,M] : Typeω@k1) by mauto 3.
      assert (exists W, nbe_ty_f Γ C'[Id,,M] W /\ Γ ⊢ C'[Id,,M] ≈ W : Typeω@k1) as [W []]
        by (eapply soundness_ty; mauto 3).
      assert (Γ ⊢ C'[Id,,M] ⊆ C[Id,,M]) by mauto 3.
      assert (Γ ⊢ W ⊆ C[Id,,M]) by (transitivity C'[Id,,M]; mauto 3).
      econstructor; [ eapply ati_let_none; eauto | mauto 4 using alg_subtyping_complete ]. }
  (** A module [let], through its body. *)
  11:{ destruct H0 as [HUa _].
       inversion H4 as [? C' ? ? HBi HBs]; subst.
       assert (Γ ▹ₘ U ⊢ B : C') by mauto 3 using alg_type_infer_sound.
       assert (exists k, Γ ▹ₘ U ⊢ C' : Typeω@k) as [k HCk] by (gen_presups; eauto 2).
       pose proof (wf_sub_single_mod _ _ _ _ H) as Hσ.
       pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCk Hσ) as HC'σ.
       destruct (soundness_ty HC'σ) as [W [HW HWe]].
       assert (Γ ▹ₘ U ⊢ C' ⊆ C)
         by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
       assert (Γ ⊢ C'[Id ,,ₘ me_lit U] ⊆ C[Id ,,ₘ me_lit U]) by mauto 3.
       assert (Γ ⊢ W ⊆ C[Id ,,ₘ me_lit U]) by (transitivity C'[Id ,,ₘ me_lit U]; mauto 3).
       econstructor; [ eapply ati_let_mod; eauto | mauto 4 using alg_subtyping_complete ]. }
  (** A record's type former, a projection and a tuple ([alg_record_complete],
      [alg_proj_complete], [alg_tuple_complete]); the fields of a tuple are
      below its bound on [let]s ([tuple_field_lets]). *)
  all: try solve [ eapply alg_record_complete; eassumption ].
  all: try solve [ eapply alg_proj_complete; eassumption ].
  all: try match goal with
    | HTt : _ ⊢ ?T : Typeω@?i, HTc : _ ⊢a ?T ⟸ Typeω@?i, HTe : _ ⊢ ?T ≈ apps_exp (a_record _) _ : _,
      HMs : forall k f M U, List.nth_error ?fs k = Some (f, M) -> _ -> _ = _ -> _ = _ -> user_exp M -> exp_lets M <= _ -> _ ⊢a M ⟸ _,
      Hbd : exp_lets (a_tuple ?T ?fs) <= _ |- _ ⊢a a_tuple ?T ?fs ⟸ _ =>
        eapply alg_tuple_complete; [ exact HTt | exact HTc | exact HTe | eassumption .. |];
        let k := fresh "k" in let f := fresh "f" in let M := fresh "M" in let U := fresh "U" in
        let Hk := fresh "Hk" in let Hfk := fresh "Hfk" in
        intros k f M U Hk Hfk; apply (HMs _ _ _ _ Hk Hfk eq_refl eq_refl (user_exp_all _));
        pose proof (tuple_field_lets T fs k f M Hk); lia
    end.
  (** A member, at the normal form of the type its module's description
      reads; the module, by generation. *)
  all: try match goal with
    | HH : _ ⍮ _ ⍮ ?G ⊢ᵐ ?H0 ≈ ?H0, Hm : mdenote _ _ ?G (me_mem ?H0 ?x0) _, Ht : ds_ty _ _ _ = Some ?A0,
      HA : ?G ⊢ ?A0 : Typeω@_, Hb : exp_lets (a_mem ?H0 ?x0) <= _ |-?G ⊢a a_mem ?H0 ?x0 ⟸ ?A0 =>
        cbn [exp_lets] in Hb;
        let W := fresh "W" in let HW := fresh "HW" in let HWe := fresh "HWe" in
        destruct (soundness_ty HA) as [W [HW HWe]];
        econstructor; [ eapply ati_mem; [ apply HmH; [ exact HH | lia ] | exact Hm | exact Ht | exact HW ]
                      | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ]
    end.
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists UA u, Γ ▹ ⊥ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]] by mauto 3.
    assert (Γ ⊢ A[Id,,M] : Typeω@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Typeω@i) as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  (** The type former and a constructor: at the normal forms of their
      types. *)
  - destruct (decl_of_lookup _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)) as [HD Hc].
    destruct (ind_ty_typed _ _ _ _ _ _ HD Hc ltac:(eassumption) ltac:(eassumption)) as [j Hj].
    destruct (soundness_ty Hj) as [W [HW HWe]].
    econstructor; [ eapply ati_ind; eassumption | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
  - assert (HΓ1 : ⊢ Γ) by assumption.
    match goal with Hl : ind_lookup _ _ _ = Some _, Hk : ind_member _ _ = Some _, Hcon : ind_con _ _ = Some _ |- _ =>
      destruct (con_ty_typed _ _ _ _ _ _ _ _ _ (ctx_wf_gctx _ _ _ HΓ1) (decls_of_ctx _ _ _ HΓ1) Hl Hk Hcon HΓ1) as [j Hj] end.
    destruct (soundness_ty Hj) as [W [HW HWe]].
    econstructor; [ eapply ati_con; eassumption | apply alg_subtyping_complete; eapply wf_subtyp_refl'; symmetry; exact HWe ].
  (** The eliminator ([alg_elim_complete]): its parts by the induction
      hypotheses, under the bound on [let]s ([elim_lets_parts]). *)
  - match goal with
    | Hl : ind_lookup _ _ ?p = Some ?D, Hg : elim_grp ?D ?oq ?p ?m, Hm : ind_member ?D ?m = Some ?Mm,
      Hb : List.nth_error ?Bks ?m = Some ?bm, HPl : List.length ?Ps = im_np ?D ?Mm,
      Hbd : exp_lets (a_elim ?oq _ ?m ?Bks ?M) <= _,
      HAt : forall k Mk b, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> _ ⊢ eb_motive b : Typeω@?i,
      HUs : forall k P T, List.nth_error ?Ps k = Some P -> List.nth_error (tele_insts (im_params ?D ?Mm) Id ?Ps) k = Some T ->
              _ = _ -> _ = _ -> user_exp P -> exp_lets P <= _ -> _ ⊢a P ⟸ T,
      HZs : forall k Mk b Z, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> eb_ann b = Some Z ->
              _ = _ -> _ = _ -> ext_entries _ _ _ /\ _,
      HAs : forall k Mk b, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> _ = _ -> _ = _ ->
              user_exp (eb_motive b) -> exp_lets (eb_motive b) <= _ -> _ ⊢a eb_motive b ⟸ _,
      HBs : forall k Mk b c gs n0 B, ind_member ?D k = Some Mk -> List.nth_error ?Bks k = Some b -> ind_con Mk c = Some gs ->
              List.In (c, n0, B) (eb_brs b) -> _ = _ -> _ = _ -> user_exp B -> exp_lets B <= _ -> _ ⊢a B ⟸ _ |- _ =>
        destruct (elim_lets_parts oq (List.firstn (ind_nu D) Ps) m Bks M) as (HLu & HLz & HLa & HLb & _);
        assert (HΓe : ⊢ Γ) by (gen_presups; assumption);
        destruct (decl_of_lookup _ _ _ _ _ HΓe Hl) as [_ Hc];
        eapply (alg_elim_complete Γ p D oq m Mm bm Bks Ps M i);
          [ exact Hl | exact Hg | exact Hm | exact Hb | exact HPl | eassumption | eassumption | eassumption
          | constructor; assumption | | | | ];
        [ intros j U T HU HT
        | intros j Mj b Z Hj Hbj HZ; destruct (HZs _ _ _ _ Hj Hbj HZ eq_refl eq_refl) as [HE _];
          apply (ext_entries_head _ _ _ _ HE); cbn [centry_lets];
          pose proof (HLz b Z (List.nth_error_In _ _ Hbj) HZ); lia
        | intros j Mj b Hj Hbj; apply (HAs _ _ _ Hj Hbj eq_refl eq_refl (user_exp_all _));
          pose proof (HLa b (List.nth_error_In _ _ Hbj)); lia
        | intros j Mj b c gs n1 B Hj Hbj Hcon Hin; apply (HBs _ _ _ _ _ _ _ Hj Hbj Hcon Hin eq_refl eq_refl (user_exp_all _));
          pose proof (HLb b _ (List.nth_error_In _ _ Hbj) Hin); cbn [snd] in *; lia ];
        assert (Hj : j < ind_nu D)
          by (assert (j < List.length (List.firstn (ind_nu D) Ps)) by (apply List.nth_error_Some; congruence);
              rewrite List.length_firstn in *; lia);
        assert (HUP : List.nth_error Ps j = Some U)
          by (rewrite <- (List.firstn_skipn (ind_nu D) Ps), List.nth_error_app1 by (rewrite List.length_firstn; unfold im_np in *; lia);
              exact HU);
        assert (HFl : List.length (List.firstn (ind_nu D) Ps) = List.length (ind_uparams D))
          by (rewrite List.length_firstn; change (List.length (ind_uparams D)) with (ind_nu D); unfold im_np in HPl; lia);
        assert (HTP : List.nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T)
          by (rewrite <- (List.firstn_skipn (ind_nu D) Ps) at 1; unfold im_params;
              rewrite tele_insts_app by (try exact (dc_ass _ Hc); exact HFl);
              rewrite List.nth_error_app1; [ exact HT | rewrite length_tele_insts by exact (dc_ass _ Hc); unfold ind_nu in Hj; lia ]);
        apply (HUs j U T HUP HTP eq_refl eq_refl (user_exp_all _));
        pose proof (HLu U (List.nth_error_In _ _ HU)); lia
    end.
  (** [Π], at either tier: the join of the two indices is below the universe
      of the rule's conclusion. *)
  - assert (exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]] by mauto 3.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (exists UB v, Γ ▹ A ⊢a B ⟹ UB /\ is_univ_nf UB v /\ unf_le v (unl i))
        as [UB [v [? []]]] by mauto 3.
    assert (HAu : Γ ⊢ A : unf_tm u)
      by (rewrite <- nf_to_exp_univ_nf; match goal with Hu : is_univ_nf ?UA u |- _ => rewrite <- (is_univ_nf_eq _ _ Hu) end;
          eapply alg_type_infer_sound; eassumption).
    assert (HBv : Γ ▹ A ⊢ B : unf_tm v)
      by (rewrite <- nf_to_exp_univ_nf; match goal with Hv : is_univ_nf ?UB v |- _ => rewrite <- (is_univ_nf_eq _ _ Hv) end;
          eapply alg_type_infer_sound; eassumption).
    assert (Hvws : unf_ws (Γ ▹ A) v).
    { match goal with Hv : is_univ_nf ?UB v, Hi : _ ▹ _ ⊢a B ⟹ ?UB |- _ =>
        pose proof (alg_type_infer_self ltac:(eassumption) Hi) as HnB;
        rewrite (is_univ_nf_eq _ _ Hv) in HnB end.
      assert (exists k, Γ ▹ A ⊢ unf_tm v : Typeω@k) as [kv Hkv] by (gen_presups; eauto 2).
      eapply unf_ws_of_nbe; [ exact Hkv | rewrite <- nf_to_exp_univ_nf; exact HnB ]. }
    destruct (wf_unf_pi_tm HAu HBv Hvws) as [k Hk].
    eapply (alg_pi_check_of_infer _ _ _ _ _ u v _ (S i)); try eassumption; [ mauto 3 |].
    eapply unf_pi_tm_large; eassumption.
  (** The small [Π], at a level term. *)
  - eapply alg_pi_small_complete; eassumption.
  - assert (exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]] by mauto 3.
    assert (Γ ▹ A ⊢a M ⟸ B) by mauto 3.
    assert (exists B', Γ ▹ A ⊢a M ⟹ B' /\ Γ ▹ A ⊢a B' ⊆ B) as [B' []] by (inversion_clear_by_head alg_type_check; firstorder).
    assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Typeω@i) as [W []] by mauto 3 using soundness_ty.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ▹ A ⊢ M : B') by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ A ⊢ B' : Typeω@j) as [] by (gen_presups; eauto 2).
    econstructor; mauto 3.
    eapply alg_subtyping_complete.
    eapply wf_subtyp_pi'; mauto 2.
    mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
  - assert (Γ ⊢a M ⟸ Π A B) by mauto 2.
    assert (Γ ⊢a N ⟸ A) by mauto 2.
    assert (exists A' B', Γ ⊢a M ⟹ Πⁿ A' B' /\ Γ ⊢ A' ≈ A : Typeω@i /\ Γ ▹ A ⊢a B' ⊆ B) as [A' [B' [? []]]] by mauto 3.
    assert (Γ ⊢ M : Πⁿ A' B') by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ⊢ Π A' B' : Typeω@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ A' : Typeω@j /\ Γ ▹ (A' : exp) ⊢ B' : Typeω@j) as [] by mauto 3.
    assert (Γ ⊢ N : A') by mauto 3.
    assert (Γ ⊢ B'[Id,,N] : Typeω@j) by mauto 3.
    assert (exists W, nbe_ty_f Γ B'[Id,,N] W /\ Γ ⊢ B'[Id,,N] ≈ W : Typeω@j) as [W []] by (eapply soundness_ty; mauto 3).
    assert (Γ ▹ A ⊢ B' : Typeω@j) by mauto 4.
    assert (Γ ▹ A ⊢ B' ⊆ B) by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert (Γ ⊢ B'[Id,,N] ⊆ B[Id,,N]) by mauto 3.
    assert (Γ ⊢ W ⊆ B[Id,,N]) by (transitivity B'[Id,,N]; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i))
        as [UA [u [? []]]] by mauto 3.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢a B ⟸ C) by mauto 2.
    assert (exists C', Γ ▸ A ≔ M ⊢a B ⟹ C' /\ Γ ▸ A ≔ M ⊢a C' ⊆ C) as [C' []]
        by (inversion_clear_by_head alg_type_check; firstorder).
    assert (Γ ▸ A ≔ M ⊢ B : C') by mauto 3 using alg_type_infer_sound.
    assert (exists k, Γ ▸ A ≔ M ⊢ C' : Typeω@k) as [k] by (gen_presups; eauto 2).
    assert (exists k', Γ ▸ A ≔ M ⊢ C : Typeω@k') as [k'] by (gen_presups; eauto 2).
    assert (Γ ▸ A ≔ M ⊢ C' ⊆ C)
      by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert (Γ ⊢ C'[Id,,M] : Typeω@k) by mauto 3.
    assert (exists W, nbe_ty_f Γ C'[Id,,M] W /\ Γ ⊢ C'[Id,,M] ≈ W : Typeω@k) as [W []]
        by (eapply soundness_ty; mauto 3).
    assert (Γ ⊢ C'[Id,,M] ⊆ C[Id,,M]) by mauto 3.
    assert (Γ ⊢ W ⊆ C[Id,,M]) by (transitivity C'[Id,,M]; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Typeω@i) as [W []] by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  (** Extensions, entry by entry. *)
  - split; apply ext_entries_nil.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
      match goal with IHA : exp_lets A <= n -> _ ⊢a A ⟸ _ |- _ =>
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ (IHA Hle)) as [UA [u [Hj [Hu _]]]] end; eauto.
    + pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
      match goal with IHA : exp_lets A' <= n -> _ ⊢a A' ⟸ _ |- _ =>
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ' (IHA Hle)) as [UA [u [Hj [Hu _]]]] end; eauto.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
      match goal with IHA : exp_lets A <= n -> _ ⊢a A ⟸ _, IHM : exp_lets M <= n -> _ ⊢a M ⟸ _ |- _ =>
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ (IHA ltac:(lia))) as [UA [u [Hj [Hu _]]]];
        split; [ eauto | exact (IHM ltac:(lia)) ] end.
    + pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
      match goal with IHA : exp_lets A' <= n -> _ ⊢a A' ⟸ _, IHM : exp_lets M' <= n -> _ ⊢a M' ⟸ _ |- _ =>
        destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ' (IHA ltac:(lia))) as [UA [u [Hj [Hu _]]]];
        split; [ eauto | exact (IHM ltac:(lia)) ] end.
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl HXr] end.
    split; apply ext_entries_cons; try assumption; intros Hle; cbn [centry_lets alg_entry] in *.
    + match goal with IHU : (gunit_lets U <= n -> _ ⊢aᵘ U) /\ _ |- _ => exact (proj1 IHU Hle) end.
    + match goal with IHU : (gunit_lets U' <= n -> ?G ⊢aᵘ U') /\ _, _ : _ ⍮ _ ⍮ ?G ⊢ᵘ U' ≈ U' |- _ => exact (proj1 IHU Hle) end.
  (** Units: a body from the entries of its expansion that are its own, and
      the targets of its opens. *)
  - match goal with
    | HX : ext_entries _ _ (body_ctx Φx ++ Δ) /\ _ |- _ => destruct HX as [HXl _]
    | HX : ext_entries _ _ (body_ctx Φx ++ Δ) |- _ => rename HX into HXl
    end.
    match goal with
    | Hs : body_shape Φ Φ', Hsx : body_shape Φx Φx', Hnd : List.NoDup (gm_names Φ),
      Ho : forall k Ψ H, List.nth_error (body_opens Φ Φx) k = Some (Ψ, H) -> _ ⍮ _ ⍮ _ ⊢ᵐ H ≈ H |- _ =>
        destruct (body_shape_refl _ _ Hs) as (Hs1 & _ & _);
        destruct (body_shape_refl _ _ Hsx) as (Hsx1 & _ & _);
        rewrite gunit_lets_mk in *; cbn [moddef_lets] in *;
        eapply aunit_body; [ apply (ext_entries_alg n); [ exact (ext_entries_app_r _ _ _ _ HXl) | lia ] | assumption | | exact Hs1 | exact Hsx1 | exact Hnd ];
        eapply alg_body_of_entries; [ eassumption | exact HXl | lia | exact Hs1 |];
        intros k Ψ0 H0' Hk Hle; apply HmH; [ exact (Ho _ _ _ Hk) | lia ]
    end.
  - match goal with
    | HX : ext_entries _ _ (body_ctx Φx' ++ Δ') /\ _ |- _ => destruct HX as [HXr _]
    | HX : ext_entries _ _ (body_ctx Φx' ++ Δ') |- _ => rename HX into HXr
    end.
    match goal with
    | Hs : body_shape Φ Φ', Hsx : body_shape Φx Φx', Hnd : List.NoDup (gm_names Φ),
      Ho : forall k Ψ H, List.nth_error (body_opens Φ' Φx') k = Some (Ψ, H) -> _ ⍮ _ ⍮ _ ⊢ᵐ H ≈ H |- _ =>
        destruct (body_shape_refl _ _ Hs) as (_ & Hs2 & Hn);
        destruct (body_shape_refl _ _ Hsx) as (_ & Hsx2 & _);
        rewrite gunit_lets_mk in *; cbn [moddef_lets] in *;
        eapply aunit_body; [ apply (ext_entries_alg n); [ exact (ext_entries_app_r _ _ _ _ HXr) | lia ] | assumption | | exact Hs2 | exact Hsx2 | rewrite <- Hn; exact Hnd ];
        eapply alg_body_of_entries; [ eassumption | exact HXr | lia | exact Hs2 |];
        intros k Ψ1 H1' Hk Hle; apply HmH; [ exact (Ho _ _ _ Hk) | lia ]
    end.
  (** An alias: its target, by generation. *)
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [HXl _] end.
    rewrite gunit_lets_mk in *; cbn [moddef_lets] in *.
    econstructor; [ apply (ext_entries_alg n); [ exact HXl | lia ] | assumption | ].
    apply HmH; [ first [ eapply wf_modexp_eq_refl_left; eassumption | eassumption ] | lia ].
  - match goal with HX : ext_entries _ _ _ /\ ext_entries _ _ _ |- _ => destruct HX as [_ HXr] end.
    rewrite gunit_lets_mk in *; cbn [moddef_lets] in *.
    econstructor; [ apply (ext_entries_alg n); [ exact HXr | lia ] | assumption | ].
    apply HmH; [ first [ eapply wf_modexp_eq_refl_left; eassumption | eassumption ] | lia ].
  (** Flattening: the alias of the literal, and the unit over both
      telescopes. *)
  - destruct H0 as [HXl _]; rewrite gunit_lets_mk in *; cbn [moddef_lets] in *.
    apply aunit_alias; [ apply (ext_entries_alg n); [ exact HXl | lia ] | assumption | apply amod_lit, (proj1 H3) ].
  - destruct H0 as [HXl _]; rewrite gunit_lets_mk, ctx_lets_app in *.
    eapply alg_unit_flatten; [ apply (ext_entries_alg n); [ exact HXl | lia ] | assumption | exact (proj1 H3) ].
  - destruct H0; assumption.
  - destruct H0; assumption.
  - destruct H0 as [H01 _]; assumption.
  - destruct H2 as [_ H22]; assumption.
Qed.

Lemma alg_type_complete_lets : forall n,
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M ->
     exp_lets M <= n -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack ->
     ext_entries n Γ Ψ /\ ext_entries n Γ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack ->
     (gunit_lets U <= n -> Γ ⊢aᵘ U) /\ (gunit_lets U' <= n -> Γ ⊢aᵘ U')) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack ->
     (modexp_lets H <= n -> Γ ⊢aᵐ H) /\ (modexp_lets H' <= n -> Γ ⊢aᵐ H')).
Proof.
  intros n; destruct (alg_type_complete_lets_all n) as (H1 & H2 & H3 & H4 & _ & H5 & H6 & _).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 _)))))).
  (** A module expression and its other side, by generation. *)
  assert (Hm : forall Γ H, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> modexp_lets H <= n -> Γ ⊢aᵐ H).
  { intros Γ H HH Hl; eapply (alg_modexp_of_wf n); [| | exact HH | exact Hl ].
    - intros; eapply H2; [ eassumption | reflexivity | reflexivity | apply user_exp_all | assumption ].
    - intros * HU HlU; exact (proj1 (H6 _ _ _ _ _ HU eq_refl eq_refl) HlU). }
  intros * HH -> ->; split; intros Hl;
    [ exact (Hm _ _ (wf_modexp_eq_refl_left HH) Hl) | exact (Hm _ _ (wf_modexp_eq_refl_right HH) Hl) ].
Qed.

Lemma alg_type_complete_all :
  (forall Θ Ξ Γ, ⊢ Θ ⍮ Ξ ⍮ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aˣ Ψ /\ Γ ⊢aˣ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵘ U /\ Γ ⊢aᵘ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵐ H /\ Γ ⊢aᵐ H').
Proof.
  repeat split; intros; try exact I.
  - eapply (alg_type_complete_lets (exp_lets M)); eauto.
  - eapply (ext_entries_alg (ctx_lets Ψ + ctx_lets Ψ'));
      [ exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)) | lia ].
  - eapply (ext_entries_alg (ctx_lets Ψ + ctx_lets Ψ'));
      [ exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)) | lia ].
  - eapply (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (gunit_lets U + gunit_lets U'))))))) _ _ _ _ _ H H0 H1)); lia.
  - eapply (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (gunit_lets U + gunit_lets U'))))))) _ _ _ _ _ H H0 H1)); lia.
  - eapply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (modexp_lets H + modexp_lets H'))))))) _ _ _ _ _ H0 H1 H2)); lia.
  - eapply (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (modexp_lets H + modexp_lets H'))))))) _ _ _ _ _ H0 H1 H2)); lia.
Qed.

Lemma alg_type_check_complete : forall {Γ A M},
    user_exp M ->
    Γ ⊢ M : A ->
    Γ ⊢a M ⟸ A.
Proof.
  intros * Hue HM; exact (proj1 (proj2 alg_type_complete_all) _ _ _ _ _ HM eq_refl eq_refl Hue).
Qed.

Lemma alg_ext_complete : forall {Γ Ψ}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ -> Γ ⊢aˣ Ψ.
Proof. intros * HΨ; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 alg_type_complete_all)))) _ _ _ _ _ HΨ eq_refl eq_refl)). Qed.

Lemma alg_unit_complete : forall {Γ U}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U -> Γ ⊢aᵘ U.
Proof. intros * HU; exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_complete_all))))) _ _ _ _ _ HU eq_refl eq_refl)). Qed.

Lemma alg_modexp_complete : forall {Γ H}, gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H -> Γ ⊢aᵐ H.
Proof. intros * HH; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 alg_type_complete_all))))) _ _ _ _ _ HH eq_refl eq_refl)). Qed.



Hint Resolve alg_type_check_complete : mctt.

Corollary alg_type_infer_complete : forall {Γ A M},
    user_exp M ->
    Γ ⊢ M : A ->
    exists B, Γ ⊢a M ⟹ B /\ Γ ⊢a B ⊆ A.
Proof.
  intros.
  assert (Γ ⊢a M ⟸ A) as Hcheck by mauto 4 using alg_type_check_complete.
  inversion_clear Hcheck.
  firstorder.
Qed.

Hint Resolve alg_type_infer_complete : mctt.

(** The normal forms below a universe in the order on normal forms are the
    universes below it. *)
Lemma asnf_univ_inv : forall W u,
    ⊢anf W ⊆ univ_nf u ->
    exists v, W = univ_nf v /\ unf_le v u.
Proof.
  intros W [[d ys] | j] H; cbn in H; inversion H; subst;
    try match goal with Hn : not_univ_pi _ |- _ => inversion Hn end.
  all: match goal with
       | |- exists v, univⁿ ?c ?xs = _ /\ _ => exists (uns (c, xs))
       | |- exists v, Typeωⁿ@?i = _ /\ _ => exists (unl i)
       end; split; [ reflexivity | cbn; first [ assumption | exact I ] ].
Qed.

(** Completeness at a universe: a type of a universe term [T] infers a
    universe below the normal form of [T].  The bound is the normal form of
    [T] and not [T]'s universe index read off syntactically: the sorts the
    atoms of a universe normal form carry are those of their types only in a
    normal form ([soundness_lvl_ws]).  At [Typeω@i] this is
    [alg_type_infer_large_typ_complete], at [Type@n]
    [alg_type_infer_typ_complete_lit], at [Type⟨t⟩]
    [alg_type_infer_typ_complete_tm]. *)
Corollary alg_type_infer_typ_complete : forall {Γ T A},
    user_exp A ->
    univ_term T ->
    Γ ⊢ A : T ->
    exists u v, nbe_ty_f Γ T (univ_nf u) /\ Γ ⊢a A ⟹ univ_nf v /\ unf_le v u.
Proof.
  intros * HA HT HAT.
  pose proof (alg_type_check_complete HA HAT) as Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [A'' B' Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  destruct (nbe_ty_univ_term HT Hnbe2) as [u ->].
  destruct (asnf_univ_inv _ _ Hnfsub) as (v & -> & Hle).
  exists u, v; split; [ exact Hnbe2 | split; [ exact Hinfer | exact Hle ] ].
Qed.

Corollary alg_type_infer_large_typ_complete : forall {Γ i A},
    user_exp A ->
    Γ ⊢ A : Typeω@i ->
    exists UA u, Γ ⊢a A ⟹ UA /\ is_univ_nf UA u /\ unf_le u (unl i).
Proof.
  intros * HA HAi.
  destruct (alg_type_infer_typ_complete HA (univ_term_typ i) HAi) as (u & v & Hu & Hinf & Hle).
  apply nbe_ty_typ_univ_nf in Hu as ->.
  exists (univ_nf v), v; split; [ exact Hinf | split; [ apply is_univ_nf_univ_nf | exact Hle ] ].
Qed.

Hint Resolve alg_type_infer_large_typ_complete : mctt.

(** At a literal small universe, with the old precise shape: the inferred
    universe is a small universe at a literal level below [n] (an atom is
    never below a literal, [lvl_le_lit_closed]). *)
Corollary alg_type_infer_typ_complete_lit : forall {Γ n A},
    user_exp A ->
    Γ ⊢ A : Type@n ->
    exists m, Γ ⊢a A ⟹ Typeⁿ@m /\ m <= n.
Proof.
  intros * HA HAn.
  destruct (alg_type_infer_typ_complete HA (univ_term_suniv _) HAn) as (u & v & Hu & Hinf & Hle).
  apply nbe_ty_lit_univ_nf in Hu as ->.
  destruct v as [[c xs] | i]; cbn in Hle; [| contradiction].
  pose proof (lvl_le_lit_closed _ _ Hle) as Hxs; cbn in Hxs; subst xs.
  rewrite lvl_le_correct in Hle; specialize (Hle _ lvl_adm_zero); unfold lvl_ev, lvl_lit in Hle; cbn in Hle.
  destruct c as [a m]; assert (a = 0) as -> by ord.
  exists m; split; [ exact Hinf | ord ].
Qed.

(** At a level term [t]: the inferred universe is small, at a canonical
    level below the normal form of [t]. *)
Corollary alg_type_infer_typ_complete_tm : forall {Γ t A},
    user_exp A ->
    Γ ⊢ A : Type⟨t⟩ ->
    exists L L', Γ ⊢a A ⟹ nf_univ_of L /\ nbe_f Γ t Level (nf_lvl_of L') /\ lvl_le L L'.
Proof.
  intros * HA HAt.
  destruct (alg_type_infer_typ_complete HA (univ_term_suniv _) HAt) as (u & v & Hu & Hinf & Hle).
  destruct (nbe_ty_suniv_univ_nf Hu) as (L' & -> & HL').
  destruct v as [L | i]; cbn in Hle; [| contradiction].
  exists L, L'; split; [ exact Hinf | split; [ exact HL' | exact Hle ] ].
Qed.

End Fixed_GCtx.

#[export]
Hint Resolve alg_type_infer_normal : mctt.
#[export]
Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.
#[export]
Hint Resolve alg_type_check_pi_implies_alg_type_infer_pi : mctt.
#[export]
Hint Resolve alg_type_check_subtyp : mctt.
#[export]
Hint Resolve alg_type_check_conv : mctt.
#[export]
Hint Resolve alg_type_check_complete : mctt.
#[export]
Hint Resolve alg_type_infer_complete : mctt.
#[export]
Hint Resolve alg_type_infer_large_typ_complete : mctt.
