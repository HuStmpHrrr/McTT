(** * Annotated Normal Forms Equal up to Their Proofs Are Equal

    Two normal forms equal up to their proofs ([nf_eq_upto_proofs]) whose
    annotations ([nf_annotate_proofs]) are typed are equal at the type of
    the first ([nf_annotate_proofs_upto]).  Only the first is asked to be
    of the type: the second is typed somewhere, so each of its parts is,
    and the induction compares the parts at the first's types.  At a proof
    position both ascriptions prove a proposition, the two propositions
    are equal by induction, and the two proofs are equal by proof
    irrelevance.

    The induction needs one fact the syntax does not give: two equal
    domains of functions are types of one kind ([subtyp_same_kind]), so
    the bodies are typed in one context.  It is a consequence of
    completeness; the lemma is used by soundness ([soundness_upto_proofs]).

    A typed annotation is moreover equal to the plain normal form
    ([nf_ne_annotate_proofs_plain]): the same induction, one-sided, with
    an ascribed proof equal to its proof by irrelevance. *)

From Stdlib Require Import List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import CoreInversions ProofAnnotation.
From Mctt.Core.Syntactic.System.Records Require Import Typing.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Views UniformParams.
From Mctt.Core.Completeness.Consequences Require Import Types.
Import Syntax_Notations Wk_Notations.

(** [X'] is equal to [X] at every type of [X], when it is typed: the
    conclusion of the induction for one pair of terms. *)
Definition exp_upto (Θ : gdeps) (Ξ : gstack) (X X' : exp) : Prop :=
  forall Γ T, Θ ⍮ Ξ ⍮ Γ ⊢ X : T -> (exists T', Θ ⍮ Ξ ⍮ Γ ⊢ X' : T') -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ X' : T.

(** Two equal domains, the second typed at some sort, are types of one
    kind: the kind of the first's sort. *)
Lemma exp_eq_same_kind : forall Θ Ξ Γ A A' S S' κ κ',
    Θ ⍮ Ξ ⍮ Γ ⊢ A ≈ A' : S -> sort_kind S κ ->
    Θ ⍮ Ξ ⍮ Γ ⊢ A' : S' -> sort_kind S' κ' -> κ = κ'.
Proof.
  intros * HAA HS HA' HS'.
  destruct (sort_kind_abs_kind_sort_inv _ _ HS) as [i ->].
  destruct (sort_kind_abs_kind_sort_inv _ _ HS') as [j ->].
  pose proof (presup_exp_eq_left HAA) as HA.
  assert (Hs : Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A')
    by (eapply wf_subtyp_refl; [ exact (presup_exp_eq_right HAA) | exact (sort_kind_type_sort _ _ HS) | exact HAA ]).
  exact (@subtyp_same_kind (gc_mk Θ Ξ) Γ A A' κ κ' i j Hs HA HA').
Qed.

(** The codomain of a [Π] over a universe is of the sort of its kind
    next to a large universe. *)
Lemma pi_cod_sort_large : forall Θ Ξ Γ U κd A B κc, Θ ⍮ Ξ ⍮ Γ ⊢ᵤ U ->
    Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : (abs_kind_sort κc U)[↑]ʷ ->
    exists j, Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B : abs_kind_sort κc Typeω@j.
Proof.
  intros * HU HB; destruct κc; cbn [abs_kind_sort] in *; [| exists 0; exact HB | exists 0; exact HB ].
  assert (HU' : Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ᵤ U[↑]ʷ)
    by (eapply (proj1 (proj2 (proj2 (proj2 wk_preserves_wf)))); [ exact HU | apply wf_wk_shift; mauto 3 ]).
  exact (wf_exp_is_univ_large HU' HB).
Qed.

(** ** Functions *)

(** The bodies are compared in the first's context: the second domain is
    equal to the first, of the same kind, so the second body is typed
    there too. *)
Lemma exp_upto_fn : forall Θ Ξ A M A' M',
    exp_upto Θ Ξ A A' -> exp_upto Θ Ξ M M' -> exp_upto Θ Ξ (λ A M) (λ A' M').
Proof.
  intros * HA HM Γ T HT [T' HT'].
  destruct (wf_fn_inversion HT) as (κd & κc & B & HMt & Hsub).
  destruct (wf_fn_inversion HT') as (κd' & κc' & B' & HMt' & _).
  destruct (presup_subtyp_left_sorted Hsub) as (S0 & HS0 & HPi).
  destruct (wf_pi_inversion_at HPi) as [U HU HAt HBt Hk _].
  pose proof (presup_exp_ctx HMt') as HΓ'; inversion HΓ' as [| ? ? ? ? Srt' κ0 HA't HS' | | |]; subst.
  pose proof (HA _ _ HAt (ex_intro _ _ HA't)) as HAA.
  pose proof (presup_exp_eq_right HAA) as HA'U.
  destruct (pi_domain_eq_sort HU HAt HA'U HAA) as (S & HSk & HAS & HA'S & HAAS).
  pose proof (exp_eq_same_kind _ _ _ _ _ _ _ _ _ HAAS HSk HA't HS') as <-.
  assert (HMt'' : Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ M' : B')
    by (eapply ctxsub_exp; [ eapply wf_sub_id_extend_eq; [ exact HA'S | exact HAS | exact HSk | symmetry; exact HAAS ]
                          | exact HMt' ]).
  pose proof (HM _ _ HMt (ex_intro _ _ HMt'')) as HMM.
  destruct (pi_cod_sort_large _ _ _ _ _ _ _ _ HU HBt) as [j HBj].
  eapply wf_exp_eq_subtyp'; [| exact Hsub ].
  eapply wf_exp_eq_fn_cong; [ exact HAS | exact HSk | exact HAAS | exact HBj | exact Hk | exact HMM ].
Qed.

(** ** The Other Formers

    Each former: invert the first at [T], the second where it is typed,
    compare the parts at the first's types, and close by the congruence
    rule and the subtyping the inversion gives. *)

(** A term is equal to itself at each of its types. *)
Lemma exp_upto_refl : forall Θ Ξ X, exp_upto Θ Ξ X X.
Proof. intros * Γ T HT _; apply wf_exp_eq_refl; exact HT. Qed.

Lemma exp_upto_pi : forall Θ Ξ κd κc A B A' B',
    exp_upto Θ Ξ A A' -> exp_upto Θ Ξ B B' -> exp_upto Θ Ξ (a_pi κd κc A B) (a_pi κd κc A' B').
Proof.
  intros * HA HB Γ T HT [T' HT'].
  destruct (wf_pi_inversion_at HT) as [U HU HAt HBt Hk Hs].
  destruct (wf_pi_inversion_at HT') as [U' HU' HA't HB't _ _].
  pose proof (HA _ _ HAt (ex_intro _ _ HA't)) as HAA.
  pose proof (presup_exp_eq_right HAA) as HA'U.
  destruct (pi_domain_eq_sort HU HAt HA'U HAA) as (S & HSk & HAS & HA'S & HAAS).
  assert (HB't' : Θ ⍮ Ξ ⍮ Γ ▹{κd} A ⊢ B' : (abs_kind_sort κc U')[↑]ʷ)
    by (eapply ctxsub_exp; [ eapply wf_sub_id_extend_eq; [ exact HA'S | exact HAS | exact HSk | symmetry; exact HAAS ]
                          | exact HB't ]).
  pose proof (HB _ _ HBt (ex_intro _ _ HB't')) as HBB.
  pose proof (wf_exp_eq_pi_cong _ _ _ _ _ _ _ _ _ _ HU HAt HAA HBB Hk) as E.
  destruct Hs as [<- | Hs]; [ exact E | eapply wf_exp_eq_subtyp'; [ exact E | exact Hs ] ].
Qed.

Lemma exp_upto_and : forall Θ Ξ P Q P' Q',
    exp_upto Θ Ξ P P' -> exp_upto Θ Ξ Q Q' -> exp_upto Θ Ξ (Σₚ P Q) (Σₚ P' Q').
Proof.
  intros * HP HQ Γ T HT [T' HT'].
  destruct (wf_and_inversion _ _ _ _ _ _ HT) as [HPt HQt Hs].
  destruct (wf_and_inversion _ _ _ _ _ _ HT') as [HP't HQ't _].
  pose proof (HP _ _ HPt (ex_intro _ _ HP't)) as HPP.
  assert (HQ't' : Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊢ Q' : Propₘ)
    by (eapply ctxsub_exp; [ eapply wf_sub_id_extend_eq; [ exact HP't | exact HPt | constructor | symmetry; exact HPP ]
                          | exact HQ't ]).
  pose proof (HQ _ _ HQt (ex_intro _ _ HQ't')) as HQQ.
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_and_cong; [ exact HPt | exact HPP | exact HQQ ] | exact Hs ].
Qed.

Lemma exp_upto_app : forall Θ Ξ F N F' N',
    exp_upto Θ Ξ F F' -> exp_upto Θ Ξ N N' -> exp_upto Θ Ξ (F $ N) (F' $ N').
Proof.
  intros * HF HN Γ T HT [T' HT'].
  destruct (wf_app_inversion HT) as [κd κc D C HFt HNt Hs].
  destruct (wf_app_inversion HT') as [κd' κc' D' C' HF't HN't _].
  pose proof (HF _ _ HFt (ex_intro _ _ HF't)) as HFF.
  pose proof (HN _ _ HNt (ex_intro _ _ HN't)) as HNN.
  pose proof (presup_exp_typ_cases HFt) as Hc; inversion Hc as [? S HS HPi |]; subst.
  destruct (wf_pi_inversion_at HPi) as [U HU HDt HCt Hk _].
  destruct (pi_domain_sort_kind HU HDt) as (SD & HSD & HDS).
  destruct (pi_cod_sort_large _ _ _ _ _ _ _ _ HU HCt) as [j HCj].
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_app_cong; [ exact HDS | exact HSD | exact HCj | exact Hk | exact HFF | exact HNN ]
                            | exact Hs ].
Qed.

Lemma exp_upto_succl : forall Θ Ξ M M', exp_upto Θ Ξ M M' -> exp_upto Θ Ξ (succl M) (succl M').
Proof.
  intros * HM Γ T HT [T' HT'].
  destruct (wf_succl_inversion _ _ _ _ _ HT) as (n & HMt & Hs).
  destruct (wf_succl_inversion _ _ _ _ _ HT') as (n' & HM't & _).
  pose proof (HM _ _ HMt (ex_intro _ _ HM't)) as HMM.
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_succl_cong; exact HMM | exact Hs ].
Qed.

Lemma exp_upto_maxl : forall Θ Ξ M N M' N',
    exp_upto Θ Ξ M M' -> exp_upto Θ Ξ N N' -> exp_upto Θ Ξ (maxl M N) (maxl M' N').
Proof.
  intros * HM HN Γ T HT [T' HT'].
  destruct (wf_maxl_inversion _ _ _ _ _ _ HT) as (n & HMt & HNt & Hs).
  destruct (wf_maxl_inversion _ _ _ _ _ _ HT') as (n' & HM't & HN't & _).
  pose proof (HM _ _ HMt (ex_intro _ _ HM't)) as HMM.
  pose proof (HN _ _ HNt (ex_intro _ _ HN't)) as HNN.
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_maxl_cong; [ exact HMM | exact HNN ] | exact Hs ].
Qed.

(** Applications to arguments pairwise in the relation. *)
Lemma exp_upto_apps : forall Θ Ξ Ns Ns' H H',
    List.Forall2 (exp_upto Θ Ξ) Ns Ns' -> exp_upto Θ Ξ H H' -> exp_upto Θ Ξ (apps_exp H Ns) (apps_exp H' Ns').
Proof.
  intros * HNs; revert H H'; induction HNs as [| N N' Ns Ns' HN HNs IH]; intros H H' HH; cbn [apps_exp];
    [ exact HH | apply IH, exp_upto_app; assumption ].
Qed.

(** The levels a canonical level is built of: its atoms' successors and
    their maxima, atom by atom. *)
Lemma exp_upto_succl_n : forall Θ Ξ k M M', exp_upto Θ Ξ M M' -> exp_upto Θ Ξ (succl_n k M) (succl_n k M').
Proof. induction k as [| k IH]; intros * HM; cbn [succl_n]; [ exact HM | apply exp_upto_succl, IH, HM ]. Qed.

Lemma exp_upto_lvl_fold : forall Θ Ξ xs xs' H H',
    List.Forall2 (fun x x' => fst x = fst x' /\ exp_upto Θ Ξ (snd x) (snd x')) xs xs' ->
    exp_upto Θ Ξ H H' -> exp_upto Θ Ξ (lvl_fold H xs) (lvl_fold H' xs').
Proof.
  intros * Hxs; revert H H'; induction Hxs as [| [k a] [k' a'] xs xs' [Hk Ha] Hxs IH]; intros H H' HH;
    cbn [lvl_fold fst snd] in *; [ exact HH | subst k' ].
  apply IH, exp_upto_maxl; [ exact HH | apply exp_upto_succl_n; exact Ha ].
Qed.

Lemma exp_upto_lvl_exp_of : forall Θ Ξ c xs xs',
    List.Forall2 (fun x x' => fst x = fst x' /\ exp_upto Θ Ξ (snd x) (snd x')) xs xs' ->
    exp_upto Θ Ξ (lvl_exp_of c xs) (lvl_exp_of c xs').
Proof.
  intros * Hxs; destruct Hxs as [| [k a] [k' a'] xs xs' [Hk Ha] Hxs]; cbn [fst snd] in *; [ apply exp_upto_refl | subst k' ].
  unfold lvl_exp_of; destruct c as [[| c1] [| c2]];
    apply exp_upto_lvl_fold; try exact Hxs;
    first [ apply exp_upto_succl_n; exact Ha | apply exp_upto_maxl; [ apply exp_upto_refl | apply exp_upto_succl_n; exact Ha ] ].
Qed.

(** Ex falso: the returned types equal, the proofs of [⊥] by proof
    irrelevance. *)
Lemma wf_absurd_inversion_closed : forall Θ Ξ Γ M C A,
    Θ ⍮ Ξ ⍮ Γ ⊢ efq M return C : A ->
    exists S, type_sort S /\ level_closed_sort Propₘ S /\ Θ ⍮ Ξ ⍮ Γ ⊢ C : S /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : ⊥ /\ Θ ⍮ Ξ ⍮ Γ ⊢ C ⊆ A.
Proof.
  intros * H; dependent induction H.
  - exists Srt; repeat split; try assumption; eapply wf_subtyp_refl_typ; eassumption.
  - destruct (IHwf_exp1 _ _ eq_refl) as (S & HS & Hc & HC & HM & Hs).
    exists S; repeat split; try assumption; eapply wf_subtyp_trans; eassumption.
Qed.

Lemma exp_upto_absurd : forall Θ Ξ C M C' M',
    exp_upto Θ Ξ C C' -> exp_upto Θ Ξ (efq M return C) (efq M' return C').
Proof.
  intros * HC Γ T HT [T' HT'].
  destruct (wf_absurd_inversion_closed _ _ _ _ _ _ HT) as (S & HS & Hc & HCt & HMt & Hs).
  destruct (wf_absurd_inversion_closed _ _ _ _ _ _ HT') as (S' & _ & _ & HC't & HM't & _).
  pose proof (HC _ _ HCt (ex_intro _ _ HC't)) as HCC.
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_absurd_cong; eassumption | exact Hs ].
Qed.

(** ** Proofs *)

(** An ascribed proof is of its proposition. *)
Lemma proof_ascription_typed : forall Θ Ξ Γ P M,
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ -> Θ ⍮ Ξ ⍮ Γ ⊢ M : P -> Θ ⍮ Ξ ⍮ Γ ⊢ proof_ascription P M : P.
Proof.
  intros * HP HM; unfold proof_ascription.
  assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
  assert (HT : Θ ⍮ Ξ ⍮ Γ ▹{ak_propositional} P ⊢ a_True : Propₘ) by (apply wf_True; mauto 3).
  assert (HN : Θ ⍮ Ξ ⍮ Γ ⊢ a_left (a_conj P a_True M a_tt) : P).
  { eapply wf_left; [ exact HP | exact HT |].
    eapply wf_conj; [ exact HP | exact HT | exact HM | cbn; apply wf_tt; exact HΓ ]. }
  assert (HΓN : ⊢ Θ ⍮ Ξ ⍮ Γ ▸ P ≔ a_left (a_conj P a_True M a_tt))
    by (eapply wf_ctx_extend_def; [ exact HP | constructor | exact HN ]).
  assert (HPw : Θ ⍮ Ξ ⍮ Γ ▸ P ≔ a_left (a_conj P a_True M a_tt) ⊢ P[↑]ʷ : Propₘ)
    by (change Propₘ with (Propₘ[↑]ʷ); eapply (proj1 wk_preserves_wf); [ exact HP | apply wf_wk_shift; exact HΓN ]).
  assert (H : Θ ⍮ Ξ ⍮ Γ ⊢ a_let (b_def P (a_left (a_conj P a_True M a_tt))) (a_var 0)
                         : P[↑]ʷ[Id,,a_left (a_conj P a_True M a_tt)]).
  { eapply wf_let; [ exact HP | constructor | exact HN | exact HPw | constructor |].
    apply wf_vlookup; [ exact HΓN | constructor ]. }
  rewrite exp_sub_shift_extend, exp_sub_id in H; exact H.
Qed.

(** An ascribed proof's proposition is a proposition, its proof a proof
    of it, and its type that proposition or above it. *)
Lemma proof_ascription_inversion : forall Θ Ξ Γ P M T,
    Θ ⍮ Ξ ⍮ Γ ⊢ proof_ascription P M : T ->
    Θ ⍮ Ξ ⍮ Γ ⊢ P : Propₘ /\ Θ ⍮ Ξ ⍮ Γ ⊢ M : P /\ Θ ⍮ Ξ ⍮ Γ ⊢ P ⊆ T.
Proof.
  intros * HT; unfold proof_ascription in HT.
  destruct (wf_let_ann_inversion HT) as [S Y HS HPS HN HB Hs].
  destruct (wf_left_inversion _ _ _ _ _ HN) as [L R HL HR Harg _].
  destruct (wf_conj_inversion _ _ _ _ _ _ _ _ Harg) as [HPp _ HMt _ _].
  split; [ exact HPp | split; [ exact HMt |] ].
  destruct (wf_vlookup_inversion HB) as (A' & Hl & HA's); inversion Hl; subst.
  pose proof (wf_sub_single_def _ _ _ _ _ _ HPS HS HN) as Hσ.
  pose proof (sub_preserves_subtyp _ _ _ _ _ _ _ HA's Hσ) as Hs'.
  rewrite exp_sub_shift_extend, exp_sub_id in Hs'.
  eapply wf_subtyp_trans; [ exact Hs' | exact Hs ].
Qed.

(** Two ascribed proofs of equal propositions are equal, by proof
    irrelevance, whatever the proofs. *)
Lemma exp_upto_proof : forall Θ Ξ P M P' M',
    exp_upto Θ Ξ P P' -> exp_upto Θ Ξ (proof_ascription P M) (proof_ascription P' M').
Proof.
  intros * HP Γ T HT [T' HT'].
  destruct (proof_ascription_inversion _ _ _ _ _ _ HT) as (HPt & HMt & Hs).
  destruct (proof_ascription_inversion _ _ _ _ _ _ HT') as (HP't & HM't & _).
  pose proof (HP _ _ HPt (ex_intro _ _ HP't)) as HPP.
  pose proof (proof_ascription_typed _ _ _ _ _ HPt HMt) as H1.
  pose proof (proof_ascription_typed _ _ _ _ _ HP't HM't) as H2.
  assert (H2' : Θ ⍮ Ξ ⍮ Γ ⊢ proof_ascription P' M' : P)
    by (eapply wf_conv_sort; [ exact H2 | exact HPt | constructor | symmetry; exact HPP ]).
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_irrelevant; [ exact HPt | exact H1 | exact H2' ] | exact Hs ].
Qed.

Lemma exp_upto_univ : forall Θ Ξ M M', exp_upto Θ Ξ M M' -> exp_upto Θ Ξ (Type⟨M⟩) (Type⟨M'⟩).
Proof.
  intros * HM Γ T HT [T' HT'].
  pose proof (wf_univ_inversion HT) as Hs.
  destruct (wf_univ_lvl_inversion HT) as [n HMt].
  destruct (wf_univ_lvl_inversion HT') as [n' HM't].
  pose proof (HM _ _ HMt (ex_intro _ _ HM't)) as HMM.
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_univ_cong; exact HMM | exact Hs ].
Qed.

(** Two related lists are related at each position they both have. *)
Lemma Forall2_nth_both : forall {A B : Type} (R : A -> B -> Prop) l l', List.Forall2 R l l' ->
    forall k x y, List.nth_error l k = Some x -> List.nth_error l' k = Some y -> R x y.
Proof.
  intros * H; induction H as [| x0 y0 l l' Hxy H IH]; intros [| k] x y Hx Hy; cbn in *; try discriminate;
    [ injection Hx as <-; injection Hy as <-; exact Hxy | exact (IH _ _ _ Hx Hy) ].
Qed.

(** ** Records *)

Lemma exp_upto_proj : forall Θ Ξ f M M', exp_upto Θ Ξ M M' -> exp_upto Θ Ξ (a_proj f M) (a_proj f M').
Proof.
  intros * HM Γ T HT [T' HT'].
  destruct (wf_proj_inversion HT) as [p R Ns k U S HMt Hr Hl Hn HNs Hfk HUt HS Hs].
  destruct (wf_proj_inversion HT') as [p' R' Ns' k' U' S' HM't _ _ _ _ _ _ _ _].
  pose proof (HM _ _ HMt (ex_intro _ _ HM't)) as HMM.
  destruct (record_sort_large _ _ _ _ _ _ Hr Hl Hn HNs) as [n HSn].
  destruct (record_proj_cong_at _ _ _ _ _ _ _ _ _ _ _ _ HMM Hr Hl Hn HNs HSn Hfk) as [_ E].
  eapply wf_exp_eq_subtyp'; [ exact E | exact Hs ].
Qed.

Lemma exp_upto_tuple : forall Θ Ξ T T' fs fs',
    exp_upto Θ Ξ T T' -> List.map fst fs = List.map fst fs' ->
    List.Forall2 (fun x x' => exp_upto Θ Ξ (snd x) (snd x')) fs fs' ->
    exp_upto Θ Ξ (a_tuple T fs) (a_tuple T' fs').
Proof.
  intros * HT0 Hnames HF Γ A HA [A' HA'].
  destruct (wf_tuple_inversion HA) as [p R Ns i HTt HTe Hr Hl Hn HNs Hfs HMs Hsub].
  destruct (wf_tuple_inversion HA') as [p' R' Ns' i' HT't HT'e Hr' Hl' Hn' HNs' Hfs' HMs' _].
  pose proof (HT0 _ _ HTt (ex_intro _ _ HT't)) as HTT.
  (** Each tuple at its own annotation *)
  assert (H1 : Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T) by (eapply wf_tuple; eassumption).
  assert (H2 : Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T' fs' : T') by (eapply wf_tuple; eassumption).
  assert (H2' : Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T' fs' : T) by (eapply wf_conv; [ exact H2 | exact HTt | symmetry; exact HTT ]).
  eapply wf_exp_eq_subtyp'; [| exact Hsub ].
  eapply wf_exp_eq_tuple_cong; [ exact H1 | exact HTT | exact HTe | exact Hl | exact Hn | exact HNs | exact Hfs
                               | symmetry; exact Hnames | | exact H2' ].
  (** The fields, position by position *)
  intros k f M M' U Hk Hk' HU.
  pose proof (Forall2_nth_both _ _ _ HF _ _ _ Hk Hk') as HMM; cbn [snd] in HMM.
  assert (HU' : exists U', List.nth_error (record_fields R') k = Some (f, U')).
  { assert (E : List.nth_error (List.map fst (record_fields R')) k = Some f)
      by (rewrite <- Hfs', List.nth_error_map, Hk'; reflexivity).
    rewrite List.nth_error_map in E; destruct (List.nth_error (record_fields R') k) as [[f0 U0] |]; cbn in E; [| discriminate ].
    injection E as ->; eexists; reflexivity. }
  destruct HU' as [U' HU'].
  exact (HMM _ _ (HMs _ _ _ _ Hk HU) (ex_intro _ _ (HMs' _ _ _ _ Hk' HU'))).
Qed.

(** ** Stuck Eliminators *)

Lemma exp_upto_elim : forall Θ Ξ p Us Us' m Bks Bks' M M',
    List.Forall2 (exp_upto Θ Ξ) Us Us' ->
    List.Forall2 (fun b b' => eb_binder_count b = eb_binder_count b' /\
                   exp_upto Θ Ξ (eb_scrutinee_type b) (eb_scrutinee_type b') /\
                   exp_upto Θ Ξ (eb_motive b) (eb_motive b') /\
                   List.Forall2 (fun br br' => fst br = fst br' /\ exp_upto Θ Ξ (snd br) (snd br')) (eb_brs b) (eb_brs b'))
      Bks Bks' ->
    exp_upto Θ Ξ M M' ->
    exp_upto Θ Ξ (a_elim ak_relevant p Us m Bks M) (a_elim ak_relevant p Us' m Bks' M').
Proof.
  intros * HUs HBks HM Γ T HT [T' HT'].
  destruct (wf_elim_inversion HT) as [D Mm bm Ps i Hl Hm Hbm HPl HPs HMt HUe HBt Hs].
  destruct (wf_elim_inversion HT') as [D' Mm' bm' Ps' i' Hl' Hm' Hbm' HPl' HPs' HM't HUe' HBt' _].
  rewrite Hl in Hl'; injection Hl' as <-; rewrite Hm in Hm'; injection Hm' as <-.
  subst Us Us'.
  pose proof (presup_exp_ctx HMt) as HΓ.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (HM _ _ HMt (ex_intro _ _ HM't)) as HMM.
  (** The right parameters: the second's uniform ones, the first's
      non-uniform ones, which the second's scrutinee is not compared at *)
  assert (Hnu : ind_nu D <= im_np D Mm) by (unfold im_np; lia).
  set (Ps'' := List.firstn (ind_nu D) Ps' ++ List.skipn (ind_nu D) Ps).
  assert (Hfst' : List.length (List.firstn (ind_nu D) Ps') = ind_nu D) by (rewrite List.length_firstn; lia).
  assert (HPl'' : List.length Ps'' = im_np D Mm) by (unfold Ps''; rewrite List.length_app, Hfst', List.length_skipn; lia).
  assert (HU'' : List.firstn (ind_nu D) Ps'' = List.firstn (ind_nu D) Ps')
    by (unfold Ps''; rewrite List.firstn_app, Hfst', PeanoNat.Nat.sub_diag, List.firstn_O, List.app_nil_r,
          List.firstn_firstn, PeanoNat.Nat.min_id; reflexivity).
  assert (Hass : all_assumptions (im_params D Mm)) by (eapply decl_closed_params_ass; eassumption).
  assert (HPP : forall k P P'' T0, nth_error Ps k = Some P -> nth_error Ps'' k = Some P'' ->
             nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T0 -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P'' : T0).
  { intros k P P'' T0 HP HP'' HT0.
    destruct (PeanoNat.Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
    - unfold Ps'' in HP''; rewrite List.nth_error_app1 in HP'' by lia.
      assert (HP1 : nth_error (List.firstn (ind_nu D) Ps) k = Some P)
        by (rewrite List.nth_error_firstn; destruct (PeanoNat.Nat.ltb_spec k (ind_nu D)); [ exact HP | lia ]).
      pose proof (Forall2_nth_both _ _ _ HUs _ _ _ HP1 HP'') as HE.
      rewrite List.nth_error_firstn in HP''; destruct (PeanoNat.Nat.ltb_spec k (ind_nu D)); [| lia ].
      assert (Hk' : k < List.length (tele_insts (im_params D Mm) Id Ps'))
        by (rewrite (length_tele_insts_params _ _ _ _ Hass HPl'); apply List.nth_error_Some; congruence).
      destruct (nth_error (tele_insts (im_params D Mm) Id Ps') k) as [T1 |] eqn:HT1; [| apply List.nth_error_None in HT1; lia ].
      exact (HE _ _ (HPs _ _ _ HP HT0) (ex_intro _ _ (HPs' _ _ _ HP'' HT1))).
    - unfold Ps'' in HP''; rewrite List.nth_error_app2 in HP'' by lia; rewrite Hfst', List.nth_error_skipn in HP''.
      replace (ind_nu D + (k - ind_nu D)) with k in HP'' by lia; rewrite HP in HP''; injection HP'' as <-.
      apply wf_exp_eq_refl; exact (HPs _ _ _ HP HT0). }
  (** The uniform parameters, both ways *)
  destruct (params_eq_split (Θ := Θ) (Ξ := Ξ) _ _ _ _ _ _ Hc Hm HPl HPl'' HPP) as [HUU _].
  rewrite HU'' in HUU.
  assert (HPsr : forall j P P' T0, nth_error Ps j = Some P -> nth_error Ps j = Some P' ->
             nth_error (tele_insts (im_params D Mm) Id Ps) j = Some T0 -> Θ ⍮ Ξ ⍮ Γ ⊢ P' : T0)
    by (intros j P P0 T0 HP HP0 HT0; rewrite HP in HP0; injection HP0 as <-; exact (HPs _ _ _ HP HT0)).
  destruct (params_typed_at_split (Θ := Θ) (Ξ := Ξ) _ _ _ _ _ _ Hc Hm HPl HPl HPsr) as [HUt _].
  assert (HPsr' : forall j P P' T0, nth_error Ps' j = Some P -> nth_error Ps' j = Some P' ->
             nth_error (tele_insts (im_params D Mm) Id Ps') j = Some T0 -> Θ ⍮ Ξ ⍮ Γ ⊢ P' : T0)
    by (intros j P P0 T0 HP HP0 HT0; rewrite HP in HP0; injection HP0 as <-; exact (HPs' _ _ _ HP HT0)).
  destruct (params_typed_at_split (Θ := Θ) (Ξ := Ξ) _ _ _ _ _ _ Hc Hm HPl' HPl' HPsr') as [HUt' _].
  set (Us := List.firstn (ind_nu D) Ps) in *; set (Us' := List.firstn (ind_nu D) Ps') in *.
  assert (HUl : List.length Us = ind_nu D) by (unfold Us; rewrite List.length_firstn; lia).
  assert (HUt0 : forall j U T0, nth_error Us j = Some U -> nth_error (tele_insts (ind_uparams D) Id Us) j = Some T0 ->
             Θ ⍮ Ξ ⍮ Γ ⊢ U : T0)
    by (intros; eapply HUt; eassumption).
  assert (HUt0' : forall j U T0, nth_error Us' j = Some U -> nth_error (tele_insts (ind_uparams D) Id Us') j = Some T0 ->
             Θ ⍮ Ξ ⍮ Γ ⊢ U : T0)
    by (intros; eapply HUt'; eassumption).
  assert (Hσσ : Θ ⍮ Ξ ⍮ Γ ⊢ˢ sb_of_list Id Us ≈ sb_of_list Id Us' : ind_uparams D ++ Γ).
  { eapply wf_sub_eq_of_list_conv; [ exact (decl_closed_ass _ Hc) | exact (wf_uparams_app _ _ _ HD Hc _ HΓ)
                                   | apply wf_sub_eq_refl, wf_sub_id, HΓ | exact HUl | exact Hfst' | exact HUt0 | exact HUt0'
                                   | exact HUU ]. }
  assert (HUU' : forall j U' U T0, nth_error Us' j = Some U' -> nth_error Us j = Some U ->
             nth_error (tele_insts (ind_uparams D) Id Us') j = Some T0 -> Θ ⍮ Ξ ⍮ Γ ⊢ U' ≈ U : T0)
    by (intros j U' U T0 HU' HU HT0;
        exact (wf_sub_eq_of_list_inv _ _ _ _ _ _ _ (decl_closed_ass _ Hc) Hfst' HUl (wf_sub_eq_sym _ _ _ _ _ _ Hσσ)
                 _ _ _ _ HU' HU HT0)).
  (** The second's blocks at the first's uniform parameters *)
  pose proof (blocks_typed_us_conv (Θ := Θ) (Ξ := Ξ) _ _ _ _ _ _ _ _ Hl HΓ Hfst' HUt0' HUl HUt0 HUU' HBt') as HBt''.
  pose proof (ctx_wf_gctx _ _ _ HΓ) as Hg.
  pose proof (decls_of_ctx _ _ _ HΓ) as HDs.
  pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD)) as Hsf.
  pose proof (wf_sub_uparams _ _ _ HD Hc _ _ HΓ HUl HUt0) as Hσ.
  pose proof (blocks_mctx_wf _ _ _ _ _ _ _ _ _ HBt) as HMc.
  (** The motives, block by block *)
  assert (HAA : forall k Mk b b', ind_member D k = Some Mk -> nth_error Bks k = Some b -> nth_error Bks' k = Some b' ->
             Θ ⍮ Ξ ⍮ elim_mctx p D k Mk Us ++ Γ ⊢ eb_motive b ≈ eb_motive b' : abs_kind_sort ak_relevant Typeω@i).
  { intros k Mk b b' Hk Hb Hb'.
    destruct (Forall2_nth_both _ _ _ HBks _ _ _ Hb Hb') as (_ & _ & HA & _).
    exact (HA _ _ (blocks_typed_motive _ _ _ _ _ _ _ _ _ HBt _ _ _ Hk Hb)
              (ex_intro _ _ (blocks_typed_motive _ _ _ _ _ _ _ _ _ HBt'' _ _ _ Hk Hb'))). }
  pose proof (blocks_motives_typed _ _ _ _ _ _ _ _ _ Hsf HBt) as HAt.
  assert (HAeq : motives_eq Θ Ξ Γ p D Us (blocks_motives Bks) (blocks_motives Bks') ak_relevant i).
  { intros j Mj Hj Hr.
    destruct (blocks_nth _ _ _ _ Hsf (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt) Hj Hr) as [b Hb].
    destruct (blocks_nth _ _ _ _ Hsf (blocks_typed_len _ _ _ _ _ _ _ _ _ HBt'') Hj Hr) as [b' Hb'].
    rewrite (blocks_motives_nth _ _ _ Hb), (blocks_motives_nth _ _ _ Hb'); exact (HAA _ _ _ _ Hj Hb Hb'). }
  assert (HAt' : motives_typed Θ Ξ Γ p D Us (blocks_motives Bks') ak_relevant i)
    by (intros j Mj Hj Hr; exact (presup_exp_eq_right (HAeq _ _ Hj Hr))).
  (** The congruence rule, at the first's parameters and the mixed ones *)
  eapply wf_exp_eq_subtyp'; [| exact Hs ].
  destruct HBt as [HlB Hnm HZ HAb HΨ Hn HΨB Hk HB Hmk].
  destruct HBt'' as [HlB2 Hnm2 HZ2 HAb2 HΨ2 Hn2 HΨB2 Hk2 HB2 Hmk2].
  eapply wf_exp_eq_elim_cong with (Ps := Ps) (Ps' := Ps''); try eassumption; try (symmetry; exact HU''); try reflexivity.
  all: try (intros k Mk b Hk' Hb; exact (Hnm _ _ _ Hk' Hb)).
  all: try (intros k Mk b Hk' Hb; exact (Hnm2 _ _ _ Hk' Hb)).
  all: try (intros k Mk b b' Hk' Hb Hb'; exact (HAA _ _ _ _ Hk' Hb Hb')).
  all: try (intros k b b' Hb Hb'; destruct (Forall2_nth_both _ _ _ HBks _ _ _ Hb Hb') as (_ & _ & _ & Hbr);
            clear - Hbr; induction Hbr as [| x y l l' [Hxy _] _ IH]; cbn; [ reflexivity | rewrite Hxy, IH; reflexivity ]).
  (** The branches, at the first's motives: the second's context is equal *)
  clear HT HT' HMt HM't HMM HPP HUU HPsr HUt HPsr' HUt' HUt0' HUU' HBt' HPs HPs' Hs.
  intros k Mk b b' i0 c gs n B B' Hk' Hb Hb' HB0 HB0' Hcon.
  pose proof (HB _ _ _ _ _ _ _ Hk' Hb Hcon (List.nth_error_In _ _ HB0)) as HBt0.
  pose proof (HB2 _ _ _ _ _ _ _ Hk' Hb' Hcon (List.nth_error_In _ _ HB0')) as HB't0.
  pose proof (elim_bctx_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg HDs Hl Hk' HΓ HUl Hσ HMc HAt HAt' HAeq Hmk Hcon) as Hbeq.
  pose proof (ctxsub_ext_rev _ _ _ _ _ Hbeq (elim_bctx_ass _ _ _ _ _ _ _ _ Hc Hk')) as HId.
  pose proof (ctxsub_exp _ _ _ _ _ _ HId HB't0) as HB't1.
  destruct (Forall2_nth_both _ _ _ HBks _ _ _ Hb Hb') as (_ & _ & _ & Hbr).
  pose proof (Forall2_nth_both _ _ _ Hbr _ _ _ HB0 HB0') as [_ HBB]; cbn [snd] in HBB.
  exact (HBB _ _ HBt0 (ex_intro _ _ HB't1)).
Qed.

(** ** The Induction *)

(** Lists related elementwise by a comparison that, at each element the
    induction covers, implies a relation, are related by it. *)
Lemma list_eqb_Forall2_all : forall {A : Set} (Q : A -> Type) (f : A -> A -> bool) (R : A -> A -> Prop) l,
    Base.list_all A Q l -> (forall x, Q x -> forall y, f x y = true -> R x y) ->
    forall l', list_eqb f l l' = true -> List.Forall2 R l l'.
Proof.
  intros * Hl Hf; induction Hl as [| x Hx l Hl IH]; intros [| y l'] H; cbn in *; try discriminate; [ constructor |].
  apply Bool.andb_true_iff in H as [H H']; constructor; [ exact (Hf _ Hx _ H) | exact (IH _ H') ].
Qed.

(** Lists related elementwise, mapped. *)
Lemma Forall2_map_both : forall {A B : Type} (R : B -> B -> Prop) (g : A -> B) l l',
    List.Forall2 (fun x y => R (g x) (g y)) l l' -> List.Forall2 R (List.map g l) (List.map g l').
Proof. intros * H; induction H; constructor; assumption. Qed.

Theorem nf_ne_annotate_proofs_upto :
  (forall W, forall Θ Ξ W', nf_eqb_upto_proofs W W' = true ->
      exp_upto Θ Ξ (nf_annotate_proofs W) (nf_annotate_proofs W')) /\
  (forall M, forall Θ Ξ M', ne_eqb_upto_proofs M M' = true ->
      exp_upto Θ Ξ (ne_annotate_proofs M) (ne_annotate_proofs M')).
Proof.
  apply nf_ne_ind; intros;
    lazymatch goal with
    | H : nf_eqb_upto_proofs _ ?W = true |- _ => destruct W
    | H : ne_eqb_upto_proofs _ ?M = true |- _ => destruct M
    end;
    cbn [nf_eqb_upto_proofs ne_eqb_upto_proofs] in *; try discriminate; eqb_split; eqb_leaves; subst;
    cbn [nf_annotate_proofs ne_annotate_proofs nf_to_exp ne_to_exp].
  all: try apply exp_upto_refl.
  (** The formers of one or two parts *)
  all: try solve [ first [ apply exp_upto_and | apply exp_upto_pi | apply exp_upto_fn | apply exp_upto_app | apply exp_upto_proof
                         | apply exp_upto_absurd | apply exp_upto_proj ]; eauto ].
  all: try solve [ eauto ].
  (** Type formers and constructors at their arguments *)
  all: try (apply exp_upto_apps; [| apply exp_upto_refl ]; rewrite !List.map_map; apply Forall2_map_both;
            eapply list_eqb_Forall2_all; [ eassumption | | eassumption ]; cbn; intros x Hx y Hxy; exact (Hx _ _ _ Hxy)).
  (** Levels and small universes, atom by atom *)
  all: try (try apply exp_upto_univ; apply exp_upto_lvl_exp_of; rewrite !List.map_map; apply Forall2_map_both;
            eapply list_eqb_Forall2_all; [ eassumption | | eassumption ]; cbn; intros x Hx y Hxy; destruct Hx; cbn in *;
            eqb_split; eqb_leaves; split; [ assumption | eauto ]).
  - (** A tuple: its type's parameters, its names, its fields *)
    apply exp_upto_tuple.
    + apply exp_upto_apps; [| apply exp_upto_refl ]; rewrite !List.map_map; apply Forall2_map_both.
      eapply list_eqb_Forall2_all; [ eassumption | | eassumption ]; cbn; intros x Hx y Hxy; exact (Hx _ _ _ Hxy).
    + pose proof (list_eqb_length _ _ _ H2) as Hlen.
      rewrite !List.map_map; clear - Hlen; revert l1 l4 Hlen; induction l3 as [| f l3 IH]; intros [| x l1] [| y l4] Hlen;
        cbn in *; try discriminate; try reflexivity; f_equal; apply IH; congruence.
    + assert (HF : List.Forall2 (exp_upto Θ Ξ) (map nf_to_exp (map nf_annotate_proofs l1))
                     (map nf_to_exp (map nf_annotate_proofs l4)))
        by (rewrite !List.map_map; apply Forall2_map_both;
            eapply list_eqb_Forall2_all; [ eassumption | | eassumption ]; cbn; intros x Hx y Hxy; exact (Hx _ _ _ Hxy)).
      clear - HF; revert l3; induction HF as [| x y X Y Hxy HF IH]; intros [| f l3]; cbn; constructor; [ exact Hxy | apply IH ].
  - (** A stuck eliminator: its uniform parameters, its blocks, its scrutinee *)
    apply exp_upto_elim.
    + rewrite !List.map_map; apply Forall2_map_both.
      eapply list_eqb_Forall2_all; [ eassumption | | eassumption ]; cbn; intros x Hx y Hxy; exact (Hx _ _ _ Hxy).
    + rewrite !List.map_map; apply Forall2_map_both.
      eapply list_eqb_Forall2_all; [ eassumption | | eassumption ]; cbn; intros x Hx y Hxy.
      destruct Hx as [n' Z HZ A' HA brs Hbrs]; cbn in *; eqb_split; eqb_leaves.
      split; [ congruence | split; [ eauto | split; [ eauto |] ] ].
      rewrite !List.map_map; apply Forall2_map_both.
      eapply list_eqb_Forall2_all; [ exact Hbrs | | eassumption ]; cbn; intros br Hbr br' Hbr'.
      destruct Hbr; cbn in *; eqb_split; eqb_leaves; split; [ congruence | eauto ].
    + eauto.
Qed.

Corollary nf_annotate_proofs_upto : forall Θ Ξ Γ T W W',
    Θ ⍮ Ξ ⍮ Γ ⊢ nf_annotate_proofs W : T ->
    (exists T', Θ ⍮ Ξ ⍮ Γ ⊢ nf_annotate_proofs W' : T') ->
    nf_eq_upto_proofs W W' ->
    Θ ⍮ Ξ ⍮ Γ ⊢ nf_annotate_proofs W ≈ nf_annotate_proofs W' : T.
Proof. intros * HW HW' E; exact (proj1 nf_ne_annotate_proofs_upto _ _ _ _ E _ _ HW HW'). Qed.

(** ** The Plain Normal Form

    A typed annotation is equal to the plain normal form.  The comparison
    is one-sided: only the annotation is typed, and each part of the plain
    form is typed because it is equal to the annotation's part.  An
    ascribed proof [proof_ascription P M] is the proof [M], which the
    ascription types, by irrelevance; the formers are congruences. *)

(** [X'] is equal to [X] at every type of [X]. *)
Definition exp_plain (Θ : gdeps) (Ξ : gstack) (X X' : exp) : Prop :=
  forall Γ T, Θ ⍮ Ξ ⍮ Γ ⊢ X : T -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ X' : T.

Lemma exp_plain_refl : forall Θ Ξ X, exp_plain Θ Ξ X X.
Proof. intros * Γ T HT; apply wf_exp_eq_refl; exact HT. Qed.

Lemma exp_plain_fn : forall Θ Ξ A M A' M',
    exp_plain Θ Ξ A A' -> exp_plain Θ Ξ M M' -> exp_plain Θ Ξ (λ A M) (λ A' M').
Proof.
  intros * HA HM Γ T HT.
  destruct (wf_fn_inversion HT) as (κd & κc & B & HMt & Hsub).
  destruct (presup_subtyp_left_sorted Hsub) as (S0 & HS0 & HPi).
  destruct (wf_pi_inversion_at HPi) as [U HU HAt HBt Hk _].
  pose proof (HA _ _ HAt) as HAA.
  destruct (pi_domain_eq_sort HU HAt (presup_exp_eq_right HAA) HAA) as (S & HSk & HAS & HA'S & HAAS).
  pose proof (HM _ _ HMt) as HMM.
  destruct (pi_cod_sort_large _ _ _ _ _ _ _ _ HU HBt) as [j HBj].
  eapply wf_exp_eq_subtyp'; [| exact Hsub ].
  eapply wf_exp_eq_fn_cong; [ exact HAS | exact HSk | exact HAAS | exact HBj | exact Hk | exact HMM ].
Qed.

Lemma exp_plain_pi : forall Θ Ξ κd κc A B A' B',
    exp_plain Θ Ξ A A' -> exp_plain Θ Ξ B B' -> exp_plain Θ Ξ (a_pi κd κc A B) (a_pi κd κc A' B').
Proof.
  intros * HA HB Γ T HT.
  destruct (wf_pi_inversion_at HT) as [U HU HAt HBt Hk Hs].
  pose proof (wf_exp_eq_pi_cong _ _ _ _ _ _ _ _ _ _ HU HAt (HA _ _ HAt) (HB _ _ HBt) Hk) as E.
  destruct Hs as [<- | Hs]; [ exact E | eapply wf_exp_eq_subtyp'; [ exact E | exact Hs ] ].
Qed.

Lemma exp_plain_and : forall Θ Ξ P Q P' Q',
    exp_plain Θ Ξ P P' -> exp_plain Θ Ξ Q Q' -> exp_plain Θ Ξ (Σₚ P Q) (Σₚ P' Q').
Proof.
  intros * HP HQ Γ T HT.
  destruct (wf_and_inversion _ _ _ _ _ _ HT) as [HPt HQt Hs].
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_and_cong; [ exact HPt | exact (HP _ _ HPt) | exact (HQ _ _ HQt) ] | exact Hs ].
Qed.

Lemma exp_plain_app : forall Θ Ξ F N F' N',
    exp_plain Θ Ξ F F' -> exp_plain Θ Ξ N N' -> exp_plain Θ Ξ (F $ N) (F' $ N').
Proof.
  intros * HF HN Γ T HT.
  destruct (wf_app_inversion HT) as [κd κc D C HFt HNt Hs].
  pose proof (presup_exp_typ_cases HFt) as Hc; inversion Hc as [? S HS HPi |]; subst.
  destruct (wf_pi_inversion_at HPi) as [U HU HDt HCt Hk _].
  destruct (pi_domain_sort_kind HU HDt) as (SD & HSD & HDS).
  destruct (pi_cod_sort_large _ _ _ _ _ _ _ _ HU HCt) as [j HCj].
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_app_cong; [ exact HDS | exact HSD | exact HCj | exact Hk
                                                         | exact (HF _ _ HFt) | exact (HN _ _ HNt) ]
                            | exact Hs ].
Qed.

Lemma exp_plain_succl : forall Θ Ξ M M', exp_plain Θ Ξ M M' -> exp_plain Θ Ξ (succl M) (succl M').
Proof.
  intros * HM Γ T HT.
  destruct (wf_succl_inversion _ _ _ _ _ HT) as (n & HMt & Hs).
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_succl_cong; exact (HM _ _ HMt) | exact Hs ].
Qed.

Lemma exp_plain_maxl : forall Θ Ξ M N M' N',
    exp_plain Θ Ξ M M' -> exp_plain Θ Ξ N N' -> exp_plain Θ Ξ (maxl M N) (maxl M' N').
Proof.
  intros * HM HN Γ T HT.
  destruct (wf_maxl_inversion _ _ _ _ _ _ HT) as (n & HMt & HNt & Hs).
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_maxl_cong; [ exact (HM _ _ HMt) | exact (HN _ _ HNt) ] | exact Hs ].
Qed.

Lemma exp_plain_apps : forall Θ Ξ Ns Ns' H H',
    List.Forall2 (exp_plain Θ Ξ) Ns Ns' -> exp_plain Θ Ξ H H' -> exp_plain Θ Ξ (apps_exp H Ns) (apps_exp H' Ns').
Proof.
  intros * HNs; revert H H'; induction HNs as [| N N' Ns Ns' HN HNs IH]; intros H H' HH; cbn [apps_exp];
    [ exact HH | apply IH, exp_plain_app; assumption ].
Qed.

Lemma exp_plain_succl_n : forall Θ Ξ k M M', exp_plain Θ Ξ M M' -> exp_plain Θ Ξ (succl_n k M) (succl_n k M').
Proof. induction k as [| k IH]; intros * HM; cbn [succl_n]; [ exact HM | apply exp_plain_succl, IH, HM ]. Qed.

Lemma exp_plain_lvl_fold : forall Θ Ξ xs xs' H H',
    List.Forall2 (fun x x' => fst x = fst x' /\ exp_plain Θ Ξ (snd x) (snd x')) xs xs' ->
    exp_plain Θ Ξ H H' -> exp_plain Θ Ξ (lvl_fold H xs) (lvl_fold H' xs').
Proof.
  intros * Hxs; revert H H'; induction Hxs as [| [k a] [k' a'] xs xs' [Hk Ha] Hxs IH]; intros H H' HH;
    cbn [lvl_fold fst snd] in *; [ exact HH | subst k' ].
  apply IH, exp_plain_maxl; [ exact HH | apply exp_plain_succl_n; exact Ha ].
Qed.

Lemma exp_plain_lvl_exp_of : forall Θ Ξ c xs xs',
    List.Forall2 (fun x x' => fst x = fst x' /\ exp_plain Θ Ξ (snd x) (snd x')) xs xs' ->
    exp_plain Θ Ξ (lvl_exp_of c xs) (lvl_exp_of c xs').
Proof.
  intros * Hxs; destruct Hxs as [| [k a] [k' a'] xs xs' [Hk Ha] Hxs]; cbn [fst snd] in *; [ apply exp_plain_refl | subst k' ].
  unfold lvl_exp_of; destruct c as [[| c1] [| c2]];
    apply exp_plain_lvl_fold; try exact Hxs;
    first [ apply exp_plain_succl_n; exact Ha | apply exp_plain_maxl; [ apply exp_plain_refl | apply exp_plain_succl_n; exact Ha ] ].
Qed.

Lemma exp_plain_absurd : forall Θ Ξ C M C', exp_plain Θ Ξ C C' -> exp_plain Θ Ξ (efq M return C) (efq M return C').
Proof.
  intros * HC Γ T HT.
  destruct (wf_absurd_inversion_closed _ _ _ _ _ _ HT) as (S & HS & Hc & HCt & HMt & Hs).
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_absurd_cong; [ exact HCt | exact HS | exact Hc | exact (HC _ _ HCt)
                                                            | exact HMt | exact HMt ]
                            | exact Hs ].
Qed.

(** An ascribed proof is the proof, which the ascription types at its
    proposition. *)
Lemma exp_plain_proof : forall Θ Ξ P M, exp_plain Θ Ξ (proof_ascription P M) M.
Proof.
  intros * Γ T HT.
  destruct (proof_ascription_inversion _ _ _ _ _ _ HT) as (HPt & HMt & Hs).
  pose proof (proof_ascription_typed _ _ _ _ _ HPt HMt) as H1.
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_irrelevant; [ exact HPt | exact H1 | exact HMt ] | exact Hs ].
Qed.

Lemma exp_plain_univ : forall Θ Ξ M M', exp_plain Θ Ξ M M' -> exp_plain Θ Ξ (Type⟨M⟩) (Type⟨M'⟩).
Proof.
  intros * HM Γ T HT.
  pose proof (wf_univ_inversion HT) as Hs.
  destruct (wf_univ_lvl_inversion HT) as [n HMt].
  eapply wf_exp_eq_subtyp'; [ eapply wf_exp_eq_univ_cong; exact (HM _ _ HMt) | exact Hs ].
Qed.

Lemma exp_plain_proj : forall Θ Ξ f M M', exp_plain Θ Ξ M M' -> exp_plain Θ Ξ (a_proj f M) (a_proj f M').
Proof.
  intros * HM Γ T HT.
  destruct (wf_proj_inversion HT) as [p R Ns k U S HMt Hr Hl Hn HNs Hfk HUt HS Hs].
  destruct (record_sort_large _ _ _ _ _ _ Hr Hl Hn HNs) as [n HSn].
  destruct (record_proj_cong_at _ _ _ _ _ _ _ _ _ _ _ _ (HM _ _ HMt) Hr Hl Hn HNs HSn Hfk) as [_ E].
  eapply wf_exp_eq_subtyp'; [ exact E | exact Hs ].
Qed.

(** The plain tuple is typed at its annotation: its fields are equal to
    the annotation's, so they are of the field types at the plain fields
    before them, which are equal to the types at the annotation's. *)
Lemma exp_plain_tuple : forall Θ Ξ T T' fs fs',
    exp_plain Θ Ξ T T' -> List.map fst fs = List.map fst fs' ->
    List.Forall2 (fun x x' => exp_plain Θ Ξ (snd x) (snd x')) fs fs' ->
    exp_plain Θ Ξ (a_tuple T fs) (a_tuple T' fs').
Proof.
  intros * HT0 Hnames HF Γ A HA.
  destruct (wf_tuple_inversion HA) as [p R Ns i HTt HTe Hr Hl Hn HNs Hfs HMs Hsub].
  pose proof (HT0 _ _ HTt) as HTT.
  assert (HΓ : ⊢ Θ ⍮ Ξ ⍮ Γ) by (gen_presups; assumption).
  destruct (wf_record_inversion Hr) as [R0 Hl0 Hnd Hass i0 Hty HF0 HS0 HFs _].
  rewrite Hl in Hl0; injection Hl0 as <-.
  pose proof (wf_record_closed _ _ _ _ _ HΓ Hl) as Hc.
  destruct (record_sort_large _ _ _ _ _ _ Hr Hl Hn HNs) as [n HSn].
  assert (Hfs' : List.map fst fs' = List.map fst fs) by (symmetry; exact Hnames).
  assert (Hlf : List.length fs = List.length (record_fields R))
    by (rewrite <- (List.length_map fst fs), <- (List.length_map fst (record_fields R)), Hfs; reflexivity).
  assert (HMM : forall k f M M' U, List.nth_error fs k = Some (f, M) -> List.nth_error fs' k = Some (f, M') ->
             List.nth_error (record_fields R) k = Some (f, U) ->
             Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : U[sb_of_list Id (Ns ++ List.firstn k (List.map snd fs))]).
  { intros k f M M' U Hk Hk' Hfk.
    exact (Forall2_nth_both _ _ _ HF _ _ _ Hk Hk' _ _ (HMs _ _ _ _ Hk Hfk)). }
  assert (HNN : forall j X Y T0, List.nth_error Ns j = Some X -> List.nth_error Ns j = Some Y ->
             List.nth_error (tele_insts (record_params R) Id Ns) j = Some T0 -> Θ ⍮ Ξ ⍮ Γ ⊢ X ≈ Y : T0)
    by (intros j X Y T0 HX HY HT1; rewrite HX in HY; injection HY as <-; apply wf_exp_eq_refl; exact (HNs _ _ _ HX HT1)).
  pose proof (record_fields_insts_eq _ _ _ p R Ns Ns fs fs' Hr Hl Hn Hn HNN Hfs Hfs' HMM) as Hins.
  assert (H1 : Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T fs : T) by (eapply wf_tuple; eassumption).
  assert (H2 : Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T' fs' : T').
  { eapply wf_tuple; [ exact (presup_exp_eq_right HTT) | etransitivity; [ symmetry; exact HTT | exact HTe ] | exact Hr | exact Hl
                     | exact Hn | exact HNs | rewrite Hfs'; exact Hfs |].
    intros k f M' U Hk' Hfk.
    assert (Hlt : k < List.length (record_fields R)) by exact (nth_error_lt_length _ _ _ Hfk).
    destruct (nth_error_lt_some fs k ltac:(lia)) as [[g M] Hg].
    assert (g = f) as ->.
    { pose proof (List.map_nth_error fst _ _ Hg) as E1; pose proof (List.map_nth_error fst _ _ Hfk) as E2.
      rewrite Hfs in E1; rewrite E1 in E2; injection E2 as ->; reflexivity. }
    pose proof (HMM _ _ _ _ _ Hg Hk' Hfk) as HE.
    assert (Hlf' : List.length fs' = List.length fs)
      by (rewrite <- (List.length_map fst fs'), <- (List.length_map fst fs), Hfs'; reflexivity).
    pose proof (record_field_sort_cong _ _ _ R k f U Ns (List.firstn k (List.map snd fs)) (Ns ++ List.firstn k (List.map snd fs'))
                  Hc Hass HFs HΓ Hfk Hn ltac:(rewrite List.length_firstn, List.length_map; lia)
                  ltac:(rewrite List.length_app, List.length_firstn, List.length_map; lia) (Hins k ltac:(lia))) as HTTk.
    eapply wf_conv_rel; [ exact (presup_exp_eq_right HE) | eapply abs_kind_sort_exp_eq_up; [ exact HTTk | exact HSn ] ]. }
  assert (H2' : Θ ⍮ Ξ ⍮ Γ ⊢ a_tuple T' fs' : T) by (eapply wf_conv; [ exact H2 | exact HTt | symmetry; exact HTT ]).
  eapply wf_exp_eq_subtyp'; [| exact Hsub ].
  eapply wf_exp_eq_tuple_cong; [ exact H1 | exact HTT | exact HTe | exact Hl | exact Hn | exact HNs | exact Hfs
                               | exact Hfs' | exact HMM | exact H2' ].
Qed.

(** A stuck eliminator: the plain blocks at the annotation's uniform
    parameters, each part equal to the annotation's. *)
Lemma exp_plain_elim : forall Θ Ξ p Us Us' m Bks Bks' M M',
    List.Forall2 (exp_plain Θ Ξ) Us Us' ->
    List.Forall2 (fun b b' => eb_binder_count b = eb_binder_count b' /\
                   exp_plain Θ Ξ (eb_scrutinee_type b) (eb_scrutinee_type b') /\
                   exp_plain Θ Ξ (eb_motive b) (eb_motive b') /\
                   List.Forall2 (fun br br' => fst br = fst br' /\ exp_plain Θ Ξ (snd br) (snd br')) (eb_brs b) (eb_brs b'))
      Bks Bks' ->
    exp_plain Θ Ξ M M' ->
    exp_plain Θ Ξ (a_elim ak_relevant p Us m Bks M) (a_elim ak_relevant p Us' m Bks' M').
Proof.
  intros * HUs HBks HM Γ T HT.
  destruct (wf_elim_inversion HT) as [D Mm bm Ps i Hl Hm Hbm HPl HPs HMt HUe HBt Hs].
  subst Us.
  pose proof (presup_exp_ctx HMt) as HΓ.
  destruct (decl_of_lookup _ _ _ _ _ HΓ Hl) as [HD Hc].
  pose proof (HM _ _ HMt) as HMM.
  assert (Hnu : ind_nu D <= im_np D Mm) by (unfold im_np; lia).
  assert (HUl' : List.length Us' = ind_nu D)
    by (rewrite <- (List.Forall2_length HUs), List.length_firstn; lia).
  set (Ps'' := Us' ++ List.skipn (ind_nu D) Ps).
  assert (HPl'' : List.length Ps'' = im_np D Mm) by (unfold Ps''; rewrite List.length_app, HUl', List.length_skipn; lia).
  assert (HU'' : List.firstn (ind_nu D) Ps'' = Us')
    by (unfold Ps''; rewrite List.firstn_app, HUl', PeanoNat.Nat.sub_diag, List.firstn_O, List.app_nil_r, <- HUl', List.firstn_all;
        reflexivity).
  assert (HPP : forall k P P'' T0, nth_error Ps k = Some P -> nth_error Ps'' k = Some P'' ->
             nth_error (tele_insts (im_params D Mm) Id Ps) k = Some T0 -> Θ ⍮ Ξ ⍮ Γ ⊢ P ≈ P'' : T0).
  { intros k P P'' T0 HP HP'' HT0.
    destruct (PeanoNat.Nat.lt_ge_cases k (ind_nu D)) as [Hk | Hk].
    - unfold Ps'' in HP''; rewrite List.nth_error_app1 in HP'' by lia.
      assert (HP1 : nth_error (List.firstn (ind_nu D) Ps) k = Some P)
        by (rewrite List.nth_error_firstn; destruct (PeanoNat.Nat.ltb_spec k (ind_nu D)); [ exact HP | lia ]).
      exact (Forall2_nth_both _ _ _ HUs _ _ _ HP1 HP'' _ _ (HPs _ _ _ HP HT0)).
    - unfold Ps'' in HP''; rewrite List.nth_error_app2 in HP'' by lia; rewrite HUl', List.nth_error_skipn in HP''.
      replace (ind_nu D + (k - ind_nu D)) with k in HP'' by lia; rewrite HP in HP''; injection HP'' as <-.
      apply wf_exp_eq_refl; exact (HPs _ _ _ HP HT0). }
  pose proof (List.Forall2_length HBks) as HlBB.
  assert (Hb' : forall k b', nth_error Bks' k = Some b' -> exists b, nth_error Bks k = Some b).
  { intros k b' Hb'; apply nth_error_lt_some; rewrite HlBB; exact (nth_error_lt_length _ _ _ Hb'). }
  eapply wf_exp_eq_subtyp'; [| exact Hs ].
  destruct HBt as [HlB Hnm HZ HAb HΨ Hn HΨB Hk HB Hmk].
  eapply wf_exp_eq_elim_cong with (Ps := Ps) (Ps' := Ps''); try eassumption; try (symmetry; exact HU''); try reflexivity.
  - rewrite <- HlBB; exact HlB.
  - (** The plain binder counts *)
    intros k Mk b' Hk' Hb0'; destruct (Hb' _ _ Hb0') as [b Hb0].
    destruct (Forall2_nth_both _ _ _ HBks _ _ _ Hb0 Hb0') as (Hc0 & _).
    rewrite <- Hc0; exact (Hnm _ _ _ Hk' Hb0).
  - (** The plain scrutinee types, equal to the annotation's *)
    intros k Mk b' Hk' Hb0'; destruct (Hb' _ _ Hb0') as [b Hb0].
    destruct (Forall2_nth_both _ _ _ HBks _ _ _ Hb0 Hb0') as (_ & HZZ & _).
    pose proof (HZ _ _ _ Hk' Hb0) as HZ0; unfold elim_mctx in HZ0 |- *.
    assert (Hass : all_assumptions (tele_sub (im_nparams Mk) (sb_of_list Id (List.firstn (ind_nu D) Ps))))
      by (apply all_assumptions_sub; exact (decl_typed_nparams_ass _ _ _ HD _ _ Hk')).
    destruct (ext_eq_ass_inv _ _ _ _ _ _ _ _ HZ0) as [S1 HS1 S1' HS1' HTT HZt _ _ _].
    pose proof (HZZ _ _ HZt) as HE.
    pose proof (sort_kind_type_sort _ _ HS1) as HS1t.
    eapply ann_ctx_trans; [| exact HZ0 | exact Hass ].
    eapply wf_ext_eq_ass; [ exact (ctx_ext_refl _ _ _ _ Hass (ext_eq_ctx_left _ _ _ _ _ HTT)) | exact HZt | exact HS1
                          | exact (presup_exp_eq_right HE) | exact HS1
                          | eapply wf_subtyp_refl; [ exact (presup_exp_eq_right HE) | exact HS1t | exact HE ]
                          | eapply wf_subtyp_refl; [ exact HZt | exact HS1t | symmetry; exact HE ] ].
  - (** The motives *)
    intros k Mk b b' Hk' Hb0 Hb0'.
    destruct (Forall2_nth_both _ _ _ HBks _ _ _ Hb0 Hb0') as (_ & _ & HA & _).
    exact (HA _ _ (HAb _ _ _ Hk' Hb0)).
  - (** The branches' names *)
    intros k b b' Hb0 Hb0'; destruct (Forall2_nth_both _ _ _ HBks _ _ _ Hb0 Hb0') as (_ & _ & _ & Hbr).
    clear - Hbr; induction Hbr as [| x y l l' [Hxy _] _ IH]; cbn; [ reflexivity | rewrite Hxy, IH; reflexivity ].
  - (** The branches, at the annotation's motives *)
    intros k Mk b b' i0 c gs n B B' Hk' Hb0 Hb0' HB0 HB0' Hcon.
    destruct (Forall2_nth_both _ _ _ HBks _ _ _ Hb0 Hb0') as (_ & _ & _ & Hbr).
    pose proof (Forall2_nth_both _ _ _ Hbr _ _ _ HB0 HB0') as [_ HBB]; cbn [snd] in HBB.
    exact (HBB _ _ (HB _ _ _ _ _ _ _ Hk' Hb0 Hcon (List.nth_error_In _ _ HB0))).
Qed.

Theorem nf_ne_annotate_proofs_plain_rel :
  (forall W Θ Ξ, exp_plain Θ Ξ (nf_annotate_proofs W) W) /\
  (forall M Θ Ξ, exp_plain Θ Ξ (ne_annotate_proofs M) M).
Proof.
  apply nf_ne_ind; intros; cbn [nf_annotate_proofs ne_annotate_proofs nf_to_exp ne_to_exp].
  all: try apply exp_plain_refl.
  all: try solve [ first [ apply exp_plain_and | apply exp_plain_pi | apply exp_plain_fn | apply exp_plain_app
                         | apply exp_plain_absurd | apply exp_plain_proj ]; eauto ].
  all: try solve [ eauto ].
  all: try apply exp_plain_proof.
  (** Type formers and constructors at their arguments *)
  all: try (apply exp_plain_apps; [| apply exp_plain_refl ]; rewrite !List.map_map;
            match goal with Hl : Base.list_all _ _ ?l |- _ =>
              clear - Hl; induction Hl as [| x Hx l' Hl' IH]; cbn; constructor; [ exact (Hx _ _) | exact IH ] end).
  (** Levels and small universes, atom by atom *)
  all: try (try apply exp_plain_univ; apply exp_plain_lvl_exp_of; rewrite !List.map_map;
            match goal with Hl : Base.list_all _ _ ?l |- _ =>
              clear - Hl; induction Hl as [| x Hx l' Hl' IH]; cbn; constructor; [ destruct Hx; cbn; split; [ reflexivity | eauto ] | exact IH ] end).
  - (** A tuple: its type's parameters, its names, its fields *)
    apply exp_plain_tuple.
    + apply exp_plain_apps; [| apply exp_plain_refl ]; rewrite !List.map_map.
      match goal with Hl : Base.list_all _ _ ?l |- List.Forall2 _ (List.map _ ?l) (List.map _ ?l) =>
        clear - Hl; induction Hl as [| x Hx l' Hl' IH]; cbn; constructor; [ exact (Hx _ _) | exact IH ] end.
    + rewrite !List.map_map; clear; revert l1; induction l0 as [| f l0 IH]; intros [| x l1]; cbn; try reflexivity;
        f_equal; apply IH.
    + assert (HF : List.Forall2 (exp_plain Θ Ξ) (map nf_to_exp (map nf_annotate_proofs l1)) (map nf_to_exp l1))
        by (rewrite !List.map_map; clear - H0; induction H0 as [| x Hx l' Hl' IH]; cbn; constructor; [ exact (Hx _ _) | exact IH ]).
      clear - HF; revert l0; induction HF as [| x y X Y Hxy HF IH]; intros [| f l0]; cbn; constructor; [ exact Hxy | apply IH ].
  - (** A stuck eliminator: its uniform parameters, its blocks, its scrutinee *)
    apply exp_plain_elim.
    + rewrite !List.map_map.
      match goal with Hl : Base.list_all _ _ ?l |- List.Forall2 _ (List.map _ ?l) (List.map _ ?l) =>
        clear - Hl; induction Hl as [| x Hx l' Hl' IH]; cbn; constructor; [ exact (Hx _ _) | exact IH ] end.
    + rewrite !List.map_map; clear - H0; induction H0 as [| x Hx l' Hl' IH]; cbn; constructor; [| exact IH ].
      destruct Hx as [n' Z HZ A' HA brs Hbrs]; cbn.
      split; [ reflexivity | split; [ apply HZ | split; [ apply HA |] ] ].
      rewrite !List.map_map; clear - Hbrs; induction Hbrs as [| br Hbr brs' Hbrs' IH]; cbn; constructor; [| exact IH ].
      destruct Hbr; cbn; split; [ reflexivity | eauto ].
    + eauto.
Qed.

Theorem nf_ne_annotate_proofs_plain :
  (forall W Θ Ξ Γ T, Θ ⍮ Ξ ⍮ Γ ⊢ nf_annotate_proofs W : T -> Θ ⍮ Ξ ⍮ Γ ⊢ nf_annotate_proofs W ≈ W : T) /\
  (forall M Θ Ξ Γ T, Θ ⍮ Ξ ⍮ Γ ⊢ ne_annotate_proofs M : T -> Θ ⍮ Ξ ⍮ Γ ⊢ ne_annotate_proofs M ≈ M : T).
Proof.
  split; intros * HT; [ exact (proj1 nf_ne_annotate_proofs_plain_rel _ _ _ _ _ HT)
                      | exact (proj2 nf_ne_annotate_proofs_plain_rel _ _ _ _ _ HT) ].
Qed.
