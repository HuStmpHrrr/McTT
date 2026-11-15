(** * The Set Judgments Along Substitutions

    A substitution [σ] of [Δ] in [Γ] moves the set judgments when it sends
    the environments of [Γ] to environments of [Δ] ([set_gsub_with]): to
    each environment the values of its entries, related ones to related
    ones.  Under an extension [Ψ], an environment of [tele_sub Ψ σ ++ Γ]
    reads [Ψ ++ Δ] at its own entries over the extension and at [σ]'s
    below it ([set_env_above]).  Weakening past one more entry and the
    instantiation of an assumption are the two instances. *)

From Stdlib Require Import List Lia PeanoNat.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel.Judgments Require Export Definitions.
From Mctt.Core.SetModel.Interpretation Require Import Substitution.
From Mctt.Core.Syntactic Require Import Syntax.
From Mctt.Core.Syntactic.System Require Import Definitions Structural.
Import ListNotations.

(** [set_env_above n ρ ρb]: the first [n] entries of [ρ], then [ρb]. *)
Fixpoint set_env_above (n : nat) (ρ ρb : set_env) : set_env :=
  match n with
  | 0 => ρb
  | S n' => set_env_extend (set_env_above n' (set_env_tail ρ) ρb) (ρ 0)
  end.

Lemma set_env_above_lt : forall n ρ ρb x, x < n -> set_env_above n ρ ρb x = ρ x.
Proof. induction n as [| n IH]; intros ρ ρb [| x] Hx; cbn; try lia; [reflexivity |]. apply (IH (set_env_tail ρ)). lia. Qed.

Lemma set_env_above_ge : forall n ρ ρb x, set_env_above n ρ ρb (n + x) = ρb x.
Proof. induction n as [| n IH]; intros; cbn; [reflexivity | apply IH]. Qed.

Section Moves.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.
  Hypothesis Hfn : fn_kinds_unique.
  (** Every global module equals itself *)
  Hypothesis Hmods : forall q, set_module_eq γ (global_module γ q) (global_module γ q).

(** [set_gsub_with Γ σ Δ Fσ]: [σ] substitutes [Δ] in [Γ], and [Fσ] gives
    the environment of [Δ] its entries read at an environment of [Γ]. *)
Record set_gsub_with (Γ : ctx) (σ : sub) (Δ : ctx) (Fσ : set_env -> set_env) : Prop :=
  { (** [σ] is a substitution of [Δ] in [Γ] *)
    set_gsub_typed : gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ σ : Δ
    (** Its entries read the entries of [Fσ] *)
  ; set_gsub_agrees : forall ρ x, set_env_in T γ Γ ρ -> sub_entry_agrees T γ Γ ρ (σ x) (Fσ ρ x)
    (** Related environments go to related ones *)
  ; set_gsub_rel : forall ρ ρ', set_env_rel T γ Γ ρ ρ' -> set_env_rel T γ Δ (Fσ ρ) (Fσ ρ') }.

(** The environment of [Ψ ++ Δ] an environment of [tele_sub Ψ σ ++ Γ]
    reads. *)
Definition set_env_moved (n : nat) (Fσ : set_env -> set_env) (ρ : set_env) : set_env :=
  set_env_above n ρ (Fσ (set_env_drop n ρ)).

Lemma set_env_rel_drop : forall Ψ Γ ρ ρ', set_env_rel T γ (Ψ ++ Γ) ρ ρ' ->
    set_env_rel T γ Γ (set_env_drop (List.length Ψ) ρ) (set_env_drop (List.length Ψ) ρ').
Proof. induction Ψ as [| e Ψ IH]; intros * H; [exact H | exact (IH _ _ _ (proj1 H))]. Qed.

Lemma set_sub_setting_moved : forall Ψ Δ Γ σ Fσ ρ, set_gsub_with Γ σ Δ Fσ ->
    set_env_in T γ Γ (set_env_drop (List.length Ψ) ρ) ->
    sub_setting T γ (Ψ ++ Δ) (set_env_moved (List.length Ψ) Fσ ρ) Ψ Δ Γ σ (set_env_drop (List.length Ψ) ρ) ρ.
Proof.
  intros * [Hσ Hag _] Hρ. constructor; [reflexivity | exact Hσ | | |].
  - intros x Hx. apply set_env_above_lt. exact Hx.
  - intros y. reflexivity.
  - intros x. unfold set_env_moved. rewrite set_env_above_ge. apply Hag. exact Hρ.
Qed.

(** ** Readings Along the Substitution *)

Lemma set_interp_moved : forall Ψ Δ Γ σ Fσ ρ M v, set_gsub_with Γ σ Δ Fσ -> ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Δ ->
    set_env_in T γ Γ (set_env_drop (List.length Ψ) ρ) ->
    set_interp T γ (Ψ ++ Δ) (set_env_moved (List.length Ψ) Fσ ρ) M v ->
    set_interp T γ (tele_sub Ψ σ ++ Γ) ρ (exp_sub M (sb_qn (List.length Ψ) σ)) v.
Proof.
  intros * Hg Hc Hρ HM. exact (set_interp_sub T γ _ _ _ _ HM Hc _ _ _ _ _ _ (set_sub_setting_moved _ _ _ _ _ _ Hg Hρ)).
Qed.

Lemma set_interp_modexp_moved : forall Ψ Δ Γ σ Fσ ρ H m, set_gsub_with Γ σ Δ Fσ -> ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Δ ->
    set_env_in T γ Γ (set_env_drop (List.length Ψ) ρ) ->
    set_interp_modexp T γ (Ψ ++ Δ) (set_env_moved (List.length Ψ) Fσ ρ) H m ->
    set_interp_modexp T γ (tele_sub Ψ σ ++ Γ) ρ (modexp_sub H (sb_qn (List.length Ψ) σ)) m.
Proof.
  intros * Hg Hc Hρ HH.
  exact (proj1 (proj2 (proj2 (proj2 (set_interp_sub_all T γ)))) _ _ _ _ HH _ _ _ _ _ _ Hc (set_sub_setting_moved _ _ _ _ _ _ Hg Hρ)).
Qed.

Lemma set_interp_gunit_moved : forall Ψ Δ Γ σ Fσ ρ U m, set_gsub_with Γ σ Δ Fσ -> ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Δ ->
    set_env_in T γ Γ (set_env_drop (List.length Ψ) ρ) ->
    set_interp_gunit T γ (Ψ ++ Δ) (set_env_moved (List.length Ψ) Fσ ρ) U m ->
    set_interp_gunit T γ (tele_sub Ψ σ ++ Γ) ρ (gunit_sub U (sb_qn (List.length Ψ) σ)) m.
Proof.
  intros * Hg Hc Hρ HU.
  exact (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_sub_all T γ))))) _ _ _ _ HU _ _ _ _ _ _ Hc (set_sub_setting_moved _ _ _ _ _ _ Hg Hρ)).
Qed.

(** An environment equal to another is equal to itself. *)
Lemma set_env_eq_left : forall ρ ρ', set_env_eq γ ρ ρ' -> set_env_eq γ ρ ρ.
Proof. intros ρ ρ' H x. eapply set_entry_eq_trans; [apply H | apply set_entry_eq_sym; apply H]. Qed.

Lemma set_interp_gunit_functional : forall Γ ρ U m, set_interp_gunit T γ Γ ρ U m ->
    forall ρ' m', set_env_eq γ ρ ρ' -> set_interp_gunit T γ Γ ρ' U m' -> set_module_eq γ m m'.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_functional_all T γ Hfn Hmods)))))). Qed.

(** Related environments of [tele_sub Ψ σ ++ Γ] read related ones of
    [Ψ ++ Δ]. *)
Lemma set_env_rel_moved : forall Ψ Δ Γ σ Fσ ρ ρ', set_gsub_with Γ σ Δ Fσ -> set_ctx T γ Γ -> set_ctx T γ (Ψ ++ Δ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Δ -> set_env_rel T γ (tele_sub Ψ σ ++ Γ) ρ ρ' ->
    set_env_rel T γ (Ψ ++ Δ) (set_env_moved (List.length Ψ) Fσ ρ) (set_env_moved (List.length Ψ) Fσ ρ').
Proof.
  intros Ψ Δ Γ σ Fσ. induction Ψ as [| ce Ψ IH]; intros ρ ρ' Hg HΓ HΔ Hc Hr; [exact (set_gsub_rel _ _ _ _ Hg _ _ Hr) |].
  destruct HΔ as [HΔ Hce]. destruct Hr as [Ht He].
  pose proof (ctx_decomp_tail Hc) as Hc'.
  pose proof (IH _ _ Hg HΓ HΔ Hc' Ht) as Ht'.
  change (set_env_tail (set_env_moved (S (List.length Ψ)) Fσ ρ)) with (set_env_moved (List.length Ψ) Fσ (set_env_tail ρ)).
  change (set_env_tail (set_env_moved (S (List.length Ψ)) Fσ ρ')) with (set_env_moved (List.length Ψ) Fσ (set_env_tail ρ')).
  change (set_env_moved (S (List.length Ψ)) Fσ ρ 0) with (ρ 0).
  change (set_env_moved (S (List.length Ψ)) Fσ ρ' 0) with (ρ' 0).
  split; [exact Ht' |].
  destruct (set_env_rel_per _ _ _ HΔ) as [Hsym Htrans].
  destruct (set_env_rel_per _ _ _ HΓ) as [HsymΓ HtransΓ].
  set (ρs := set_env_moved (List.length Ψ) Fσ (set_env_tail ρ)).
  assert (Hin : set_env_in T γ (Ψ ++ Δ) ρs) by (eapply Htrans; [exact Ht' | apply Hsym; exact Ht']).
  assert (Hb : set_env_in T γ Γ (set_env_drop (List.length Ψ) (set_env_tail ρ))).
  { pose proof (set_env_rel_drop _ _ _ _ Ht) as Hd. rewrite length_tele_sub in Hd.
    eapply HtransΓ; [exact Hd | apply HsymΓ; exact Hd]. }
  pose proof (set_env_eq_left _ _ (set_env_rel_eq _ _ _ _ _ Ht)) as Eρ.
  assert (Hmv : forall M v, set_interp T γ (Ψ ++ Δ) ρs M v ->
            set_interp T γ (tele_sub Ψ σ ++ Γ) (set_env_tail ρ) (exp_sub M (sb_qn (List.length Ψ) σ)) v)
    by (intros; apply (set_interp_moved _ _ _ _ _ _ _ _ Hg Hc' Hb); assumption).
  assert (Hmu : forall U m, set_interp_gunit T γ (Ψ ++ Δ) ρs U m ->
            set_interp_gunit T γ (tele_sub Ψ σ ++ Γ) (set_env_tail ρ) (gunit_sub U (sb_qn (List.length Ψ) σ)) m)
    by (intros; apply (set_interp_gunit_moved _ _ _ _ _ _ _ _ Hg Hc' Hb); assumption).
  destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_rel set_entry_valid centry_sub] in He, Hce |- *.
  - destruct He as (x & x' & a & [E1 E2 Ha Hx Ex]). destruct Hce as [FA HA].
    pose proof (set_denotes_exists _ _ _ _ _ HA _ Hin) as Ha0.
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ Ha _ _ Eρ (Hmv _ _ Ha0)) as E.
    exists x, x', (FA ρs). constructor; [exact E1 | exact E2 | exact Ha0 | | exact Ex].
    eapply set_mem_eq_r; [apply code_carrier_resp; exact E | exact Hx].
  - destruct He as (r & v & v' & w & [E1 E2 Hw Ev Ev']). destruct Hce as (FA & FM & FM' & [_ HM _ _ _]).
    pose proof (set_denotes_exists _ _ _ _ _ HM _ Hin) as Hw0.
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ Hw _ _ Eρ (Hmv _ _ Hw0)) as E.
    exists r, v, v', (FM ρs).
    constructor; [exact E1 | exact E2 | exact Hw0 | eapply set_eq_trans; [exact Ev | exact E] | eapply set_eq_trans; [exact Ev' | exact E]].
  - destruct He as (m & m' & n & [E1 E2 Hn Em Em']). destruct Hce as (FU & FU' & [HU _ _]).
    pose proof (proj1 (set_interp_me_lit_iff _ _ _ _ _ _) (set_modexp_denotes_exists _ _ _ _ _ HU _ Hin)) as Hn0.
    pose proof (set_interp_gunit_functional _ _ _ _ Hn _ _ Eρ (Hmu _ _ Hn0)) as E.
    exists m, m', (FU ρs).
    constructor; [exact E1 | exact E2 | exact Hn0 | eapply set_module_eq_trans; [exact Em | exact E]
                 | eapply set_module_eq_trans; [exact Em' | exact E]].
  - destruct He as (v & v' & w & m & m' & n & [E1 E2 Hw Hn Ev Ev' Em Em']).
    destruct Hce as [(FA & FM & FM' & [_ HM _ _ _]) (FU & FU' & [HU _ _])].
    pose proof (set_denotes_exists _ _ _ _ _ HM _ Hin) as Hw0.
    pose proof (set_interp_functional T γ Hfn Hmods _ _ _ _ Hw _ _ Eρ (Hmv _ _ Hw0)) as E.
    pose proof (proj1 (set_interp_me_lit_iff _ _ _ _ _ _) (set_modexp_denotes_exists _ _ _ _ _ HU _ Hin)) as Hn0.
    pose proof (set_interp_gunit_functional _ _ _ _ Hn _ _ Eρ (Hmu _ _ Hn0)) as En.
    exists v, v', (FM ρs), m, m', (FU ρs).
    constructor; [exact E1 | exact E2 | exact Hw0 | exact Hn0 | eapply set_eq_trans; [exact Ev | exact E]
                 | eapply set_eq_trans; [exact Ev' | exact E] | eapply set_module_eq_trans; [exact Em | exact En]
                 | eapply set_module_eq_trans; [exact Em' | exact En]].
Qed.

Corollary set_env_in_moved : forall Ψ Δ Γ σ Fσ ρ, set_gsub_with Γ σ Δ Fσ -> set_ctx T γ Γ -> set_ctx T γ (Ψ ++ Δ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Δ -> set_env_in T γ (tele_sub Ψ σ ++ Γ) ρ ->
    set_env_in T γ (Ψ ++ Δ) (set_env_moved (List.length Ψ) Fσ ρ).
Proof. intros * Hg HΓ HΔ Hc Hρ. exact (set_env_rel_moved _ _ _ _ _ _ _ Hg HΓ HΔ Hc Hρ). Qed.

Lemma set_env_in_drop : forall Ψ σ Γ ρ, set_env_in T γ (tele_sub Ψ σ ++ Γ) ρ ->
    set_env_in T γ Γ (set_env_drop (List.length Ψ) ρ).
Proof. intros * Hρ. pose proof (set_env_rel_drop _ _ _ _ Hρ) as H. rewrite length_tele_sub in H. exact H. Qed.

(** ** Judgments Along the Substitution *)

(** The setting the judgments move in: both contexts denote, and the
    source is well formed. *)
Record set_moves_with (Ψ Δ Γ : ctx) (σ : sub) (Fσ : set_env -> set_env) : Prop :=
  { (** [σ] sends environments of [Γ] to ones of [Δ] *)
    set_moves_gsub : set_gsub_with Γ σ Δ Fσ
    (** The target's base denotes *)
  ; set_moves_base : set_ctx T γ Γ
    (** The source denotes *)
  ; set_moves_source : set_ctx T γ (Ψ ++ Δ)
    (** The target denotes *)
  ; set_moves_target : set_ctx T γ (tele_sub Ψ σ ++ Γ)
    (** The source is well formed *)
  ; set_moves_wf : ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Δ }.

Lemma set_denotes_moved : forall Ψ Δ Γ σ Fσ M F, set_moves_with Ψ Δ Γ σ Fσ -> set_denotes T γ (Ψ ++ Δ) M F ->
    set_denotes T γ (tele_sub Ψ σ ++ Γ) (exp_sub M (sb_qn (List.length Ψ) σ)) (fun ρ => F (set_env_moved (List.length Ψ) Fσ ρ)).
Proof.
  intros * [Hg HΓ HΔ HΓ' Hc] HM. apply set_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ' |]. intros ρ Hρ.
  apply (set_interp_moved _ _ _ _ _ _ _ _ Hg Hc); [exact (set_env_in_drop _ _ _ _ Hρ) |].
  apply (set_denotes_exists _ _ _ _ _ HM). exact (set_env_in_moved _ _ _ _ _ _ Hg HΓ HΔ Hc Hρ).
Qed.

Lemma set_modexp_denotes_moved : forall Ψ Δ Γ σ Fσ H F, set_moves_with Ψ Δ Γ σ Fσ -> set_modexp_denotes T γ (Ψ ++ Δ) H F ->
    set_modexp_denotes T γ (tele_sub Ψ σ ++ Γ) (modexp_sub H (sb_qn (List.length Ψ) σ))
      (fun ρ => F (set_env_moved (List.length Ψ) Fσ ρ)).
Proof.
  intros * [Hg HΓ HΔ HΓ' Hc] HH. apply set_modexp_denotes_of_exists; [exact Hfn | exact Hmods | exact HΓ' |]. intros ρ Hρ.
  apply (set_interp_modexp_moved _ _ _ _ _ _ _ _ Hg Hc); [exact (set_env_in_drop _ _ _ _ Hρ) |].
  apply (set_modexp_denotes_exists _ _ _ _ _ HH). exact (set_env_in_moved _ _ _ _ _ _ Hg HΓ HΔ Hc Hρ).
Qed.

Lemma set_exp_eq_with_moved : forall Ψ Δ Γ σ Fσ A M M' FA FM FM', set_moves_with Ψ Δ Γ σ Fσ ->
    set_exp_eq_with T γ (Ψ ++ Δ) A M M' FA FM FM' ->
    set_exp_eq_with T γ (tele_sub Ψ σ ++ Γ) (exp_sub A (sb_qn (List.length Ψ) σ)) (exp_sub M (sb_qn (List.length Ψ) σ))
      (exp_sub M' (sb_qn (List.length Ψ) σ)) (fun ρ => FA (set_env_moved (List.length Ψ) Fσ ρ))
      (fun ρ => FM (set_env_moved (List.length Ψ) Fσ ρ)) (fun ρ => FM' (set_env_moved (List.length Ψ) Fσ ρ)).
Proof.
  intros * Hs [HA HM HM' E Hm]. pose proof Hs as [Hg HΓ HΔ _ Hc].
  constructor; [exact (set_denotes_moved _ _ _ _ _ _ _ Hs HA) | exact (set_denotes_moved _ _ _ _ _ _ _ Hs HM)
               | exact (set_denotes_moved _ _ _ _ _ _ _ Hs HM') | |];
    intros ρ Hρ; [apply E | apply Hm]; exact (set_env_in_moved _ _ _ _ _ _ Hg HΓ HΔ Hc Hρ).
Qed.

Lemma set_exp_eq_moved : forall Ψ Δ Γ σ Fσ A M M', set_moves_with Ψ Δ Γ σ Fσ -> set_rel_exp_eq T γ (Ψ ++ Δ) A M M' ->
    set_rel_exp_eq T γ (tele_sub Ψ σ ++ Γ) (exp_sub A (sb_qn (List.length Ψ) σ)) (exp_sub M (sb_qn (List.length Ψ) σ))
      (exp_sub M' (sb_qn (List.length Ψ) σ)).
Proof. intros * Hs (FA & FM & FM' & H). exact (ex_intro _ _ (ex_intro _ _ (ex_intro _ _ (set_exp_eq_with_moved _ _ _ _ _ _ _ _ _ _ _ Hs H)))). Qed.

Lemma set_modexp_rel_moved : forall Ψ Δ Γ σ Fσ H H', set_moves_with Ψ Δ Γ σ Fσ -> set_modexp_rel T γ (Ψ ++ Δ) H H' ->
    set_modexp_rel T γ (tele_sub Ψ σ ++ Γ) (modexp_sub H (sb_qn (List.length Ψ) σ)) (modexp_sub H' (sb_qn (List.length Ψ) σ)).
Proof.
  intros * Hs (F & F' & [HF HF' E]). pose proof Hs as [Hg HΓ HΔ _ Hc].
  exists (fun ρ => F (set_env_moved (List.length Ψ) Fσ ρ)), (fun ρ => F' (set_env_moved (List.length Ψ) Fσ ρ)).
  constructor; [exact (set_modexp_denotes_moved _ _ _ _ _ _ _ Hs HF) | exact (set_modexp_denotes_moved _ _ _ _ _ _ _ Hs HF') |].
  intros ρ Hρ. apply E. exact (set_env_in_moved _ _ _ _ _ _ Hg HΓ HΔ Hc Hρ).
Qed.

(** ** Contexts Along the Substitution *)

Lemma set_ctx_moved : forall Ψ Δ Γ σ Fσ, set_gsub_with Γ σ Δ Fσ -> set_ctx T γ Γ -> set_ctx T γ (Ψ ++ Δ) ->
    ⊢ gc_deps ⍮ gc_stack ⍮ Ψ ++ Δ -> set_ctx T γ (tele_sub Ψ σ ++ Γ).
Proof.
  induction Ψ as [| ce Ψ IH]; intros * Hg HΓ HΔ Hc; [exact HΓ |].
  destruct HΔ as [HΔ Hce]. pose proof (ctx_decomp_tail Hc) as Hc'.
  pose proof (IH _ _ _ _ Hg HΓ HΔ Hc') as HΓ'. split; [exact HΓ' |].
  assert (Hs : set_moves_with Ψ Δ Γ σ Fσ) by (constructor; assumption).
  destruct ce as [κ A | A M | U | A M U]; cbn [set_entry_valid centry_sub] in Hce |- *.
  - destruct Hce as [FA HA]. eexists. exact (set_denotes_moved _ _ _ _ _ _ _ Hs HA).
  - exact (set_exp_eq_moved _ _ _ _ _ _ _ _ Hs Hce).
  - exact (set_modexp_rel_moved _ _ _ _ _ (me_lit U) (me_lit U) Hs Hce).
  - destruct Hce as [HM HU]. split; [exact (set_exp_eq_moved _ _ _ _ _ _ _ _ Hs HM)
                                  | exact (set_modexp_rel_moved _ _ _ _ _ (me_lit U) (me_lit U) Hs HU)].
Qed.

(** The substitution lifted past the extension sends the environments of
    the moved extension to the moved environments. *)
Lemma set_gsub_lift : forall Ψ Δ Γ σ Fσ, set_moves_with Ψ Δ Γ σ Fσ ->
    set_gsub_with (tele_sub Ψ σ ++ Γ) (sb_qn (List.length Ψ) σ) (Ψ ++ Δ) (set_env_moved (List.length Ψ) Fσ).
Proof.
  intros * [Hg HΓ HΔ HΓ' Hc]. constructor.
  - apply wf_sub_ext; [exact (set_gsub_typed _ _ _ _ Hg) | exact (ctx_sub _ _ _ _ Hc (set_gsub_typed _ _ _ _ Hg)) | exact Hc].
  - intros ρ x Hρ. exact (sub_setting_var T γ _ _ _ _ _ _ _ _ x Hc (set_sub_setting_moved _ _ _ _ _ _ Hg (set_env_in_drop _ _ _ _ Hρ))).
  - intros ρ ρ' Hr. exact (set_env_rel_moved _ _ _ _ _ _ _ Hg HΓ HΔ Hc Hr).
Qed.

(** ** The Instances *)

(** Weakening past one more entry: its environments without their
    variable [#0]. *)
Lemma set_gsub_shift : forall Γ e, ⊢ gc_deps ⍮ gc_stack ⍮ e :: Γ -> set_gsub_with (e :: Γ) (sb_of_wk wk_shift) Γ set_env_tail.
Proof.
  intros * Hc. constructor.
  - apply wf_sub_of_wk. apply wf_wk_shift. exact Hc.
  - intros ρ x _. split; cbn; [exact (set_interp_var T γ _ ρ (S x)) | exact (set_interp_me_var T γ _ ρ (S x))].
  - intros ρ ρ' [Ht _]. exact Ht.
Qed.

(** The instantiation of an assumption by a term of its type: its
    environments extended by the term's value. *)
Lemma set_gsub_single : forall Γ κ A N FA FN, set_ctx T γ Γ ->
    gc_deps ⍮ gc_stack ⍮ Γ ⊢ˢ sb_extend sb_id (se_exp N) : ce_ass κ A :: Γ ->
    set_denotes T γ Γ A FA -> set_denotes T γ Γ N FN -> (forall ρ, set_env_in T γ Γ ρ -> set_mem (FN ρ) (code_carrier (FA ρ))) ->
    set_gsub_with Γ (sb_extend sb_id (se_exp N)) (ce_ass κ A :: Γ) (fun ρ => set_env_extend ρ (set_entry_term κ (FN ρ))).
Proof.
  intros * HΓ Hσ HA HN Hm. destruct (set_env_rel_per _ _ _ HΓ) as [Hsym Htrans]. constructor; [exact Hσ | |].
  - intros ρ [| x] Hρ; split; cbn; first [exact (set_denotes_exists _ _ _ _ _ HN _ Hρ) | constructor].
  - intros ρ ρ' Hr.
    assert (Hl : set_env_in T γ Γ ρ) by (eapply Htrans; [exact Hr | apply Hsym; exact Hr]).
    assert (Hr' : set_env_in T γ Γ ρ') by (eapply Htrans; [apply Hsym; exact Hr | exact Hr]).
    apply (set_env_rel_extend_ass T γ Γ ρ ρ' κ A (FA ρ)); [exact Hr | exact (set_denotes_exists _ _ _ _ _ HA _ Hl) | exact (Hm _ Hl) |].
    apply set_eq_sym. exact (set_denotes_unique _ _ _ _ _ HN _ _ _ Hr (set_denotes_exists _ _ _ _ _ HN _ Hr')).
Qed.

(** ** Coherent Slots Along Substitutions *)

Lemma set_slots_coherent_resp : forall Γ κs κs', slot_proofs_eq κs κs' ->
    set_slots_coherent γ Γ κs -> set_slots_coherent γ Γ κs'.
Proof.
  induction Γ as [| ce Γ IH]; intros κs κs' E Hc; cbn [set_slots_coherent] in *; [exact I |].
  destruct Hc as [Hc Hu]. split; [exact (IH _ _ (fun s => E (S s)) Hc) |].
  intros U HU ys x. rewrite <- (E 0 ys x), (Hu U HU ys x).
  apply (proj1 (proj2 (unit_member_proofs_resp_all γ))). intros s; apply E.
Qed.

(** An environment of a context gives it coherent slots. *)
Lemma set_slots_coherent_env : forall Γ ρ, set_env_in T γ Γ ρ -> set_slots_coherent γ Γ (env_slot_proofs γ ρ).
Proof.
  induction Γ as [| ce Γ IH]; intros ρ Hρ; cbn [set_slots_coherent]; [exact I |].
  destruct Hρ as [Ht He]. split; [exact (IH _ Ht) |].
  intros U HU ys x. unfold env_slot_proofs at 1.
  destruct ce as [κ A | A M | U0 | A M U0]; cbn [centry_unit] in HU; try discriminate; injection HU as <-; cbn [set_entry_rel] in He.
  - destruct He as (m & m' & n & [-> _ Hn Hmn _]); cbn [set_entry_module_part].
    rewrite (module_member_proofs_resp γ ys _ _ Hmn x).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_member_proofs_all T γ))))) _ _ _ _ Hn ys x).
  - destruct He as (v & v' & w & m & m' & n & [-> _ _ Hn _ _ Hmn _]); cbn [set_entry_module_part].
    rewrite (module_member_proofs_resp γ ys _ _ Hmn x).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (set_interp_member_proofs_all T γ))))) _ _ _ _ Hn ys x).
Qed.

(** [set_sub_slots_coherent Δ Γ σ]: [σ], a substitution of [Δ] in [Γ],
    gives coherent slots of [Δ] at coherent slots of [Γ]. *)
Definition set_sub_slots_coherent (Δ Γ : ctx) (σ : sub) : Prop :=
  forall κs, set_slots_coherent γ Γ κs -> set_slots_coherent γ Δ (fun s => modexp_member_proofs γ κs (sentry_modexp (σ s))).

Lemma centry_unit_sub : forall e τ U, centry_unit e = Some U -> centry_unit (centry_sub e τ) = Some (gunit_sub U τ).
Proof. intros [] τ U H; cbn in *; try discriminate; injection H as <-; reflexivity. Qed.

Lemma set_sub_slots_coherent_q : forall e Δ Γ τ, set_sub_slots_coherent Δ Γ τ ->
    set_sub_slots_coherent (e :: Δ) (centry_sub e τ :: Γ) (sb_q τ).
Proof.
  intros * Hτ κs [Hc Hu].
  set (κs0 := fun s => modexp_member_proofs γ (fun s' => κs (S s')) (sentry_modexp (τ s))).
  apply (set_slots_coherent_resp _ (push_slot_proofs κs0 (κs 0))).
  - intros s ys x. symmetry.
    rewrite (proj1 (unit_member_proofs_resp_all γ) _ κs (push_slot_proofs (fun s' => κs (S s')) (κs 0))) by (intros [| s'] ys' x'; reflexivity).
    symmetry. exact (slot_proofs_sub_q γ (fun s' => κs (S s')) τ κs0 (κs 0) (κs 0) ltac:(intros s' ys' x'; reflexivity)
                       ltac:(intros; reflexivity) s ys x).
  - split; [exact (Hτ _ Hc) |]. intros U HU ys x. cbn [push_slot_proofs].
    rewrite (Hu _ (centry_unit_sub _ τ _ HU) ys x).
    apply (proj2 (unit_member_proofs_sub_all γ)). intros s ys' x'; reflexivity.
Qed.

(** Lifted past an extension. *)
Lemma set_sub_slots_coherent_lift : forall Ψ Δ Γ σ, set_sub_slots_coherent Δ Γ σ ->
    set_sub_slots_coherent (Ψ ++ Δ) (tele_sub Ψ σ ++ Γ) (sb_qn (List.length Ψ) σ).
Proof.
  induction Ψ as [| e Ψ IH]; intros * Hσ; [exact Hσ |].
  cbn [List.app tele_sub List.length sb_qn]. apply set_sub_slots_coherent_q. exact (IH _ _ _ Hσ).
Qed.

(** Weakening past one more entry. *)
Lemma set_sub_slots_coherent_shift : forall e Γ, set_sub_slots_coherent Γ (e :: Γ) (sb_of_wk wk_shift).
Proof. intros * κs [Hc _]. apply (set_slots_coherent_resp _ _ _ ltac:(intros s ys x; reflexivity) Hc). Qed.

End Moves.
