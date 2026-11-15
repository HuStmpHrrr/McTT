(** * The Set Model of Universes

    The set judgments of the rules of the universes: a universe denotes
    its code, a member of the next universe's carrier. *)

From Stdlib Require Import String List.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.SetModel Require Export Judgments.
From Mctt.Core.Syntactic Require Import Syntax.
Import ListNotations.

Section Universes.
  Context {GC : GCtx}.
  Variable T : universe_tower.
  Variable γ : global_valuation.

(** A term every derivation gives the value [c] denotes [c]. *)
Lemma set_denotes_const : forall Γ M c, (forall ρ, set_interp T γ Γ ρ M c) ->
    (forall ρ v, set_interp T γ Γ ρ M v -> set_eq v c) -> set_denotes T γ Γ M (fun _ => c).
Proof. intros * Hex Hun. constructor; [intros ρ _; apply Hex | intros ρ ρ' v _ Hv; exact (Hun _ _ Hv)]. Qed.

(** The code of the large universe [Typeω@i]. *)
Definition large_universe_code (i : nat) : aczel_set := universe_code (large_ordinal_set i) (tower T (ul i)).

Lemma set_denotes_typ : forall Γ i, set_denotes T γ Γ (a_typ i) (fun _ => large_universe_code i).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

(** A universe code of a member of a universe of sets is relevant and a
    member. *)
Lemma universe_code_mem : forall l U V, grothendieck V -> set_mem l V -> set_mem U V ->
    set_mem (universe_code l U) V /\ is_relevant_code (universe_code l U).
Proof.
  intros * HV Hl HU. split.
  - apply (grothendieck_type_code _ HV); [exact Hl | apply (grothendieck_separation _ HV); exact HU].
  - do 3 eexists. split; [apply set_eq_refl | discriminate].
Qed.

(** The code of the small universe at a literal level [o]. *)
Definition small_universe_code (o : o2) : aczel_set :=
  universe_code (pair_ordinal_set o) (small_universe_set T (pair_ordinal_set o)).

Lemma set_denotes_univ_lit : forall Γ o, set_denotes T γ Γ (a_univ (a_llit o)) (fun _ => small_universe_code o).
Proof.
  intros. apply set_denotes_const; [intros; constructor; constructor |].
  intros ρ v H. inversion H; subst. match goal with Hl : set_interp _ _ _ _ (a_llit _) _ |- _ => inversion Hl; subst end.
  apply set_eq_refl.
Qed.

(** A relevant code of the universe of sets at [o] is of the small
    universe's carrier. *)
Lemma set_mem_small_universe_code : forall o x, set_mem x (tower T (us o)) -> is_relevant_code x ->
    set_mem x (code_carrier (small_universe_code o)).
Proof.
  intros * Hx Hr. unfold small_universe_code, universe_code. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |].
  apply set_mem_separation; [exact is_relevant_code_resp |]. split; [| exact Hr].
  eapply set_mem_eq_r; [apply set_eq_sym; apply small_universe_set_eq; apply set_eq_refl | exact Hx].
Qed.

(** ** Small Universes at Levels *)

Lemma set_mem_level_type : forall n z, set_mem z (code_carrier (level_type_code n)) <->
    exists o, fst o <= n /\ set_eq z (pair_ordinal_set o).
Proof.
  intros n z. unfold level_type_code. split.
  - intros Hz. eapply set_mem_eq_r in Hz; [| apply code_carrier_type_code]. destruct Hz as [[o Ho] E]. exists o. auto.
  - intros [o [Ho E]]. eapply set_mem_eq_r; [apply set_eq_sym; apply code_carrier_type_code |]. exists (exist _ o Ho). exact E.
Qed.

Lemma set_denotes_level : forall Γ n, set_denotes T γ Γ (a_level n) (fun _ => level_type_code n).
Proof. intros. apply set_denotes_const; [intros; constructor | intros ρ v H; inversion H; subst; apply set_eq_refl]. Qed.

(** The code of the small universe at a level's value. *)
Definition level_universe_code (l : aczel_set) : aczel_set := universe_code l (small_universe_set T l).

Lemma set_denotes_univ : forall Γ M FM, set_denotes T γ Γ M FM ->
    set_denotes T γ Γ (a_univ M) (fun ρ => level_universe_code (FM ρ)).
Proof.
  intros * HM. constructor; [intros ρ Hρ; constructor; exact (set_denotes_exists _ _ _ _ _ HM _ Hρ) |].
  intros ρ ρ' v Hr Hv. inversion Hv; subst.
  pose proof (set_denotes_unique _ _ _ _ _ HM _ _ _ Hr ltac:(eassumption)) as E.
  unfold level_universe_code, universe_code. apply type_code_resp; [exact E |].
  apply separation_set_resp; [exact is_relevant_code_resp | exact is_relevant_code_resp | apply small_universe_set_resp; exact E | tauto].
Qed.

End Universes.

(** ** The Rules *)


