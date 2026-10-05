From Stdlib Require Import Wf_nat.
From Mctt Require Import LibTactics.
From Mctt.Algorithmic.Typing Require Import Definitions.
From Mctt.Algorithmic.Subtyping Require Export Lemmas.
From Mctt.Core Require Import Base.
From Mctt.Core.Completeness Require Import Consequences.Rules.
From Mctt.Core.Semantic Require Import Consequences.
From Mctt.Core.Syntactic Require Import Corollaries.
From Mctt.Core.Syntactic.System Require Import GlobalModules MemberWf.
From Mctt.Core.Semantic Require Import MemberWf.
Import Domain_Notations Fixed_Notations.

Lemma me_noargs_spine : forall H R args pre, me_noargs H -> modexp_spine H = (R, args, pre) -> args = nil.
Proof.
  induction H as [| | H IH y | H IH N | ]; intros * Hn Hs; cbn in *; try (injection Hs; intros; subst; reflexivity).
  - destruct (modexp_spine H) as [[R0 args0] pre0]; injection Hs; intros; subst; eauto.
  - contradiction.
Qed.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma functional_alg_type_infer : forall {Γ A A' M},
    Γ ⊢a M ⟹ A ->
    Γ ⊢a M ⟹ A' ->
    A = A'.
Proof.
  intros * HM1 HM2. gen A'.
  induction HM1; intros;
    inversion_clear HM2;
    functional_nbe_rewrite_clear;
    f_equiv;
    try reflexivity;
    intuition.
  (** A global against another rule for members: a chain from a unit has no
      argument, and a global's member type is its resolved type. *)
  all: try solve [ exfalso; match goal with
    | Hp : mod_qname ?H = Some _, Hs : modexp_spine ?H = (_, ?args, _), Ha : ?args = nil -> False |- _ =>
        rewrite (mod_qname_spine _ _ Hp) in Hs; injection Hs; intros; subst; contradiction end ].
  all: try solve [ match goal with
    | Hp : mod_qname ?H = Some _, Hm : member_type _ _ _ ?H _ (mr_term ?A1), Hr : gc_resolve _ _ _ = Some (ge_def _ _ ?A2 _) |- _ =>
        pose proof (mt_glob_type _ _ _ _ _ _ _ _ _ _ _ Hp Hm Hr); subst; functional_nbe_rewrite_clear; reflexivity end ].
  (** An unannotated [let]: the body's type, then the type of the rest. *)
  4:{ assert (A = A0) as <- by eauto. assert (C = C0) as <- by eauto.
      functional_nbe_rewrite_clear. reflexivity. }
  (** Module [let]s and members. *)
  4:{ assert (C = C0) as <- by eauto. functional_nbe_rewrite_clear. reflexivity. }
  4:{ match goal with
      | H1 : member_type _ _ _ ?H ?c (mr_term ?A1), H2 : member_type _ _ _ ?H ?c (mr_term ?A2) |- _ =>
          tryif constr_eq A1 A2 then fail
          else pose proof (proj1 (member_type_functional _ _) _ _ _ _ H1 _ H2) as E; injection E as E; subst A2
      end.
      functional_nbe_rewrite_clear. reflexivity. }
  4,5: exfalso; match goal with Hn : me_noargs ?H, Hs : modexp_spine ?H = _, Ha : _ = nil -> False |- _ =>
         apply Ha, (me_noargs_spine _ _ _ _ Hn Hs) end.
  4:{ match goal with Hs1 : modexp_spine ?H = _, Hs2 : modexp_spine ?H = _ |- _ =>
        rewrite Hs1 in Hs2; injection Hs2; intros; subst end; eauto. }
  - assert (Typeⁿ@i = Typeⁿ@i0) as [= <-] by intuition.
    assert (Typeⁿ@j = Typeⁿ@j0) as [= <-] by intuition.
    reflexivity.
  - assert (Πⁿ A B = Πⁿ A0 B0) as [= <- <-] by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (C = C0) as <- by intuition.
    functional_nbe_rewrite_clear.
    reflexivity.
  - assert (A = A0) as <- by mauto using ctx_lookup_functional.
    functional_nbe_rewrite_clear.
    reflexivity.
  (** Globals are resolved by a function, so both derivations read the same
      type. *)
  - assert (A = A0) as <- by congruence.
    functional_nbe_rewrite_clear.
    reflexivity.
Qed.

#[local]
Hint Resolve functional_alg_type_infer : mctt.

End Fixed_GCtx.

Ltac functional_alg_type_infer_rewrite_clear1 :=
  let tactic_error o1 o2 := fail 3 "functional_alg_type_infer equality between" o1 "and" o2 "cannot be solved by mauto" in
  match goal with
  | H1 : (?Γ ⊢a ?M ⟹ ?A1), H2 : (?Γ ⊢a ?M ⟹ ?A2) |- _ =>
      clean replace A2 with A1 by first [solve [mauto 2 using functional_alg_type_infer] | tactic_error A2 A1]; clear H2
  end.
Ltac functional_alg_type_infer_rewrite_clear := repeat functional_alg_type_infer_rewrite_clear1.

Section Fixed_GCtx.
  Context {GC : GCtx}.

Lemma alg_type_sound :
  (forall {Γ A M}, Γ ⊢a M ⟸ A -> ⊢ Γ -> forall i, Γ ⊢ A : Type@i -> Γ ⊢ M : A) /\
    (forall {Γ A M}, Γ ⊢a M ⟹ A -> ⊢ Γ -> Γ ⊢ M : A) /\
    (forall {Γ Ψ}, Γ ⊢aˣ Ψ -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ˣ Ψ ≈ Ψ) /\
    (forall {Γ U}, Γ ⊢aᵘ U -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) /\
    (forall {Γ H}, Γ ⊢aᵐ H -> ⊢ Γ -> gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H).
Proof.
  apply alg_type_mut_ind; intros; try mautosolve 4.
  (** An unannotated [let]: the type its body infers is a type. *)
  8:{ assert (HM : Γ ⊢ M : A) by eauto.
      assert (exists i, Γ ⊢ (A : exp) : Type@i) as [i HA] by (gen_presups; eauto 2).
      assert (⊢ Γ ▸ (A : exp) ≔ M) by mauto 3.
      assert (Γ ▸ (A : exp) ≔ M ⊢ B : C) by eauto.
      assert (exists j, Γ ▸ (A : exp) ≔ M ⊢ C : Type@j) as [j HCj] by (gen_presups; eauto 2).
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCj (wf_sub_single_def _ _ _ _ _ _ HA HM)) as HCs.
      assert (Γ ⊢ C[Id,,M] ≈ D : Type@j) as <- by mauto 3 using soundness_ty'.
      eapply wf_let; [ exact HA | exact HM | eassumption | solve_let_ann ]. }
  (** Module [let]s and members. *)
  8:{ assert (HU : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) by eauto.
      assert (⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
      assert (Γ ▹ₘ U ⊢ B : C) by eauto.
      assert (exists j, Γ ▹ₘ U ⊢ C : Type@j) as [j HCj] by (gen_presups; eauto 2).
      pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCj (wf_sub_single_mod _ _ _ _ HU)) as HCs.
      assert (Γ ⊢ C[Id ,,ₘ me_lit U] ≈ D : Type@j) as <- by mauto 3 using soundness_ty'.
      eapply wf_let_mod; eauto. }
  8:{ match goal with Hm : member_type _ _ _ _ _ (mr_term _) |- _ => rename Hm into Hmt end.
      assert (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) by eauto.
      destruct (proj1 member_wf _ _ _ _ Hmt HH ltac:(intros; discriminate)) as ([i HA] & HMu & _); cbn [mres_ty] in *.
      destruct (HMu eq_refl) as (M & HMe & HMt).
      assert (Γ ⊢ A ≈ B : Type@i) as <- by mauto 3 using soundness_ty'.
      eapply wf_mem; [ eassumption | exact HH | exact Hmt | exact HA | exact HMe | exact HMt ]. }
  8:{ assert (Γ ⊢ apps (member_ref R (pre ++ x :: nil)) args : A) by eauto.
      assert (exists j, Γ ⊢ A : Type@j) as [j] by (gen_presups; eauto 2).
      eapply wf_mem_app; eauto. }
  (** Extensions, units and module expressions. *)
  10:{ match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
         pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end.
       eapply wf_ext_eq_ass; [ eauto | eauto | eapply wf_exp_eq_refl; eauto | eauto ]. }
  10:{ match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
         pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end.
       assert (Ψ ++ Γ ⊢ A : Type@i) by eauto.
       assert (Ψ ++ Γ ⊢ M : A) by eauto.
       eapply wf_ext_eq_def;
         [ eauto | eauto | eapply wf_exp_eq_refl; eauto | eauto | eapply wf_exp_eq_refl; eauto | eauto | eauto ]. }
  10:{ match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
         pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end.
       eapply wf_ext_eq_mod; eauto. }
  10:{ match goal with HΓ : ⊢ ?G, Hx : ⊢ ?G -> wf_ext_eq _ _ ?G ?P ?P |- _ =>
         pose proof (ext_eq_ctx_left _ _ _ _ _ (Hx HΓ)) as HΨ; pose proof (Hx HΓ) as HXe end.
       eapply wf_unit_eq_alias; eauto. }
  10:{ match goal with Hm : member_type _ _ _ _ nil (mr_mod _) |- _ => rename Hm into Hmt end.
       assert (HH : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵐ H ≈ H) by eauto.
       destruct (proj1 member_wf _ _ _ _ Hmt HH ltac:(intros; discriminate)) as ([i HA] & _); cbn [mres_ty] in HA.
       match goal with Hv : tele_view _ = Some _ |- _ => destruct (tele_view_wf _ _ _ _ _ HA Hv) as (_ & HB & _) end.
       assert (Γ ⊢ N : B) by eauto.
       eapply wf_me_app; eauto using wf_exp_eq_refl. }
  - assert (Γ ⊢ M : A) by mauto 3.
    assert (exists i, Γ ⊢ A : Type@i) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Type@(max i j)) by mauto 3 using lift_exp_max_right.
    assert (Γ ⊢ B : Type@(max i j)) by mauto 3 using lift_exp_max_left.
    assert (Γ ⊢ A ⊆ B) by mauto 2 using alg_subtyping_sound.
    mauto 3.
  - assert (Γ ⊢ ℕ : Type@0) by mauto 2.
    assert (⊢ Γ ▹ ℕ) by mauto 2.
    assert (Γ ▹ ℕ ⊢ A : Type@i) by mauto 2.
    assert (⊢ Γ ▹ ℕ ▹ A) by mauto 3.
    assert (Γ ⊢ M : ℕ) by mauto 2.
    assert (Γ ⊢ A[Id,,zero] : Type@i) by mauto 3.
    assert (Γ ▹ ℕ ▹ A ⊢ A[Wk ⨟ Wk,,succ #1] : Type@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ B : Type@i) as <- by mauto 4 using soundness_ty'.
    mauto 4.
  - assert (Γ ⊢ ⊥ : Type@0) by mauto 2.
    assert (⊢ Γ ▹ ⊥) by mauto 2.
    assert (Γ ▹ ⊥ ⊢ A : Type@i) by mauto 2.
    assert (Γ ⊢ M : ⊥) by mauto 2.
    assert (Γ ⊢ A[Id,,M] : Type@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ B : Type@i) as <- by mauto 4 using soundness_ty'.
    mauto 4.
  - assert (Γ ⊢ A : Type@i) by mauto 2.
    assert (⊢ Γ ▹ A) by mauto 3.
    mauto 3.
  - assert (Γ ⊢ A : Type@i) by mauto 2.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ⊢ A ≈ C : Type@i) by mauto 2 using soundness_ty'.
    assert (Γ ▹ A ⊢ M : B) by mauto 2.
    assert (exists j, Γ ▹ A ⊢ B : Type@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ Π A B ≈ Π C B : Type@(max i j)) as <- by mauto 3.
    mauto 3.
  - assert (Γ ⊢ M : Π A B) by mauto 2.
    assert (exists i, Γ ⊢ Π A B : Type@i) as [i] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Type@i /\ Γ ▹ (A : exp) ⊢ B : Type@i) as [] by mauto 3.
    assert (Γ ⊢ N : A) by mauto 2.
    assert (Γ ⊢ B[Id,,N] ≈ C : Type@i) as <- by mauto 4 using soundness_ty'.
    mauto 3.
  - assert (Γ ⊢ A : Type@i) by mauto 2.
    assert (Γ ⊢ M : A) by mauto 2.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢ B : C) by mauto 2.
    assert (exists j, Γ ▸ A ≔ M ⊢ C : Type@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ C[Id,,M] : Type@j) by mauto 3.
    assert (Γ ⊢ C[Id,,M] ≈ D : Type@j) as <- by mauto 3 using soundness_ty'.
    mauto 3.
  - assert (Γ ⊢ #x : A) by mauto 2.
    assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 2.
    assert (Γ ⊢ A ≈ B : Type@i) as <- by mauto 2 using soundness_ty'.
    mauto 3.
  (** The resolution premise of [wf_mem_glob] is the same function call, so
      the declarative rule applies directly; [soundness_ty'] relates the
      inferred normal form to the declarative type. *)
  - assert (Γ ⊢ a_mem H x : A) by mauto 3.
    assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 3 using wf_glob_typ.
    assert (Γ ⊢ A ≈ C : Type@i) as <- by mauto 2 using soundness_ty'.
    mauto 3.
Qed.

Lemma alg_type_check_sound : forall {Γ i A M},
    Γ ⊢a M ⟸ A ->
    ⊢ Γ ->
    Γ ⊢ A : Type@i ->
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
Proof. intros; eapply (proj2 (proj2 (proj2 (proj2 alg_type_sound)))); eassumption. Qed.

Lemma alg_type_infer_normal : forall {Γ A A' M},
    ⊢ Γ ->
    Γ ⊢a M ⟹ A ->
    nbe_ty_f Γ A A' ->
    A = A'.
Proof.
  intros * ? Hinfer Hnbe. gen A'.
  assert (Γ ⊢ M : A) by mauto 3 using alg_type_infer_sound.
  induction Hinfer; intros;
    try (dir_inversion_clear_by_head nbe_ty;
         dir_inversion_by_head eval_exp; subst;
         dir_inversion_by_head read_typ; subst;
         reflexivity).
  - assert (Γ ⊢ ℕ : Type@0) by mauto 3.
    assert (Γ ⊢ M : ℕ) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▹ ℕ) by mauto 3.
    assert (Γ ▹ ℕ ⊢ A : Typeⁿ@i) by mauto 3 using alg_type_infer_sound; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ ⊥ : Type@0) by mauto 3.
    assert (Γ ⊢ M : ⊥) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▹ ⊥) by mauto 3.
    assert (Γ ▹ ⊥ ⊢ A : Typeⁿ@i) by mauto 3 using alg_type_infer_sound; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ A : Typeⁿ@i) by mauto 3 using alg_type_infer_sound.
    assert (Γ ⊢ A ≈ C : Type@i) by mauto 3 using soundness_ty'.
    assert (Γ ▹ A ⊢ M : B) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ A ⊢ B : Type@j) as [j] by (gen_presups; eauto 2).
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
    assert (exists i, Γ ⊢ Π A B : Type@i) as [i] by (gen_presups; eauto 2).
    assert (Γ ⊢ A : Type@i /\ Γ ▹ (A : exp) ⊢ B : Type@i) as [] by mauto 3.
    assert (Γ ⊢ N : A) by mauto 3 using alg_type_check_sound.
    assert (Γ ⊢ B[Id,,N] : Type@i) by mauto 3; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ A : Typeⁿ@i) by mauto 3 using alg_type_infer_sound.
    assert (Γ ⊢ M : A) by mauto 3 using alg_type_check_sound.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢ B : C) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▸ A ≔ M ⊢ C : Type@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ C[Id,,M] : Type@j) by mauto 3; (f_equiv; mautosolve 4).
  - assert (Γ ⊢ M : A) by mauto 3 using alg_type_infer_sound.
    assert (exists i, Γ ⊢ (A : exp) : Type@i) as [i] by (gen_presups; eauto 2).
    assert (⊢ Γ ▸ (A : exp) ≔ M) by mauto 2.
    assert (Γ ▸ (A : exp) ≔ M ⊢ B : C) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▸ (A : exp) ≔ M ⊢ C : Type@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ C[Id,,M] : Type@j) by mauto 3; (f_equiv; mautosolve 4).
  - assert (HU : gc_deps ⍮ gc_stack ⍮ Γ ⊢ᵘ U ≈ U) by (eapply alg_unit_sound; eassumption).
    assert (⊢ Γ ▹ₘ U) by (apply wf_ctx_extend_mod; exact HU).
    assert (Γ ▹ₘ U ⊢ B : C) by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ₘ U ⊢ C : Type@j) as [j HCj] by (gen_presups; eauto 2).
    pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCj (wf_sub_single_mod _ _ _ _ HU)); (f_equiv; mautosolve 4).
  - match goal with Hm : member_type _ _ _ _ _ (mr_term _) |- _ => rename Hm into Hmt end.
    destruct (proj1 member_wf _ _ _ _ Hmt ltac:(eapply alg_modexp_sound; eassumption) ltac:(intros; discriminate))
      as ([i HA] & _); cbn [mres_ty] in HA.
    (f_equiv; mautosolve 4).
  - eapply IHHinfer; [ assumption | mauto 3 using alg_type_infer_sound | assumption ].
  - assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 2; (f_equiv; mautosolve 4).
  (** A global infers the normal form of a type of the ambient context, so
      [idempotent_nbe_ty] closes it; that it is a type is [wf_glob_typ]. *)
  - assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 3 using wf_glob_typ.
    (f_equiv; mautosolve 4).
Qed.

Hint Resolve alg_type_infer_normal : mctt.

Lemma alg_type_check_typ_implies_alg_type_infer_typ : forall {Γ A i},
    ⊢ Γ ->
    Γ ⊢a A ⟸ Type@i ->
    exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i.
Proof.
  intros * ? Hcheck.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' ? Hnbe1 Hnbe2 Hnfsub]; subst.
  replace A' with A'' in * by (symmetry; mauto 3).
  inversion Hnbe2; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  inversion Hnfsub; subst; [contradiction |].
  firstorder.
Qed.

Hint Resolve alg_type_check_typ_implies_alg_type_infer_typ : mctt.

Lemma alg_type_check_pi_implies_alg_type_infer_pi : forall {Γ M A B i},
    ⊢ Γ ->
    Γ ⊢ Π A B : Type@i ->
    Γ ⊢a M ⟸ Π A B ->
    exists A' B', Γ ⊢a M ⟹ Πⁿ A' B' /\ Γ ⊢ A' ≈ A : Type@i /\ Γ ▹ A ⊢a B' ⊆ B.
Proof.
  intros * ? ? Hcheck.
  assert (Γ ⊢ A : Type@i /\ Γ ▹ A ⊢ B : Type@i) as [] by mauto 3.
  inversion Hcheck as [? A' ? ? Hinfer Hsub]; subst.
  inversion Hsub as [? ? ? A'' C Hnbe1 Hnbe2 Hnfsub]; subst.
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
  assert (exists j, Γ ⊢ Π A0 B0 : Type@j) as [j] by (gen_presups; eauto 2).
  assert (Γ ⊢ A0 : Type@j /\ Γ ▹ (A0 : exp) ⊢ B0 : Type@j) as [] by mauto 3.
  do 2 eexists.
  assert (nbe_ty_f Γ A A0) by mauto 3.
  assert (Γ ⊢ A ≈ A0 : Type@i) by mauto 3 using soundness_ty'.
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
    Γ ⊢ A ≈ A' : Type@i ->
    Γ ⊢a M ⟸ A'.
Proof.
  mauto 3.
Qed.

Hint Resolve alg_type_check_conv : mctt.

Lemma nbe_ty_pi_inv : forall Γ B C W, nbe_ty_f Γ (Π B C) W ->
    exists B' C', W = Πⁿ B' C' /\ nbe_ty_f Γ B B'.
Proof.
  intros * Hnbe.
  inversion Hnbe; subst.
  dir_inversion_by_head eval_exp; subst.
  dir_inversion_by_head read_typ; subst.
  do 2 eexists; split; [ reflexivity | econstructor; eassumption ].
Qed.

(** ** Unannotated Definitions

    The number of unannotated [let]s in a term, the measure of the outer
    induction of completeness: the body of an unannotated [let] is checked in
    a context refined to the type its definiens infers, by a derivation which
    is not a subderivation, but whose subject has fewer of them. *)
Fixpoint exp_lets (M : exp) : nat :=
  match M with
  | a_succ M => exp_lets M
  | a_natrec A MZ MS M => exp_lets A + exp_lets MZ + exp_lets MS + exp_lets M
  | a_exfalso A M => exp_lets A + exp_lets M
  | a_pi A B => exp_lets A + exp_lets B
  | a_fn A M => exp_lets A + exp_lets M
  | a_app M N => exp_lets M + exp_lets N
  | a_let b B => bnd_lets b + exp_lets B
  | a_mem H _ => modexp_lets H
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
  | md_body Φ => gmod_lets Φ
  | md_alias E => modexp_lets E
  end
with gmod_lets (Φ : gmod) : nat :=
  match Φ with
  | gm_nil => 0
  | gm_ext Φ _ E => gmod_lets Φ + gentry_lets E
  | gm_open Φ H _ => gmod_lets Φ + modexp_lets H
  end
with gentry_lets (E : gentry) : nat :=
  match E with
  | ge_def _ _ A B => exp_lets A + match B with Some M => exp_lets M | None => 0 end
  | ge_mod _ U => gunit_lets U
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
  induction Φ as [| Φ IH x [b pv A [M |] | pm U] | Φ IH c its ]; cbn; rewrite ?ctx_lets_app; [ lia .. |].
  enough (ctx_lets (List.repeat (ce_ass a_nat) (List.length its)) = 0) by lia.
  induction (List.length its); cbn; auto.
Qed.

Lemma exp_lets_apps : forall M args,
    exp_lets (apps M args) = exp_lets M + List.fold_right (fun N n => exp_lets N + n) 0 args.
Proof. intros M args; revert M; induction args; intros; cbn; [ lia | rewrite IHargs; cbn; lia ]. Qed.

Lemma exp_lets_member_ref : forall ch H, ch <> nil -> exp_lets (member_ref H ch) = modexp_lets H.
Proof.
  induction ch as [| y ch IH]; intros H Hch; [ congruence |].
  destruct ch as [| z ch]; [ reflexivity |].
  change (member_ref H (y :: z :: ch)) with (member_ref (me_mem H y) (z :: ch)).
  rewrite IH by discriminate; reflexivity.
Qed.

Lemma exp_lets_spine : forall H R args pre x,
    modexp_spine H = (R, args, pre) ->
    exp_lets (apps (member_ref R (pre ++ x :: nil)) args) = modexp_lets H.
Proof.
  intros; rewrite exp_lets_apps, exp_lets_member_ref by (destruct pre; discriminate).
  match goal with Hs : modexp_spine _ = _ |- _ => revert R args pre Hs end.
  induction H as [| | H IH y | H IH N | ]; intros R args pre Hs; cbn in Hs |- *;
    try (injection Hs as <- <- <-; cbn; lia).
  - destruct (modexp_spine H) as [[R0 args0] pre0]; injection Hs as <- <- <-; eauto.
  - destruct (modexp_spine H) as [[R0 args0] pre0]; injection Hs as <- <- <-.
    rewrite List.fold_right_app; cbn.
    specialize (IH _ _ _ eq_refl).
    enough (forall l k, List.fold_right (fun N n => exp_lets N + n) k l
                   = List.fold_right (fun N n => exp_lets N + n) 0 l + k) as E by (rewrite E; lia).
    induction l; intros; cbn; [ lia | rewrite IHl; lia ].
Qed.

Ltac lets_bound :=
  repeat match goal with
         | Hs : modexp_spine ?H = (?R, ?args, ?pre)
           |- context [exp_lets (apps (member_ref ?R (?pre ++ ?x :: nil)) ?args)] =>
             rewrite (exp_lets_spine H R args pre x Hs)
         end;
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

(** Completeness, for terms and for the module judgments at once, since a
    unit's body holds terms and a term may hold a unit.  The global context is
    an index of the judgments, so it is fixed for the induction, as in
    [subtyp_spec]. *)
Lemma alg_type_complete_lets : forall n,
  (forall Θ Ξ Γ, wf_ctx Θ Ξ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M ->
     exp_lets M <= n -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack ->
     (ctx_lets Ψ <= n -> Γ ⊢aˣ Ψ) /\ (ctx_lets Ψ' <= n -> Γ ⊢aˣ Ψ')) /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack ->
     (gunit_lets U <= n -> Γ ⊢aᵘ U) /\ (gunit_lets U' <= n -> Γ ⊢aᵘ U')) /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack ->
     (modexp_lets H <= n -> Γ ⊢aᵐ H) /\ (modexp_lets H' <= n -> Γ ⊢aᵐ H')).
Proof.
  intros n; induction n as [n IHn] using lt_wf_ind.
  apply syntactic_wf_mut_ind; intros; try exact I; subst; destruct_let_ann;
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
  all: match goal with |- _ ⊢a _ ⟸ _ =>
         gen_presups; mauto 4 using alg_subtyping_complete, alg_type_check_subtyp | _ => idtac end.
  (** An unannotated [let].  The definiens infers [A'], a subtype of the [A]
      of the derivation, so the body's derivation is moved to [Γ ▸ A' ≔ M] by
      refinement.  That derivation is no subderivation, but its subject has
      fewer unannotated [let]s, which is what the outer induction is for. *)
  9:{ match goal with Hc : Γ ⊢a M ⟸ A |- _ => inversion Hc as [? A' ? ? HMi HMs]; subst end.
      assert (Γ ⊢ M : A') by mauto 3 using alg_type_infer_sound.
      assert (exists k, Γ ⊢ A' : Type@k) as [k HA'] by (gen_presups; eauto 2).
      assert (Γ ⊢ A' : Type@(max i k)) by mauto 3 using lift_exp_max_right.
      assert (Γ ⊢ A : Type@(max i k)) by mauto 3 using lift_exp_max_left.
      assert (Γ ⊢ A' ⊆ A) by mauto 3 using alg_subtyping_sound.
      assert (Γ ▸ A' ≔ M ⊢s Id : Γ ▸ A ≔ M) by (eapply wf_sub_id_extend_def; mauto 3).
      assert (HB' : Γ ▸ A' ≔ M ⊢ B : C) by mauto 3.
      assert (HBa : Γ ▸ A' ≔ M ⊢a B ⟸ C).
      { destruct (IHn (exp_lets B) ltac:(lets_bound)) as (_ & IHt & _).
        eapply IHt; [ exact HB' | reflexivity | reflexivity | apply user_exp_all | lia ]. }
      clear IHn.
      inversion HBa as [? C' ? ? HBi HBs]; subst.
      assert (⊢ Γ ▸ A' ≔ M) by mauto 3.
      assert (Γ ▸ A' ≔ M ⊢ B : C') by mauto 3 using alg_type_infer_sound.
      assert (exists k, Γ ▸ A' ≔ M ⊢ C' : Type@k) as [k1] by (gen_presups; eauto 2).
      assert (exists k, Γ ▸ A ≔ M ⊢ C : Type@k) as [k2] by (gen_presups; eauto 2).
      assert (Γ ▸ A' ≔ M ⊢ C : Type@k2) by mauto 3.
      assert (Γ ▸ A' ≔ M ⊢ C' ⊆ C)
        by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
      assert (Γ ⊢s Id,,M : Γ ▸ A' ≔ M) by (eapply wf_sub_single_def; eassumption).
      assert (Γ ⊢ C'[Id,,M] : Type@k1) by mauto 3.
      assert (exists W, nbe_ty_f Γ C'[Id,,M] W /\ Γ ⊢ C'[Id,,M] ≈ W : Type@k1) as [W []]
        by (eapply soundness_ty; mauto 3).
      assert (Γ ⊢ C'[Id,,M] ⊆ C[Id,,M]) by mauto 3.
      assert (Γ ⊢ W ⊆ C[Id,,M]) by (transitivity C'[Id,,M]; mauto 3).
      econstructor; [ eapply ati_let_infer; eauto | mauto 4 using alg_subtyping_complete ]. }
  (** A module [let], through its body. *)
  10:{ destruct H0 as [HUa _].
       inversion H4 as [? C' ? ? HBi HBs]; subst.
       assert (Γ ▹ₘ U ⊢ B : C') by mauto 3 using alg_type_infer_sound.
       assert (exists k, Γ ▹ₘ U ⊢ C' : Type@k) as [k HCk] by (gen_presups; eauto 2).
       pose proof (wf_sub_single_mod _ _ _ _ H) as Hσ.
       pose proof (sub_preserves_exp _ _ _ _ _ _ _ HCk Hσ) as HC'σ.
       destruct (soundness_ty HC'σ) as [W [HW HWe]].
       assert (Γ ▹ₘ U ⊢ C' ⊆ C)
         by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
       assert (Γ ⊢ C'[Id ,,ₘ me_lit U] ⊆ C[Id ,,ₘ me_lit U]) by mauto 3.
       assert (Γ ⊢ W ⊆ C[Id ,,ₘ me_lit U]) by (transitivity C'[Id ,,ₘ me_lit U]; mauto 3).
       econstructor; [ eapply ati_let_mod; eauto | mauto 4 using alg_subtyping_complete ]. }
  (** A member, at the normal form of its canonical type. *)
  10:{ destruct H2 as [Hm _].
       destruct (soundness_ty H4) as [W [HW HWe]].
       econstructor; [ eapply ati_mem; eauto | mauto 4 using alg_subtyping_complete ]. }
  (** A member of an applied module, as its root's member applied. *)
  10:{ destruct H1 as [Hm _].
       inversion H7 as [? A' ? ? Hi Hs]; subst.
       econstructor; [ eapply ati_mem_app; eauto | exact Hs ]. }
  - econstructor; mauto 3.
    unshelve solve [mauto using alg_subtyping_complete]; constructor.
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists j, Γ ▹ ℕ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (Γ ⊢ A[Id,,M] : Type@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Type@i) as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  - econstructor; mauto 3.
    mauto using alg_subtyping_complete.
  - assert (exists j, Γ ▹ ⊥ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (Γ ⊢ A[Id,,M] : Type@i) by mauto 3.
    assert (Γ ⊢ A[Id,,M] ≈ A[Id,,M] : Type@i) as [? [? _]]%completeness_ty by mauto 3.
    econstructor; mauto using alg_subtyping_complete, soundness_ty'.
  - assert (exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (exists j, Γ ▹ A ⊢a B ⟹ Typeⁿ@j /\ j <= i) as [j' []] by mauto 3.
    assert (max j j' <= i) by lia.
    econstructor; mauto 3 using alg_subtyping_complete.
  - assert (exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (Γ ▹ A ⊢a M ⟸ B) by mauto 3.
    assert (exists B', Γ ▹ A ⊢a M ⟹ B' /\ Γ ▹ A ⊢a B' ⊆ B) as [B' []] by (inversion_clear_by_head alg_type_check; firstorder).
    assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Type@i) as [W []] by mauto 3 using soundness_ty.
    assert (⊢ Γ ▹ A) by mauto 3.
    assert (Γ ▹ A ⊢ M : B') by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ▹ A ⊢ B' : Type@j) as [] by (gen_presups; eauto 2).
    econstructor; mauto 3.
    eapply alg_subtyping_complete.
    eapply wf_subtyp_pi'; mauto 2.
    mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
  - assert (Γ ⊢a M ⟸ Π A B) by mauto 2.
    assert (Γ ⊢a N ⟸ A) by mauto 2.
    assert (exists A' B', Γ ⊢a M ⟹ Πⁿ A' B' /\ Γ ⊢ A' ≈ A : Type@i /\ Γ ▹ A ⊢a B' ⊆ B) as [A' [B' [? []]]] by mauto 3.
    assert (Γ ⊢ M : Πⁿ A' B') by mauto 3 using alg_type_infer_sound.
    assert (exists j, Γ ⊢ Π A' B' : Type@j) as [j] by (gen_presups; eauto 2).
    assert (Γ ⊢ A' : Type@j /\ Γ ▹ (A' : exp) ⊢ B' : Type@j) as [] by mauto 3.
    assert (Γ ⊢ N : A') by mauto 3.
    assert (Γ ⊢ B'[Id,,N] : Type@j) by mauto 3.
    assert (exists W, nbe_ty_f Γ B'[Id,,N] W /\ Γ ⊢ B'[Id,,N] ≈ W : Type@j) as [W []] by (eapply soundness_ty; mauto 3).
    assert (Γ ▹ A ⊢ B' : Type@j) by mauto 4.
    assert (Γ ▹ A ⊢ B' ⊆ B) by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert (Γ ⊢ B'[Id,,N] ⊆ B[Id,,N]) by mauto 3.
    assert (Γ ⊢ W ⊆ B[Id,,N]) by (transitivity B'[Id,,N]; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i) as [j []] by mauto 3.
    assert (⊢ Γ ▸ A ≔ M) by mauto 2.
    assert (Γ ▸ A ≔ M ⊢a B ⟸ C) by mauto 2.
    assert (exists C', Γ ▸ A ≔ M ⊢a B ⟹ C' /\ Γ ▸ A ≔ M ⊢a C' ⊆ C) as [C' []]
        by (inversion_clear_by_head alg_type_check; firstorder).
    assert (Γ ▸ A ≔ M ⊢ B : C') by mauto 3 using alg_type_infer_sound.
    assert (exists k, Γ ▸ A ≔ M ⊢ C' : Type@k) as [k] by (gen_presups; eauto 2).
    assert (exists k', Γ ▸ A ≔ M ⊢ C : Type@k') as [k'] by (gen_presups; eauto 2).
    assert (Γ ▸ A ≔ M ⊢ C' ⊆ C)
      by mauto 4 using alg_subtyping_sound, lift_exp_max_left, lift_exp_max_right.
    assert (Γ ⊢ C'[Id,,M] : Type@k) by mauto 3.
    assert (exists W, nbe_ty_f Γ C'[Id,,M] W /\ Γ ⊢ C'[Id,,M] ≈ W : Type@k) as [W []]
        by (eapply soundness_ty; mauto 3).
    assert (Γ ⊢ C'[Id,,M] ⊆ C[Id,,M]) by mauto 3.
    assert (Γ ⊢ W ⊆ C[Id,,M]) by (transitivity C'[Id,,M]; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  - assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Type@i) as [W []] by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.
  (** Resolution is the same function call in both systems. *)
  - assert (exists i, Γ ⊢ A : Type@i) as [i] by mauto 3 using wf_glob_typ.
    assert (exists W, nbe_ty_f Γ A W /\ Γ ⊢ A ≈ W : Type@i) as [W []]
        by (eapply soundness_ty; mauto 3).
    econstructor; mauto 4 using alg_subtyping_complete.

  (** Extensions. *)
  - constructor.
  - constructor.
  - destruct H0 as [Hl _].
    pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
    destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ H2) as [j [Hj _]].
    econstructor; eauto.
  - destruct H0 as [_ Hr].
    pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
    destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ' H6) as [j' [Hj' _]].
    econstructor; eauto.
  - destruct H0 as [Hl _].
    pose proof (ext_eq_ctx_left _ _ _ _ _ H) as HΨ.
    destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ H2) as [j [Hj _]].
    econstructor; eauto.
  - destruct H0 as [_ Hr].
    pose proof (ext_eq_ctx_right _ _ _ _ _ H) as HΨ'.
    destruct (alg_type_check_typ_implies_alg_type_infer_typ HΨ' H10) as [j' [Hj' _]].
    econstructor; eauto.
  - destruct H0 as [Hl _]; destruct H2 as [HU _]; econstructor; eauto.
  - destruct H0 as [_ Hr]; destruct H4 as [HU' _]; econstructor; eauto.
  (** Units. *)
  - destruct H0 as [Hl _]; destruct (body_shape_refl _ _ H4) as (Hs1 & Hs2 & Hn).
    eapply aunit_body; eauto.
  - destruct H0 as [_ Hr]; destruct (body_shape_refl _ _ H4) as (Hs1 & Hs2 & Hn).
    eapply aunit_body; eauto.
    rewrite <- Hn; assumption.
  - destruct H0 as [Hl _]; destruct H4 as [HE _]; econstructor; eauto.
  - destruct H0 as [_ Hr]; destruct H6 as [HE' _]; econstructor; eauto.
  - destruct H0; assumption.
  - destruct H0; assumption.
  - destruct H0 as [H01 _]; assumption.
  - destruct H2 as [_ H22]; assumption.
  (** Module expressions. *)
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
  - repeat match goal with IH : _ /\ _ |- _ => destruct IH end;
      solve [ assumption | econstructor; eauto | eapply amod_app; eauto ].
Qed.

Lemma alg_type_complete_all :
  (forall Θ Ξ Γ, wf_ctx Θ Ξ Γ -> True) /\
  (forall Θ Ξ Γ A M, Θ ⍮ Ξ ⍮ Γ ⊢ M : A -> Θ = gc_deps -> Ξ = gc_stack -> user_exp M -> Γ ⊢a M ⟸ A) /\
  (forall Θ Ξ Γ A M M', Θ ⍮ Ξ ⍮ Γ ⊢ M ≈ M' : A -> True) /\
  (forall Θ Ξ Γ A A', Θ ⍮ Ξ ⍮ Γ ⊢ A ⊆ A' -> True) /\
  (forall Θ Ξ Γ Ψ Ψ', Θ ⍮ Ξ ⍮ Γ ⊢ˣ Ψ ≈ Ψ' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aˣ Ψ /\ Γ ⊢aˣ Ψ') /\
  (forall Θ Ξ Γ U U', Θ ⍮ Ξ ⍮ Γ ⊢ᵘ U ≈ U' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵘ U /\ Γ ⊢aᵘ U') /\
  (forall Θ Ξ Γ H H', Θ ⍮ Ξ ⍮ Γ ⊢ᵐ H ≈ H' -> Θ = gc_deps -> Ξ = gc_stack -> Γ ⊢aᵐ H /\ Γ ⊢aᵐ H').
Proof.
  repeat split; intros; try exact I.
  - eapply (alg_type_complete_lets (exp_lets M)); eauto.
  - eapply (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)); lia.
  - eapply (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (alg_type_complete_lets (ctx_lets Ψ + ctx_lets Ψ')))))) _ _ _ _ _ H H0 H1)); lia.
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

Corollary alg_type_infer_typ_complete : forall {Γ i A},
    user_exp A ->
    Γ ⊢ A : Type@i ->
    exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i.
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

Hint Resolve alg_type_infer_typ_complete : mctt.

Corollary alg_type_infer_pi_complete : forall {Γ i A},
    user_exp A ->
    Γ ⊢ A : Type@i ->
    exists j, Γ ⊢a A ⟹ Typeⁿ@j /\ j <= i.
Proof.
  mauto 4 using alg_type_check_complete.
Qed.

Hint Resolve alg_type_infer_pi_complete : mctt.

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
Hint Resolve alg_type_infer_typ_complete : mctt.
#[export]
Hint Resolve alg_type_infer_pi_complete : mctt.
