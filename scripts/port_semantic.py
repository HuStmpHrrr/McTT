#!/usr/bin/env python3
"""Port a semantic file from its pre-global-context form: the per-file edits
beyond what [fix_gctx.py] does mechanically, then [fix_gctx.py]."""
import re, subprocess, sys

def rep(s, a, b):
    assert a in s, a[:80]
    return s.replace(a, b)

def ported_names():
    # constants defined inside a [Fixed_GCtx] section: they take the instance first
    import glob
    names = set()
    for f in glob.glob('Core/**/*.v', recursive=True):
        t = open(f).read()
        if 'Section Fixed_GCtx' not in t: continue
        for sec in re.findall(r'Section Fixed_GCtx\.(.*?)End Fixed_GCtx\.', t, re.S):
            names.update(re.findall(r'^\s*(?:#\[[^\]]*\]\s*)?(?:Lemma|Corollary|Theorem|Proposition|Fact|Definition|Fixpoint|Inductive|Record|Equations)\s+([A-Za-z_][\w\']*)', sec, re.M))
    return names

def explicit_apps(s, names):
    return re.sub(r'@([A-Za-z_][\w\']*)(?=\s+[^\s)])', lambda m: '@%s _' % m.group(1) if m.group(1) in names else m.group(0), s)

def mono_apply(s):
    # the monotonicity instance these take is left as a goal by [apply]
    return re.sub(r'\bapply (eval_sub_of_wk|eval_sub_wk_pre)\b(?!;\s*try typeclasses)', r'(apply \1; try typeclasses eauto)', s)

def induction(s):
    s = re.sub(r'induction 1 using per_univ_elem_ind', 'per_univ_elem_induction1', s)
    return re.sub(r'induction (\w+) using per_univ_elem_ind', r'per_univ_elem_induction \1', s)

EDITS = {}

def edit(f):
    def deco(g):
        EDITS[f] = g
        return g
    return deco

@edit('Core/Semantic/PER/Definitions.v')
def _(s):
    return rep(s, "From Mctt.Core.Semantic Require Export Domain Evaluation Readback.",
               "From Mctt.Core.Semantic Require Export Fixed.")

@edit('Core/Semantic/PER/Lemmas.v')
def _(s): return induction(s)

@edit('Core/Semantic/Realizability.v')
def _(s): return induction(s)

@edit('Core/Completeness/LogicalRelation/Definitions.v')
def _(s):
    return rep(s, """    Because a weakening is an operation, related environments are not
    automatically related after it is applied; the semantic judgment for
    weakenings simply demands it.  Stripped of its two context witnesses this is
    just [Proper (R ==> R') (eval_wk φ)], and that is the form the proofs use. *)

Definition rel_wk (φ : wk) (R R' : relation env) : Prop :=
  forall ρ ρ',
    Dom ρ ≈ ρ' ∈ R ->
    Dom ⟪φ⟫ ρ ≈ ⟪φ⟫ ρ' ∈ R'.""", """    Because a weakening is an operation, related environments are not
    automatically related after it is applied; the semantic judgment for
    weakenings simply demands it.  Stripped of its two context witnesses this is
    [Proper (R ==> R') (eval_wk φ)], for a weakening that moves no variable
    down: environments are lists, and that is what makes weakenings compose on
    them ([eval_wk_compose]).  Every weakening the proofs instantiate this at is
    built from [↑] and [wk_q], hence is one. *)

Record rel_wk (φ : wk) (R R' : relation env) : Prop := mk_rel_wk
  { rel_wk_mono : WkMono φ
  ; rel_wk_app :> forall ρ ρ',
      Dom ρ ≈ ρ' ∈ R ->
      Dom ⟪φ⟫ ρ ≈ ⟪φ⟫ ρ' ∈ R' }.""")

@edit('Core/Completeness/LogicalRelation/Lemmas.v')
def _(s):
    s = rep(s, """  unfold rel_wk; split; intros H ρ ρ' Hρ; apply H2; apply H; now apply H1.""",
            """  split; intros [Hm H]; split; auto; intros ρ ρ' Hρ; apply H2; apply H; now apply H1.""")
    s = rep(s, """(** [⟪wk_id⟫ ρ] is [fun x => ρ x], so this is the identity. *)
Lemma rel_wk_id : forall R, rel_wk wk_id R R.
Proof.
  intros R ρ ρ' H. exact H.
Qed.""", """(** [⟪wk_id⟫ ρ] is [ρ], so this is the identity. *)
Lemma rel_wk_id : forall R, rel_wk wk_id R R.
Proof.
  intros R; split; [ apply wk_mono_id |]; intros ρ ρ' H; rewrite !eval_wk_id; exact H.
Qed.""")
    s = rep(s, """  intros * Hψ Hφ ρ ρ' H.
  exact (Hφ _ _ (Hψ _ _ H)).
Qed.""", """  intros * [Hψm Hψ] [Hφm Hφ]; split; [ apply wk_mono_compose; assumption |].
  intros ρ ρ' H; rewrite !eval_wk_compose by assumption.
  exact (Hφ _ _ (Hψ _ _ H)).
Qed.""")
    s = rep(s, """  intros * HΓ HΓA ρ ρ' H.
  invert_per_ctx_env HΓA.
  apply_relation_equivalence.
  destruct H as [? ?].
  eassumption.
Qed.""", """  intros * HΓ HΓA; split; [ apply wk_mono_shift |]; intros ρ ρ' H; rewrite !eval_wk_shift.
  invert_per_ctx_env HΓA.
  apply_relation_equivalence.
  destruct H as [? ?].
  eassumption.
Qed.""")
    s = rep(s, """  intros * [env_relΔ [HΔ [env_relΓ [HΓ Hψ]]]].
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ Hφ ρ ρ' Hρ.
  econstructor; try apply eval_sub_of_wk.
  apply rel_chain_4_of_2; [ solve_chain_PER |].
  exact (Hψ _ _ (Hφ _ _ Hρ)).""", """  intros * [env_relΔ [HΔ [env_relΓ [HΓ [Hψm Hψ]]]]].
  eexists_rel_sub.
  intros Γ' env_rel' HΓ' φ [Hφm Hφ] ρ ρ' Hρ.
  apply mk_rel_sub with (ρσφ := ⟪ψ ⊙ φ⟫ ρ) (ρσ := ⟪ψ⟫ (⟪φ⟫ ρ)) (ρ'σ' := ⟪ψ⟫ (⟪φ⟫ ρ')) (ρ'σ'φ := ⟪ψ ⊙ φ⟫ ρ');
    try apply eval_sub_of_wk; try (apply wk_mono_compose; assumption); try assumption.
  rewrite !eval_wk_compose by assumption.
  apply rel_chain_4_of_2; [ solve_chain_PER |].
  exact (Hψ _ _ (Hφ _ _ Hρ)).""")
    s = rep(s, """  destruct (Hσ _ _ HΓ' _ (rel_wk_compose Hφ Hψ) _ _ Hρ) as [a1 a2 ? a4 Ha1 Ha2 ? Ha4 Ha].""",
            """  destruct (Hσ _ _ HΓ' _ (rel_wk_compose Hφ Hψ) _ _ Hρ) as [a1 a2 ? a4 Ha1 Ha2 ? Ha4 Ha].
  rewrite eval_wk_compose in Ha2 by (eapply rel_wk_mono; eassumption).""")
    s = rep(s, """  destruct (Hσ _ _ HΓ wk_id (rel_wk_id _) _ _ Hρ) as [? ρσ ρ'σ' ? ? ? ? ? Hchain].
  exists ρσ, ρ'σ'.""", """  destruct (Hσ _ _ HΓ wk_id (rel_wk_id _) _ _ Hρ) as [? ρσ ρ'σ' ? ? ? ? ? Hchain].
  rewrite !eval_wk_id in *.
  exists ρσ, ρ'σ'.""")
    s = rep(s, """  pose proof (rel_chain_map _ _ (eval_wk φ) Hφ _ Hchain) as Hchain'.""",
            """  pose proof (rel_chain_map _ _ (eval_wk φ) (rel_wk_app _ _ _ Hφ) _ Hchain) as Hchain'.""")
    s = rep(s, """  pose proof (rel_chain_map _ _ drop_env Hdrop _ Hchain) as Hchain'.""",
            """  assert (Hdrop' : forall ρ ρ', Dom ρ ≈ ρ' ∈ env_relΔA -> Dom ρ↯ ≈ ρ'↯ ∈ env_relΔ)
    by (intros; rewrite <- !eval_wk_shift; apply Hdrop; assumption).
  pose proof (rel_chain_map _ _ drop_env Hdrop' _ Hchain) as Hchain'.""")
    return s

def mono_args(s):
    s = s.replace('(eval_sub_of_wk _ _)', '(eval_sub_of_wk _ _ ltac:(solve_wk_mono))')
    return re.sub(r'\(eval_sub_wk_pre _ _ _ _ (\w+\'?)\)', r'(eval_sub_wk_pre _ _ _ _ ltac:(solve_wk_mono) \1)', s)

@edit('Core/Completeness/SubstitutionCases.v')
def _(s):
    s = induction(s)
    s = rep(s, """  intros ρ ρ' [Htail Hhead].
  apply per_env_extend_intro.
  - exact (Hψ _ _ Htail).""", """  split; [ typeclasses eauto |].
  intros ρ ρ' [Htail Hhead].
  apply per_env_extend_intro; rewrite ?eval_wk_q_zero; rewrite ?eval_wk_q_tail by typeclasses eauto.
  - exact (Hψ _ _ Htail).""")
    s = rep(s, """    by (apply rel_chain_4_of_2; [ solve_chain_PER | exact Hh ]).""",
            """    by (apply rel_chain_4_of_2; [ solve_chain_PER | rewrite <- !(eval_wk_app ψ); exact Hh ]).""")
    s = rep(s, """    [ apply eval_sub_wk_q; eassumption
    | apply eval_sub_q; eassumption
    | apply eval_sub_q; eassumption
    | apply eval_sub_wk_q; eassumption
    | ].""", """    [ apply eval_sub_wk_q; eassumption
    | rewrite <- (eval_wk_app ψ); apply eval_sub_q; eassumption
    | rewrite <- (eval_wk_app ψ); apply eval_sub_q; eassumption
    | apply eval_sub_wk_q; eassumption
    | ].""")
    # what [↑] evaluates to is the tail, as a list
    s = re.sub(r'(\n(\s*)destruct \([^\n]*_ Hshift _ _[^\n]*\]\.)', r'\1\n\2rewrite ?eval_wk_shift in *.', s)
    return s

TAIL = {
    'Core/Completeness/LogicalRelation/Definitions.v': "\n(** A semantic weakening in scope says its weakening moves no variable\n    down. *)\nExisting Class rel_wk.\n#[export] Existing Instance rel_wk_mono.\n\nExisting Class rel_wk_under_ctx.\n\n#[export] Instance rel_wk_under_ctx_mono {GC : GCtx} {Γ φ Δ} (Hφ : Γ ⊨w φ : Δ) : WkMono φ.\nProof. destruct Hφ as [? [? [? [? []]]]]; assumption. Qed.\n" + '\n(** That a weakening moves no variable down: from a semantic weakening in\n    scope, or from how the weakening is built. *)\nLtac solve_wk_mono :=\n  repeat first\n    [ eapply rel_wk_mono; eassumption\n    | apply wk_mono_id | apply wk_mono_shift\n    | apply wk_mono_q | apply wk_mono_compose ].\n',
}

APPEND = {
    'Core/Semantic/PER/Definitions.v': open('/tmp/port_save/Core_Semantic_PER_Definitions.v').read().split("(** [induction H using per_univ_elem_ind] no longer applies")[1],
}

NAMES = ported_names()

for f in sys.argv[1:]:
    subprocess.run(['git', 'checkout', 'HEAD', '--', f], check=True)
    s = open(f).read()
    s = mono_apply(EDITS[f](s) if f in EDITS else induction(s))
    s = explicit_apps(s, NAMES)
    open(f, 'w').write(s)
    subprocess.run(['python3', '../scripts/fix_gctx.py', f], check=True)
    if f in TAIL:
        open(f, 'a').write(TAIL[f])
    if f in APPEND:
        s = open(f).read().rstrip() + "\n\n(** [induction H using per_univ_elem_ind] no longer applies" + APPEND[f]
        open(f, 'w').write(s)
