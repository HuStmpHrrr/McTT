# Porting the Semantic Development to Global Contexts

> **Option B branch:** "The global rules" below (Kripke over module
> substitutions, `GlobalInduction.v`) is replaced by embeddings; see
> [`optionB.md`](optionB.md).

The semantic files (`Core/Semantic/PER*`, `Core/Completeness`, `Core/Soundness`,
…), the algorithmic system and the extraction were written before judgments
and evaluation took a global context `Θ ⍮ Ξ`.  All of them are ported; these
are the conventions they follow.

## The conventions

* **The global context is an instance.** `Class GCtx := { gc_deps; gc_stack }`
  (`Core/Syntactic/GlobalCtx.v`).  A ported file's commands live in
  `Section Fixed_GCtx. Context {GC : GCtx}. … End Fixed_GCtx.` blocks, and use
  the short forms of `Core/Semantic/Fixed.v` (module `Fixed_Notations`):
  `Γ ⊢ M : A`, `⊢ Γ`, `⟦ M ⟧ ρ ↘ m`, `$| m & n |↘ r`, `Rnf m in s ↘ M`, …,
  all at `gc_deps gc_stack`.  `initial_env`, `nbe`, `nbe_ty` at the fixed
  context are `initial_env_f`, `nbe_f`, `nbe_ty_f`.
* **Context subtyping's short form is `Δ ⊆ Γ`**, not `⊢ Δ ⊆ Γ`: the latter does
  not parse next to `⊢ Γ` and the long forms.
* **The long forms `⊢ Θ ⍮ Ξ ⍮ Γ` do not parse once `Fixed_Notations` is
  imported.** Write the constant (`wf_ctx Θ Ξ Γ`) where another global context
  is meant.
* **Environments are lists** (`env := list domain`), with a total lookup
  `env_var ρ x` (a coercion: `ρ x`), `zeroᵈ` past the end, defined by recursion
  on the index so that `ρ↯ x` is `ρ (S x)` and `(ρ ↦ a) 0` is `a` by
  conversion.  `env_eq` is pointwise equality.
* **`⟦ σ ⟧s ρ ↘ ρσ` holds at every index**: `∀ x, ⟦ σ x ⟧ ρ ↘ ρσ x`.
* **`⟪φ⟫ ρ` is a list** — `ρ` looked up after `φ`, over the variables `φ`
  keeps.  For an order-preserving `φ` (class `WkMono`, with instances for
  `wk_id`, `↑`, `wk_q`, `⊙`), these hold as *list equations*: `eval_wk_id`,
  `eval_wk_shift : ⟪↑⟫ ρ = ρ↯`, `eval_wk_q_tail`, `eval_wk_q_zero`,
  `eval_wk_compose`, and pointwise `eval_wk_app : (⟪φ⟫ ρ) x = ρ (φ x)`.  They
  used to be conversions; where an old proof relied on that, rewrite.
* **Semantic weakenings are order preserving**: `rel_wk` is a record
  `{ rel_wk_mono : WkMono φ ; rel_wk_app :> … }`, and `rel_wk`,
  `rel_wk_under_ctx` are classes, so a hypothesis of either supplies the
  `WkMono` instance.  `eval_sub_of_wk`, `eval_sub_wk_pre`, `eval_wk_compose` take
  it by instance resolution; after `apply` of one of them the instance may be
  left as a goal — close it with `typeclasses eauto`.  `rewrite` with them needs
  `by typeclasses eauto` (or `by assumption`).
* **`Θ Ξ` are implicit** in the evaluation, readback and NbE lemmas.
* **Explicit applications `@X …` of a ported constant take `GC` first**: add
  a `_`.
* **`induction H using per_univ_elem_ind` no longer works** (the instance is
  an argument of the major premise that is not an index of the eliminator);
  use `per_univ_elem_induction H` / `per_univ_elem_induction1`
  (`Core/Semantic/PER/Definitions.v`), which emulate it, including the `IHH`
  name of the Π-case hypothesis.  The gluing eliminator `glu_univ_elem_ind` has
  the same problem and needs the same treatment.
* **In a section, `Ltac` is local**, so tactics are defined between sections;
  hints and instances are local inside and re-exported after `End`;
  `#[global] Arguments` stays inside.

## Building

* Build one file: `make -f CoqMakefile.mk Core/…/X.vo` from `theories/`.  Use
  the rocq MCP to step through a failing proof.
* The mutual block's global context is an *index*, so `induction` on a
  judgment at `gc_deps gc_stack` abstracts it: `remember` it first (see
  `subtyp_spec`), or state the lemma at explicit `Θ Ξ`.

## The global rules (glob, param, δ)

The models are not monotone under growing the global context: both break at Π
(`AGENT/experiments/extension_invariance.md`, `AGENT/experiments/soundness_alt.md`).  Instead:

* `Core/Completeness/ModuleCases.v`: a judgment is valid when it is valid, at the
  fixed-context sense, after every *sound* module substitution (`sem_msub`: the
  premises of `msub_preserves_wf` plus validity at the target of what it puts
  in).  `kripke_fundamental` proves this for every rule; composition needs only
  the syntactic half of the first step.
* `Core/Syntactic/GlobalInduction.v`: the model-independent part — `syn_msub`,
  embeddings (`Emb`), and `global_induction`, over a validity predicate and a
  sound-substitution predicate.  By age: every item is typed where it was inserted, in a
  context of older items only (`ins_typed`; a truncated level for filed units;
  a telescope suffix for parameters), and embeds into the final context
  (`Emb`).
* Its instances: `gctx_sem` (`Core/Completeness/GlobalCases.v`, PER model) and
  `gctx_glu` (`Core/Soundness/GlobalCases.v`, gluing model, with
  `Core/Soundness/ModuleCases.v`).  Both fundamental theorems are then the old
  ones at the identity.
* Canonical forms and consistency hold at a *transparent* global context
  (`gc_transparent`: every definition transparent with a body, no open frame
  with parameters), where no global or parameter is a neutral
  (`Core/Semantic/Transparency.v`: `nbe_clean`); an axiom is a closed neutral.

## What the driver needs

`Frontend/Elaborator.v` hands back a `gunit` and one obligation per `eval`,
each `(gstack * exp * option typ)` — the stack of frames as they stood at that
point.  Nothing proves that stack well formed (the elaborator has no soundness
proof yet), so `Entrypoint.v` has to *check* it: a decision procedure for
`⊢ Γ`, `⊢e`, `⊢m`, `⊢u` and `⊢g`, built on `Extraction/TypeCheck.v`
(`type_infer` plus `get_level_of_type_nf` decides "is a type").  Checking the
unit as well catches the definitions that follow the last `eval`.
