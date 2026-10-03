# Simplifying the elaborator (exploration, `wip/elab-simplify`)

Status: prototype done and proved against the **current core**, with no core
change beyond the surface syntax `Cst`. Everything below "Options" is a
proposal with its cost, not implemented.

## 1. The idea

Today's elaborator keeps three kinds of state and three searches: local
binders (`lbind`, `lb_lookup`), a stack of open frames (`sframe`, `ustate`,
`fr_lookup`, `preapp`) and per-frame import scopes (`sscope`, `starget`,
`alias_lookup`). The searches have no priority between them, so the spec needs
the invariant `sf_wf` (one binding per name per frame) to be functional, and
the proof threads it everywhere.

The prototype replaces all of that by **one scope: a list of entries,
innermost first**, and **first-match lookup**:

```coq
Inductive ent : Set :=
| en_var  : string -> ent           (* a core binder: λ, Π, rec, let, a parameter, a local-body entry *)
| en_mem  : string -> path -> ent   (* a member of an open frame, by absolute path *)
| en_as   : string -> modexp -> ent (* import E as y *)
| en_use  : string -> modexp -> ent (* import E use (n) *)
| en_unit : fpath -> ent.           (* import X::Y: the unit may be named *)

Definition bound (S : list ent) (x : string) (k : nat) (e : ent) (n : nat) : Prop :=
  exists S1 S2, S = S1 ++ e :: S2 /\ ent_name e = Some x /\ ~ In x (names S1) /\
           k = binders S1 /\ n = binders S2.
```

Two facts make this enough:

* **Pre-application is positional.** Members are declared at frame level,
  under no local binder, so the binders *outside* a member's entry are exactly
  the parameters of its frame and the frames enclosing it, i.e. the telescope
  it is generalized over. A use with `k` binders inside the entry and `n`
  outside is `apps (a_glob p) (vars_desc k n)`. `preapp`, `tele`, the `off`
  bookkeeping of `fbind` and `fr_binds` all disappear.
* **No frame stack.** `elab_cmd` elaborates the body of `module x … where body
  end` by recursion where it stands, then binds `x`. Frames are just the
  segment `F` of the scope that the current module has bound (needed for the
  freshness check only). `ustate`, `us_open`, `us_close`, `us_top`,
  `"unbalanced modules"` and `"no module to close"` disappear.

The spec (`ElabSpec.v`) is a homomorphism on every constructor except the two
name rules (`sel_var`, `selm_var`: `bound` + `den_term`/`den_mod`) and
`selm_glob` (`In (en_unit fq) S`). Commands are `scmd fp ch O F c F' c'` and
`scmds` (one mutual pair), leading imports `simports`, the unit `elab_spec`.
No invariant: freshness is a premise `fresh x F := ~ In x (names F)`, not a
property the proof must preserve.

## 2. What moves where

| Responsibility | Today | Prototype | Core cost |
|---|---|---|---|
| Names → de Bruijn | `lb_lookup`, `fr_lookup`, `alias_lookup`; three searches, unordered, need `sf_wf` | one `lookup` over `list ent`, first match (`bound`) | 0 |
| Term vs module by position | `sel`/`selm` | same | 0 |
| Pre-application of open-frame members | `preapp`, `tele`, `vars_desc off (tele …)`, offsets in `fbind` | `vars_desc k n` read off the entry's position | 0 (removal: option O6, large) |
| Open frames | `sframe` stack in `ustate`, open/close | none; body elaborated by structural recursion | 0 |
| `import … as y` / `use (n)` | `sscope`, `starget`, `wk_starget`, `ss_add`, `ibinds`, `use_binds` over a separate alias list | entries `en_as`/`en_use`, weakened by `k` at use (`mwk E k`) | 0 (move: options O2/O3) |
| Unit reachability | `ss_units` in every frame scope + leading scope, `unit_in` | `en_unit fq` entry, `In (en_unit fq) S` | 0 (move: option O5) |
| One binding per name per frame | `sf_wf`/`ss_wf` invariants, `NoDup` over aliases ++ members ++ params, preservation lemmas | premise `fresh x F`; no invariant | 0 (move: option O4) |
| `module A.B` | `open_path`, `path_unit`, `sc_mod_path`, `sb_mod_path`, `spath`, `path_unit_iff` | **parser** action `Cst.c_mod_dotted`; `Cst.c_mod` takes a `string` | 0 |
| Imports in local bodies | `ltarget`, `libinds`, `lb_alias`, `sb_import` | rejected: `"a local module has no imports"` | 0 (`gm_check`/`bc_import` now dead in the core: option O1) |
| `eval` in local bodies | `sb_eval`, `sb_eval_typ` | rejected: `"a local module has no evals"` | 0 (same) |
| Privacy | not checked | not checked | — |
| `Resolve.v` | `index_of` (frame params) + `ImportDepth` (unused anywhere) | deleted | 0 |

## 3. Changes made

* `Core/Syntactic/Syntax.v` (`Cst` only):
  ```coq
  | c_mod : string -> list (string * obj) -> mdef -> cmd      (* was: list string -> … *)
  Definition c_mod_dotted (x : string) (rev_pre : list string) ps md : cmd :=
    List.fold_left (fun c y => c_mod y nil (md_where (c :: nil))) rev_pre (c_mod x ps md).
  ```
* `Frontend/Parser.vy`: `path` returns `(last segment, earlier segments
  reversed)`, so it is non-empty by its type; `MODULE path mdecl` builds
  `c_mod_dotted`. The automaton is unchanged (same productions), so
  `parserMessages.messages` is unchanged.
* `Frontend/{Elaborator,ElabSpec,ElabCorrect,ElabExamples}.v` rewritten;
  `Frontend/Resolve.v` deleted.
* `driver/PrettyPrinter.ml`: `Coq_c_mod` takes a name.
* `lib/Polynomials.mctt`, `examples/ModuleForms.mctt`: the import in a local
  body is removed (the member is named through the module instead). The
  expectations change accordingly; the test "a local body with an import"
  becomes two rejection tests.

Every other example in `ElabExamples.v` (pre-application, `ModuleParam`,
`ImportUse`, `multi/Main`, shadowing, every one-binding rejection and its
message, aliases, `let`) elaborates to **exactly the same core unit** as
before; they were kept verbatim apart from the `c_mod` constructor.

## 4. Examples (surface, today's core, prototype's core)

`⟨T.M⟩` is `me_path (p_abs ["T"] ["M"])`, `T.M.b` is `a_glob (p_abs ["T"]
["M"; "b"])`, flags of `cc_def` are omitted.

**Pre-application inside `module U (A)`.**
```
module U (A : Type@0) where
  def a : Type@0 := A end
  module M (B : Type@0) where
    def b : Type@0 := B end
    eval a   eval b   eval fun (x : Nat) -> b
  end
  eval M.b Nat
end
```
Today and prototype (identical):
```
cc_def a Type@0 #0 ;
cc_mod M (⋅ ▹ Type@0)
  [ cc_def b Type@0 #0 ; cc_eval (U.a $ #1) ; cc_eval (U.M.b $ #1 $ #0) ;
    cc_eval (λ ℕ (U.M.b $ #2 $ #1)) ] ;
cc_eval (a_mem (me_app ⟨U.M⟩ #0) b $ ℕ)
```
Prototype derivation of `eval a`: the scope is `B, a ↦ U.a, A`; `a` has one
binder inside (`B`) and one outside (`A`), so `U.a $ vars_desc 1 1 = U.a $ #1`
(`ElabExamples.a_preapplied`).

**`import X as Y`** and **`import X use (n)`**, leading and in a frame:
```
import L::X as Y
import L::X use (n)
module T where
  module M (B : Type@0) where
    module K where def k : Nat := 0 end end
    import K as Z
    import K use (k)
    eval fun (z : Nat) -> Y.f Z.k (n k)
  end
end
```
Today and prototype (identical):
```
leading: cc_import (Some L::X) ⟨L::X⟩ [] ; cc_import (Some L::X) ⟨L::X⟩ [n]
cc_mod M (⋅ ▹ Type@0)
  [ cc_mod K ⋅ [cc_def k ℕ zero] ;
    cc_import None (me_app ⟨T.M.K⟩ #0) [] ;
    cc_import None (me_app ⟨T.M.K⟩ #0) [k] ;
    cc_eval (λ ℕ (a_mem ⟨L::X⟩ f $ a_mem (me_app ⟨T.M.K⟩ #1) k
                   $ (a_mem ⟨L::X⟩ n $ a_mem (me_app ⟨T.M.K⟩ #1) k))) ]
```
`Z` and `k` are `en_as`/`en_use` entries holding `me_app ⟨T.M.K⟩ #0`; under
the `λ` they are weakened by one (`#1`). With options O2/O3 the outputs
would be (not implemented):
```
cc_import None (me_app ⟨T.M.K⟩ #0) [] ; cc_alias Z (private) ⋅ (me_app ⟨T.M.K⟩ #0) ;
cc_import None (me_app ⟨T.M.K⟩ #0) [k] ; cc_use (me_app ⟨T.M.K⟩ #0) k ;
cc_eval (λ ℕ (… a_mem (me_app ⟨T.M.Z⟩ #1) k … (T.M.k $ #1)))
```
i.e. `Z` and `k` become ordinary members (`en_mem`), pre-applied like any
other.

**A dotted module.**
```
module A.B (X : Type@0) where abstract def y : Type@0 := X end end
eval A.B.y Nat
```
Today: the elaborator opens `A`, then `B`. Prototype: the parser produces
`c_mod "A" nil (md_where [c_mod "B" [(X, Type@0)] …])`; the core output is
identical:
```
cc_mod A ⋅ [cc_mod B (⋅ ▹ Type@0) [cc_def y Type@0 #0]] ;
cc_eval (a_mem (me_mem ⟨T.A⟩ B) y $ ℕ)
```

**A local module.**
```
eval let module L (A : Type@0) where
       def x : A -> A := fun (a : A) -> a end
       module N where def y : Nat := 0 end end
       def z : Nat := N.y end
     end in L.x end
```
Today and prototype (identical):
```
cc_eval (ℓₘ (gu_mk (⋅ ▹ Type@0) (md_body
           (Φ ⊳ x ↦ ge_def (Π #0 #1) (λ #0 #0)
              ⊳ N ↦ ge_mod (gu_mk ⋅ (md_body (⋅ ⊳ y ↦ ge_def ℕ zero)))
              ⊳ z ↦ ge_def ℕ (a_mem (me_var 0) y))))
         in a_mem (me_var 0) x)
```
With `import N use (y)` or `eval …` in the body, today emits a `gm_check`
entry; the prototype rejects (`"a local module has no imports"`, `"… no
evals"`), by the user's decision.

**A rejected duplicate name.**
```
module T where def x : Nat := 0 end def x : Nat := 0 end end
```
Today and prototype: elaboration error `x is already declared`. With option
O4a (drop the member–member check from the elaborator) the elaborator would
emit both `cc_def`s and the core would reject with `duplicate name x`
(`rc_def` needs `gs_fresh`).

## 5. Options for the core (not implemented), with cost

Line estimates are for the current core; the core is being refactored on
`wip/lm-refactor`, so these should be redone against it.

* **O1. Drop the check entries of local bodies.** `gm_check`, `bcheck`
  (`bc_import`, `bc_eval`) are now unreachable from the front end. Removing
  them from `Syntax.v` deletes one `gmod` constructor and its cases in
  substitution, scoping, typing (`wf_gmod_check*`), member search, the PER and
  completeness, extraction and the printer: about 100 references in 15 core
  files. Pure deletion, est. −200 to −400 core lines, no new proof. **Recommended**, after `wip/lm-refactor` lands.
* **O2. `import E as y` as a core alias member.** The frame case is free today:
  `cc_alias y ⋅ E` exists. It needs (a) a privacy flag on aliases, so that `y`
  is not exported (privacy is being built elsewhere), and (b) a frame for the
  *leading* imports, which today run on the empty stack and are visible in the
  unit's parameter types. (b) has no cheap form: a gunit's parameters precede
  its body, so members filed before the parameters are not representable.
  Saves `en_as` and the weakening in the elaborator (≈ 15 lines across
  elaborator/spec/proof). Cost (a) small once privacy exists; (b) ≈ 200–400
  lines (a pre-parameter frame in `run_unit`, its typing and checker). **Not
  worth it.**
* **O3. `import E use (n)` as a core member.**
  ```coq
  | cc_use : modexp -> string -> ccmd
  | rc_use_def : …, member_type Θ Ξ (gs_tele Ξ) E (n :: nil) mk_term A ->
      Θ ⍮ Ξ ⊢[ch] cc_use E n ⇝ Θ ⍮ gs_add n (gs_def true true Ξ A (a_mem E n)) Ξ
  | rc_use_mod : …, (* n is a submodule of E *) ->
      Θ ⍮ Ξ ⊢[ch] cc_use E n ⇝ Θ ⍮ gs_add n (ge_mod (gu_mk (gs_tele Ξ) (md_alias (me_mem E n)))) Ξ
  ```
  `run_functional` needs `member_type` functional; the checker needs to infer
  the type and to decide term vs submodule; and leading imports have the same
  problem as O2(b). Saves `en_use` (≈ 10 lines). Cost ≈ 300–500 lines.
  **Not worth it.**
* **O4. Freshness in the core.** (a) Member vs member is checked by the core
  already (`gs_fresh` in `rc_def`/`rc_mod`/`rc_alias`), so the elaborator's
  check is redundant there; dropping it splits one language rule over two
  layers and changes the message (`duplicate name x`). (b) Parameter vs
  member and duplicate parameters cannot move: core contexts are nameless.
  Giving `cc_mod`/`cc_alias`/`cunit` parameter names and the stack a name list
  touches `gstack`, i.e. all of typing. **Keep the check in the elaborator**:
  without the invariant it is one premise per declaring rule.
* **O5. Unit reachability in the core.** The core types `me_path (p_abs fq
  nil)` whenever `fq` is filed, which includes units loaded transitively or by
  a closed module. Moving the lexical rule needs a per-frame "imported units"
  component in `run_cmd`'s state and in the checker's invariant (≈ 200
  lines). It is name resolution, so **it stays in the elaborator**, as one
  entry kind.
* **O6. Pre-application in the core** (the user kept today's handling). The
  core would type a member of an open frame un-generalized, i.e. `a_glob p`
  read under the frame's telescope. That makes the meaning of a path depend on
  the stack position, against the "a path denotes the same everywhere" rule
  of `Syntax.v`, and touches typing, semantics and completeness of `a_glob`.
  The prototype's gain from it would be small (`vars_desc k n` is one line).
  **Not recommended.**
* **O7. `a_glob` → `a_mem` chains** (being built elsewhere). In the
  prototype it is a change of two lines, `den_term`/`den_mod` of `en_mem`,
  e.g. `apps (a_mem (me_path (p_abs fp ch)) x) (vars_desc k n)`, once the core
  types `me_path` of an open frame.

## 6. Proof shape

`ElabCorrect.v`: `lookup_iff` (first match ↔ `bound`), `den_to_*_iff`,
`objects_iff` by `Cst.cst_mut_ind` (one generic tactic `iff_case` closes all
homomorphic cases), `itarget_iff`/`ibinds_iff`/`import_iff`, `commands_iff` by
`Cst.cst_mut_ind` again with the motive `md = md_where body -> Pcmds body`,
`imports_iff`, `elaborate_core_iff`. The relational spec is kept: it is now
small enough that a declarative reading costs little, and it states the
scoping rule (`bound`) independently of the search.

## 7. Remaining work

* O1 (drop `gm_check`), after the core refactor: 1–2 days.
* O7, when `a_mem` chains land: an hour.
* `AGENT/elab-spec.md` is updated; `doc/alignment.md` does not mention the
  front end's internals.
