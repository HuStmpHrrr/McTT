From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Import PER.
From Mctt.Core.Completeness.LogicalRelation Require Import Definitions.
Import Domain_Notations Fixed_Notations.

(** Each semantic judgment is a record whose witnesses come first: the
    context PERs, read off a hypothesis by [eassumption], and the universe
    level, left to be found.  These open one, leaving its body.  The derived
    forms of the judgments ([rel_exp_under_ctx_simple] and the like) state the
    same witnesses as existentials, which the second alternative opens. *)
Ltac eexists_ctx_level :=
  eexists;
  eexists; [eassumption |];
  eexists.

Ltac eexists_ctx_level_with i :=
  eexists;
  eexists; [eassumption |];
  exists i.

Ltac eexists_ctx_pair :=
  eexists;
  eexists; [eassumption |];
  eexists;
  eexists; [eassumption |].

Ltac eexists_rel_exp :=
  first [ eapply mk_rel_exp_under_ctx; [eassumption |] | eexists_ctx_level ].

Ltac eexists_rel_exp_with i :=
  first [ eapply mk_rel_exp_under_ctx with (rel_exp_under_ctx_lvl := i); [eassumption |] | eexists_ctx_level_with i ].

Ltac eexists_rel_sub :=
  first [ eapply mk_rel_sub_under_ctx; [eassumption | eassumption |] | eexists_ctx_pair ].

(** [rel_wk_under_ctx] has the same outer shape as [rel_sub_under_ctx] — two
    environment PERs, each with its context witness read off the goal. *)
Ltac eexists_rel_wk :=
  first [ eapply mk_rel_wk_under_ctx; [eassumption | eassumption |] | eexists_ctx_pair ].

Ltac eexists_subtyp :=
  first [ eapply mk_rel_subtyp_under_ctx; [eassumption |] | eexists_ctx_level ].

Ltac eexists_subtyp_with i :=
  first [ eapply mk_rel_subtyp_under_ctx with (rel_subtyp_under_ctx_lvl := i); [eassumption |] | eexists_ctx_level_with i ].

(** ** The Semantic Judgments *)

(** Take the judgments at a target apart.  A premise [H] becomes, under its
    own name, its relation at the target; its context and the validity
    parts get fresh names. *)
Ltac sem_destruct :=
  repeat match goal with
    | H : sem_exp_eq_at _ _ _ _ _ _ _ _ |- _ => let Hc := fresh "HKctx" in destruct H as [Hc H]
    | H : sem_subtyp_at _ _ _ _ _ _ _ |- _ => let Hc := fresh "HKctx" in destruct H as [Hc H]
    | H : sem_is_univ_at _ _ _ _ _ _ |- _ => let Hc := fresh "HKctx" in destruct H as [Hc H]
    | H : sem_ext_eq_at _ _ _ _ _ _ _ |- _ =>
        let Hc := fresh "HKctx" in let Hx := fresh "HKext" in let Hx' := fresh "HKext" in
        destruct H as [Hc H Hx Hx']
    | H : sem_unit_eq_at _ _ _ _ _ _ _ |- _ =>
        let Hc := fresh "HKctx" in let Hk := fresh "HKunit" in let Hk' := fresh "HKunit" in
        destruct H as [Hc H Hk Hk']
    | H : sem_modexp_eq_at _ _ _ _ _ _ _ |- _ =>
        let Hc := fresh "HKctx" in let Hs := fresh "HKmodexp" in let Hs' := fresh "HKmodexp" in
        destruct H as [Hc H Hs Hs']
    end.

(** Each context with valid slots in scope is semantically well formed: a
    hypothesis [H] of it becomes, under its own name, the semantic
    well-formedness, and the context with valid slots is kept under a
    fresh name. *)
Ltac add_rel_ctx_wf :=
  repeat match goal with
    | H : @valid_ctx ?gc _ _ ?G |- _ =>
        lazymatch goal with
        | _ : @rel_ctx_wf gc G |- _ => fail
        | _ =>
            let Hs := fresh "HKslots" in rename H into Hs;
            assert (H : @rel_ctx_wf gc G) by (inversion Hs; subst; first [ assumption | constructor ])
        end
    end.

(** State a judgment at a target by its parts. *)
Ltac sem_goal :=
  try lazymatch goal with
  | |- sem_exp_eq_at _ _ _ _ _ _ _ _ => constructor
  | |- sem_subtyp_at _ _ _ _ _ _ _ => constructor
  | |- sem_is_univ_at _ _ _ _ _ _ => constructor
  | |- sem_ext_eq_at _ _ _ _ _ _ _ => constructor
  | |- sem_unit_eq_at _ _ _ _ _ _ _ => constructor
  | |- sem_modexp_eq_at _ _ _ _ _ _ _ => constructor
  end.

(** Open the case of a rule: fix a sound embedding, read every premise at
    its target, take the premises apart, and state the conclusion there by
    its parts.  [Hemb], [Hgm], [Hgf], [Hsub] and [Hgw] are what the
    embedding gives. *)
Ltac sem_intro0 :=
  (** A rule is stated at no global context: an ambient one (a section's) is
      not the one the relations are read at. *)
  repeat match goal with G : GCtx |- _ => clear G end;
  unfold sem_ctx, sem_exp, sem_exp_eq, sem_subtyp, sem_is_univ, sem_ext_eq, sem_unit_eq, sem_modexp_eq in *; intros;
  match goal with He : valid_emb ?T1 ?X1 ?T2 ?X2 |- _ =>
    let Hemb := fresh "Hemb" in let Hgm := fresh "Hgm" in let Hgf := fresh "Hgf" in
    let Hsub := fresh "Hsub" in let Hgw := fresh "Hgw" in
    pose proof (valid_emb_emb _ _ _ _ He) as Hemb; pose proof (valid_emb_wf _ _ _ _ He) as Hgm;
    pose proof (valid_emb_filed _ _ _ _ He) as Hgf;
    pose proof (em_res _ _ _ _ Hemb) as Hsub; pose proof (em_wf _ _ _ _ Hemb) as Hgw;
    change (⊢ᵍ @gc_deps (gc_mk T2 X2) ⍮ @gc_stack (gc_mk T2 X2)) in Hgw;
    change (gc_sub T1 X1 (@gc_deps (gc_mk T2 X2)) (@gc_stack (gc_mk T2 X2))) in Hsub;
    (** The target, named, is the global context the relations are read at. *)
    let GC := fresh "GC" in set (GC := gc_mk T2 X2) in * end;
  repeat match goal with IH : forall _ _, valid_emb _ _ _ _ -> _, He : valid_emb _ _ _ _ |- _ =>
    specialize (IH _ _ He) end;
  sem_destruct; destruct_conjs; add_rel_ctx_wf.

(** The same, with the conclusion stated by its parts. *)
Ltac sem_intro := sem_intro0; sem_goal.

Ltac invert_rel_typ_body :=
  simplify_evals;
  match_by_head per_univ_elem ltac:(fun H => directed invert_per_univ_elem H); subst;
  clear_dups;
  clear_refl_eqs;
  handle_per_univ_elem_irrel;
  clear_dups;
  try rewrite <- per_univ_elem_equation_1 in *.
