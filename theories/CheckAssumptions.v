(** * The Assumptions of the Main Theorems

    Every theorem below must be closed under the global context: it uses
    no axiom, no parameter and no section variable left open.  The only
    exceptions, with the axioms they may use, are listed in
    [CheckAssumptions.expected].

    Run [make check-assumptions] after a build.  This file is not part of
    the build ([_CoqProject]): printing the assumptions of every theorem
    takes minutes.  Add a theorem here when it becomes a main result. *)

From Mctt Require Import Entrypoint.
From Mctt Require Import Core.Completeness Core.Soundness Core.Consequences.Consistency Extraction.Command Frontend.ElabCorrect Algorithmic.Typing.Lemmas Algorithmic.Strengthening Core.Semantic.Avoid Core.Consequences.NormalFormWeakening.
From Mctt Require Import Reference.Refinement Extraction.Simulation Extraction.GlobalCheck.
From Mctt Require Import Core.Syntactic.Presup Core.Syntactic.System.Global.Presup Core.Consequences.FiledConstructorTypes.
From Mctt Require Import Core.Syntactic.System.Inductives.IndRuns Core.Syntactic.System.Records.RecordRuns.
Print Assumptions Mctt.Core.Completeness.completeness.
Print Assumptions Mctt.Core.Completeness.FundamentalTheorem.completeness_fundamental.
Print Assumptions Mctt.Core.Soundness.soundness.
Print Assumptions Mctt.Core.Soundness.soundness'.
Print Assumptions Mctt.Core.Soundness.FundamentalTheorem.soundness_fundamental.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_ind_nat_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_ind_nat_stuck_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_ind_nat_no_axioms.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_bound_nat_prog.
Print Assumptions Mctt.Core.Syntactic.System.Command.run_builtins_wf.
Print Assumptions Mctt.Core.Syntactic.System.Command.prog_sem_builtins_wf.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_large.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_large_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_no_axioms.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_large_no_axioms.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_large_typ_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ_stuck_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_large_typ_stuck_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ_no_axioms.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_large_typ_no_axioms.
Print Assumptions alg_type_infer_typ_complete.
Print Assumptions alg_type_infer_typ_complete_tm.
Print Assumptions alg_type_infer_large_typ_complete.
Print Assumptions nbe_wk_fresh.
Print Assumptions nf_strengthen_shift.
Print Assumptions level_nf_strengthen.
Print Assumptions nbe_wk.
Print Assumptions nbe_ty_wk.
Print Assumptions nbe_wk_fresh_sem.
Print Assumptions exp_eq_strengthen_sem.
Print Assumptions prog_impl_sound.
Print Assumptions prog_impl_complete.
Print Assumptions prog_impl_rep.
Print Assumptions main_sound.
Print Assumptions main_complete.
Print Assumptions main_rep.
Print Assumptions elaborate_core_iff.
(* Sorted levels: the general statements and their corollaries. *)
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ_stuck.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ_lit.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ_lit_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ_lit_stuck.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ_lit_stuck_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_typ_lit_no_axioms.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_lit.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_lit_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_lit_no_axioms.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_False.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_False_no_axioms.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_False_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_False_prog.
Print Assumptions Mctt.Core.Consequences.Consistency.consistency_False_run.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_large_typ.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_large_typ_stuck.
Print Assumptions Mctt.Core.Consequences.Consistency.typ_nf_below_of_nbe.
Print Assumptions Mctt.Core.Consequences.Consistency.subtyp_suniv_bound.
Print Assumptions Mctt.Core.Consequences.Consistency.subtyp_suniv_lit_bound.
Print Assumptions Mctt.Algorithmic.Typing.Lemmas.alg_type_infer_typ_complete_lit.
Print Assumptions Mctt.Extraction.GlobalCheck.alg_type_infer_typ_complete'.
Print Assumptions Mctt.Extraction.GlobalCheck.alg_type_infer_typ_complete_lit'.
Print Assumptions Mctt.Extraction.GlobalCheck.alg_type_infer_large_typ_complete'.
(* Refinement: the fast extracted code agrees with the reference. *)
Print Assumptions Mctt.Reference.Refinement.type_check_in_refines.
Print Assumptions Mctt.Reference.Refinement.type_infer_in_refines.
Print Assumptions Mctt.Reference.Refinement.ext_check_refines.
Print Assumptions Mctt.Reference.Refinement.unit_check_refines.
Print Assumptions Mctt.Reference.Refinement.modexp_check_refines.
Print Assumptions Mctt.Reference.Refinement.eval_exp_impl_refines.
Print Assumptions Mctt.Reference.Refinement.read_typ_impl_refines.
Print Assumptions Mctt.Reference.Refinement.read_nf_impl_refines.
Print Assumptions Mctt.Reference.Refinement.initial_env_impl_refines.
Print Assumptions Mctt.Reference.Refinement.nbe_ty_env_impl_refines.
Print Assumptions Mctt.Reference.Refinement.nbe_ty_impl_refines.
Print Assumptions Mctt.Reference.Refinement.nbe_impl_refines.
Print Assumptions Mctt.Reference.Refinement.eval_exp_impl_refines_at.
Print Assumptions Mctt.Reference.Refinement.read_typ_impl_refines_at.
Print Assumptions Mctt.Reference.Refinement.read_nf_impl_refines_at.
Print Assumptions Mctt.Reference.Refinement.initial_env_impl_refines_at.
Print Assumptions Mctt.Reference.Refinement.nbe_ty_env_impl_refines_at.
Print Assumptions Mctt.Reference.Refinement.nbe_ty_impl_refines_at.
Print Assumptions Mctt.Reference.Refinement.nbe_impl_refines_at.
Print Assumptions Mctt.Extraction.Simulation.fast_eval_sim.
Print Assumptions Mctt.Extraction.Simulation.fast_read_sim.
Print Assumptions Mctt.Extraction.Simulation.fast_read_typ_sim.
Print Assumptions Mctt.Extraction.Simulation.fast_read_nf_sim.
Print Assumptions Mctt.Extraction.Simulation.fast_eval_exp_sim.
Print Assumptions Mctt.Extraction.Simulation.fast_eval_app_sim.
Print Assumptions Mctt.Extraction.Simulation.fast_eval_clo_sim.
Print Assumptions Mctt.Extraction.Simulation.fast_eval_clo2_sim.
(* Inductive types: canonical forms, and the generated eliminators. *)
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_pi.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_ind.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_ind_gctx.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_ind_nat.
Print Assumptions Mctt.Core.Consequences.Consistency.canonical_form_of_ind_nat_stuck.
Print Assumptions Mctt.Core.Consequences.FiledConstructorTypes.run_cmd_ind_con_types.
Print Assumptions Mctt.Core.Syntactic.System.Inductives.IndRuns.run_cmd_ind_runs.
(* Presupposition: local, and of the global context. *)
Print Assumptions Mctt.Core.Syntactic.System.Lemmas.presup_exp.
Print Assumptions Mctt.Core.Syntactic.Presup.presup_exp_eq.
Print Assumptions Mctt.Core.Syntactic.Presup.presup_subtyp.
Print Assumptions Mctt.Core.Syntactic.Presup.presup_sub_eq.
Print Assumptions Mctt.Core.Syntactic.System.Global.Presup.presup_global.
Print Assumptions Mctt.Core.Syntactic.System.Global.Presup.presup_exp_typ.
(* The checker of commands and units, and the elaborator. *)
Print Assumptions Mctt.Extraction.Command.run_cmd_impl_sound.
Print Assumptions Mctt.Extraction.Command.run_cmds_impl_sound.
Print Assumptions Mctt.Extraction.Command.run_unit_impl_sound.
Print Assumptions Mctt.Extraction.Command.run_cmd_impl_complete.
Print Assumptions Mctt.Extraction.Command.run_cmds_impl_complete.
Print Assumptions Mctt.Extraction.Command.run_unit_impl_complete.
Print Assumptions Mctt.Extraction.Command.prog_impl_complete_wf.
Print Assumptions Mctt.Frontend.ElabCorrect.elaborate_core_sound.
Print Assumptions Mctt.Frontend.ElabCorrect.elaborate_core_complete.
Print Assumptions Mctt.Frontend.ElabCorrect.elab_spec_functional.
(* Records: equal record types have equal parameters, and a type below a
   record type normalises to it. *)
Print Assumptions Mctt.Core.Consequences.Consistency.exp_eq_record_apps_inv.
Print Assumptions Mctt.Core.Consequences.Consistency.subtyp_record_nf.
(* Records: a field's projection of its module's value is of the field's
   type, and an accepted record declaration runs. *)
Print Assumptions Mctt.Core.Syntactic.System.Records.RecordRuns.record_field_def_typed.
Print Assumptions Mctt.Core.Syntactic.System.Records.RecordRuns.run_cmd_record_runs.
(* The typed fill of a command (its literals, its eliminators' groups,
   its accesses through terms) is functional, and decided by the
   checker. *)
Print Assumptions Mctt.Core.TypedElab.Lemmas.fill_cmd_functional.
Print Assumptions Mctt.Core.TypedElab.Lemmas.fill_params_functional.
Print Assumptions Mctt.Core.Syntactic.System.Command.fill_unique_run.
Print Assumptions Mctt.Extraction.TypedElab.fill_cmd_fn_sound.
Print Assumptions Mctt.Extraction.TypedElab.fill_cmd_fn_complete.
Print Assumptions Mctt.Extraction.TypedElab.fill_params_fn_sound.
Print Assumptions Mctt.Extraction.TypedElab.fill_params_fn_complete.
Print Assumptions Mctt.Extraction.MdefGroup.mdef_group_dec_complete.
