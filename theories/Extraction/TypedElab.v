(** * Deciding the Typed Fill

    The fill of [Core.TypedElab.Fill], computed.  Every written command is
    filled part by part, its contexts computed as the relation reads them,
    inferring a type ([infer_at]) only where the relation does: at the
    sort of a binder's type, at an access's head, at an unannotated [let],
    at an eliminator's scrutinee and motive.  The computed fill is the
    relation's ([fill_cmd_fn_sound]), and is found whenever the relation
    has one ([fill_cmd_fn_complete]). *)

From Stdlib Require Import List String PeanoNat Bool Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System Builtin Records.
From Mctt.Core.Syntactic.System Require Import Privacy Translations.
From Mctt.Core Require Import TypedElab.
From Mctt.Core.Semantic Require Import GlobalExt.
From Mctt.Core.Syntactic.System.Global Require Import Paths.
From Mctt.Algorithmic.Typing Require Import Definitions Functional Lemmas.
From Mctt.Extraction Require Import Lookup TypeCheckBase TypeCheck GlobalCheck MemberType MemberOrder Privacy.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Import IndDecl MdefGroup FastDesc LookupTwins Formers.
Import Syntax_Notations.

Open Scope string_scope.

(** ** The Fill Crosses [gds_equiv]

    The checker fills a command at the units the unit imported, the
    judgment at the units filed: the two have the same lookups, so the
    same inferred types, the same denotations, the same eliminator
    readings, the same literals and the same privacy, and so the same
    fills. *)

(** The literals are read off the bound type's declaration, the same at
    equivalent dependencies. *)
Lemma equiv_nat_view : forall Θ Θ' Ξ B, gds_equiv Θ Θ' -> nat_view Θ Ξ B = nat_view Θ' Ξ B.
Proof.
  intros * He; unfold nat_view; destruct (builtins_nat B) as [p |]; [| reflexivity ].
  rewrite (gds_equiv_ind_lookup _ _ _ _ He); reflexivity.
Qed.

Section AlgEquiv.
  Variables (Θ Θ' : gdeps) (Ξ : gstack) (B : builtins).
  Hypothesis He : gds_equiv Θ Θ'.

  Let Hind : forall p D, ind_lookup Θ Ξ p = Some D -> ind_lookup Θ' Ξ p = Some D.
  Proof. intros; rewrite <- (gds_equiv_ind_lookup _ _ _ _ He); assumption. Qed.
  Let Hrec : forall p R, record_lookup Θ Ξ p = Some R -> record_lookup Θ' Ξ p = Some R.
  Proof. intros; rewrite <- (gds_equiv_record_lookup _ _ _ _ He); assumption. Qed.
  Let Hnv : forall v, nat_view Θ Ξ B = v -> nat_view Θ' Ξ B = v.
  Proof. intros; rewrite <- (equiv_nat_view _ _ _ _ He); assumption. Qed.
  Let Het : forall pc k Rs m Bks t, elim_target Θ Ξ pc k Rs m Bks = t -> elim_target Θ' Ξ pc k Rs m Bks = t.
  Proof.
    intros * E; rewrite <- E; symmetry; apply elim_target_lookup_ext; intros p.
    exact (gds_equiv_ind_lookup _ _ _ _ He).
  Qed.
  Let Hnbt : forall Γ A W, nbe_ty Θ Ξ Γ A W -> nbe_ty Θ' Ξ Γ A W := equiv_nbe_ty Θ Θ' Ξ He.
  Let Hnb : forall Γ M A W, nbe Θ Ξ Γ M A W -> nbe Θ' Ξ Γ M A W := equiv_nbe Θ Θ' Ξ He.
  Let Hmd := gds_equiv_mdenote_all Θ Θ' Ξ He.
  Let Hif : forall Γ M W, ind_former Θ Ξ Γ M W -> ind_former Θ' Ξ Γ M W :=
    fun Γ M W => equiv_ind_former Θ Θ' Ξ Γ M W He.
  Let Hrf : forall Γ M W, record_former Θ Ξ Γ M W -> record_former Θ' Ξ Γ M W :=
    fun Γ M W => equiv_record_former Θ Θ' Ξ Γ M W He.

  Lemma equiv_nfs_agree : forall Γ Ms Rs Ts, @nfs_agree (gc_mk Θ Ξ) Γ Ms Rs Ts -> @nfs_agree (gc_mk Θ' Ξ) Γ Ms Rs Ts.
  Proof. induction 1; [ apply (@nfs_agree_nil (gc_mk Θ' Ξ)) | eapply (@nfs_agree_cons (gc_mk Θ' Ξ)); eauto ]. Qed.

  Lemma equiv_alg_subtyping : forall Γ A B, @alg_subtyping (gc_mk Θ Ξ) Γ A B -> @alg_subtyping (gc_mk Θ' Ξ) Γ A B.
  Proof. intros * []; econstructor; eauto. Qed.

  (** Types with normal forms equal up to proofs have them at the
      equivalent dependencies too. *)
  Lemma equiv_alg_ty_conv : forall Γ A A', @alg_ty_conv (gc_mk Θ Ξ) Γ A A' -> @alg_ty_conv (gc_mk Θ' Ξ) Γ A A'.
  Proof. intros * (W & W' & HW & HW' & E); exists W, W'; auto. Qed.

  (** The kind of a type is read off its value, which evaluation reads
      through the lookups alone. *)
  Lemma equiv_nbe_ty_kind : forall Γ A κ, @nbe_ty_kind (gc_mk Θ Ξ) Γ A κ -> @nbe_ty_kind (gc_mk Θ' Ξ) Γ A κ.
  Proof.
    assert (Hs : (forall p, gc_resolve Θ Ξ p = gc_resolve Θ' Ξ p) /\ (forall p, gc_module Θ Ξ p = gc_module Θ' Ξ p) /\
                 (forall p, ind_lookup Θ Ξ p = ind_lookup Θ' Ξ p) /\ (forall p, gc_entry Θ Ξ p = gc_entry Θ' Ξ p) /\
                 (forall p, gc_frame Ξ p = gc_frame Ξ p) /\ (forall p, gs_find_ind Ξ p = gs_find_ind Ξ p) /\
                 (forall p, gc_body Θ Ξ p = gc_body Θ' Ξ p) /\ (forall p, record_lookup Θ Ξ p = record_lookup Θ' Ξ p))
      by (repeat split; intros; first [ reflexivity | apply gds_equiv_resolve | apply gds_equiv_module
                                       | apply gds_equiv_ind_lookup | apply gds_equiv_entry | apply gds_equiv_body
                                       | apply gds_equiv_record_lookup ];
          exact He).
    destruct Hs as (Hres & Hmod & Hind' & Hia & Hfr & Hfi & Hbody & Hrec').
    pose proof (eval_ext _ _ _ _ Hres Hmod Hind' Hia Hfr Hfi Hbody Hrec') as Hev.
    pose proof (initial_env_ext _ _ _ _ Hres Hmod Hind' Hia Hfr Hfi Hbody Hrec') as Hie.
    (** the section's [Let]s are no conjunctions to split *)
    clear Hmd Hnbt Hnb.
    destruct_all.
    intros * (ρ & a & Hi & Ha & Hr); exists ρ, a; cbn in *; split; [| split ]; eauto.
  Qed.

  (** The dependencies the fill and the algorithm are moved to are well
      formed: the flag premise ([levels_abstractable]) is a judgment. *)
  Hypothesis Hg' : ⊢ᵍ Θ' ⍮ Ξ.

  (** The flag premise moves along the equivalence: a parameter telescope
      of types of levels does not read the dependencies, and what a target
      denotes and that it has no member of a type of levels read them
      through lookups and judgments ([deps_grow]). *)
  Lemma equiv_levels_abstractable : forall Γ Δ E, levels_abstractable Θ Ξ Γ Δ E -> levels_abstractable Θ' Ξ Γ Δ E.
  Proof.
    destruct Hmd as (Hm1 & _).
    intros * [Hs | (R & HR & Hnl)]; [ left; exact Hs | right; exists R; split; [ exact (Hm1 _ _ _ HR) |] ].
    apply (deps_grow _ _ _ (proj1 He)); [ constructor; exact Hg' | exact Hnl ].
  Qed.

  (** The frame premise moves along the equivalence: what a target denotes
      moves unchanged, and the frames are the same. *)
  Lemma equiv_frame_free : forall Γ E, frame_free_target Θ Ξ Γ E -> frame_free_target Θ' Ξ Γ E.
  Proof.
    destruct Hmd as (Hm1 & _).
    intros * (R & HR & Hn); exists R; split; [ exact (Hm1 _ _ _ HR) | exact Hn ].
  Qed.

  (** Algorithmic typing reads the dependencies through their lookups
      alone, and the flag premise through judgments. *)
  Lemma equiv_alg_all :
    (forall Γ A M, @alg_type_check (gc_mk Θ Ξ) Γ A M -> @alg_type_check (gc_mk Θ' Ξ) Γ A M) /\
    (forall Γ A M, @alg_type_infer (gc_mk Θ Ξ) Γ A M -> @alg_type_infer (gc_mk Θ' Ξ) Γ A M) /\
    (forall Γ Ψ, @alg_ext (gc_mk Θ Ξ) Γ Ψ -> @alg_ext (gc_mk Θ' Ξ) Γ Ψ) /\
    (forall Γ Δ, @alg_params (gc_mk Θ Ξ) Γ Δ -> @alg_params (gc_mk Θ' Ξ) Γ Δ) /\
    (forall Γ U, @alg_unit (gc_mk Θ Ξ) Γ U -> @alg_unit (gc_mk Θ' Ξ) Γ U) /\
    (forall Γ Φ Φx, @alg_body (gc_mk Θ Ξ) Γ Φ Φx -> @alg_body (gc_mk Θ' Ξ) Γ Φ Φx) /\
    (forall Γ H, @alg_modexp (gc_mk Θ Ξ) Γ H -> @alg_modexp (gc_mk Θ' Ξ) Γ H).
  Proof.
    destruct Hmd as (Hm1 & Hm2 & Hm3 & Hm4 & Hm5).
    apply (@alg_type_mut_ind (gc_mk Θ Ξ)); intros; cbn [gc_deps gc_stack] in *;
      solve [ econstructor; eauto 6 using equiv_nfs_agree, equiv_alg_subtyping, equiv_nbe_ty_kind, equiv_alg_ty_conv, equiv_levels_abstractable,
                equiv_frame_free ].
  Qed.

  Lemma equiv_glob_ok : forall H y, glob_ok Θ Ξ H y -> glob_ok Θ' Ξ H y.
  Proof. intros * Hok qd Hd; apply Hok; exact (mdecl_deps_sub _ _ _ (proj2 He) _ _ _ _ Hd). Qed.

  Lemma equiv_sel_ok : forall op y, sel_ok Θ Ξ op y -> sel_ok Θ' Ξ op y.
  Proof. intros [p |] y; cbn; [ apply equiv_glob_ok | auto ]. Qed.

  Let Hmd' := gds_equiv_mdenote_all Θ' Θ Ξ (gds_equiv_sym _ _ He).

  (** The fill reads the dependencies through lookups, inference, the
      eliminator readings, the literals and privacy, all alike. *)
  Lemma equiv_fill_all :
    (forall Γ M M', fill_exp Θ Ξ B Γ M M' -> fill_exp Θ' Ξ B Γ M M') /\
    (forall Γ fs fs', fill_field_vals Θ Ξ B Γ fs fs' -> fill_field_vals Θ' Ξ B Γ fs fs') /\
    (forall r Γ p D Us As j Bks Bks', fill_blocks Θ Ξ B r Γ p D Us As j Bks Bks' -> fill_blocks Θ' Ξ B r Γ p D Us As j Bks Bks') /\
    (forall Γ p D j Mj Us Z Z', fill_scrutinee_type Θ Ξ B Γ p D j Mj Us Z Z' -> fill_scrutinee_type Θ' Ξ B Γ p D j Mj Us Z Z') /\
    (forall r Γ p D Mj Us As Bs Bs', fill_brs Θ Ξ B r Γ p D Mj Us As Bs Bs' -> fill_brs Θ' Ξ B r Γ p D Mj Us As Bs Bs') /\
    (forall Γ oM oM', fill_optional_exp Θ Ξ B Γ oM oM' -> fill_optional_exp Θ' Ξ B Γ oM oM') /\
    (forall Γ H r, fill_read Θ Ξ B Γ H r -> fill_read Θ' Ξ B Γ H r) /\
    (forall Γ H H' op, fill_mod Θ Ξ B Γ H H' op -> fill_mod Θ' Ξ B Γ H H' op) /\
    (forall Γ U U', fill_unit Θ Ξ B Γ U U' -> fill_unit Θ' Ξ B Γ U U') /\
    (forall Γ D D', fill_def Θ Ξ B Γ D D' -> fill_def Θ' Ξ B Γ D D') /\
    (forall Γ Δ Δ', fill_tele Θ Ξ B Γ Δ Δ' -> fill_tele Θ' Ξ B Γ Δ Δ') /\
    (forall Γ Φ Φ', fill_body Θ Ξ B Γ Φ Φ' -> fill_body Θ' Ξ B Γ Φ Φ').
  Proof.
    destruct Hmd as (Hm1 & _ & _ & Hm4 & Hm5); destruct Hmd' as (Hm1' & _ & _ & _ & _).
    pose proof (proj1 (proj2 equiv_alg_all)) as Hinf.
    apply fill_mut_ind; intros; try solve [ econstructor; eauto using equiv_sel_ok, equiv_ctx, Forall_impl ].
    (* a member that is no term: no term along the equivalence either *)
    eapply fill_read_mem_module; [ exact H0 | apply equiv_sel_ok; exact s | intros r A oM Hm; exact (n r A oM (Hm1' _ _ _ Hm)) ].
  Qed.

  (** Named types, filled, along the equivalence. *)
  Lemma equiv_fill_fields : forall Γ fs fs', fill_fields Θ Ξ B Γ fs fs' -> fill_fields Θ' Ξ B Γ fs fs'.
  Proof.
    pose proof (proj1 equiv_fill_all) as Fe; pose proof (proj1 (proj2 equiv_alg_all)) as Hinf.
    induction 1; econstructor; eauto using equiv_ctx.
  Qed.
End AlgEquiv.

(** The fill of a command, and of a unit's parameters, along an
    equivalence of the dependencies. *)
Lemma equiv_fill_cmd : forall Θ Θ' Ξ B c its, gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> fill_cmd Θ Ξ B c its -> fill_cmd Θ' Ξ B c its.
Proof.
  intros * He Hg' H.
  pose proof (equiv_fill_all _ _ _ B He Hg') as (Fe & _ & _ & _ & Fbr & Fo & _ & Fm & _ & _ & Ft & _).
  pose proof (proj1 (proj2 (equiv_alg_all _ _ _ He Hg'))) as Hinf.
  pose proof (equiv_fill_fields _ _ _ B He Hg') as Ff.
  destruct H as [ | | | | | | | | | | pv R R' [Hu Hr Hm] | b pv Δ Δ' f0 fs h0 hs f0' fs' pq m0 Ps D Us ms HΔ Hh Hgp Hb | ].
  11:{ (* a group: each part *)
       apply fill_cmd_ind_decl; constructor; [ exact (Ft _ _ _ Hu) | exact Hr |].
       eapply Forall2_impl; [| exact Hm ]; intros Mr Mr' [En Hn Hs Hc]; constructor; eauto.
       eapply Forall2_impl; [| exact Hc ]; intros rc rc' [Ef Ht]; split; [ exact Ef | exact (Ff _ _ _ Ht) ]. }
  11:{ (* a mutual definition: its heads, its group, its bodies *)
       eapply fill_cmd_mdef; [ exact (Ft _ _ _ HΔ) | | exact (equiv_mdef_group _ _ _ _ _ _ _ _ _ _ _ _ He Hg' Hgp) | ].
       - eapply Forall2_impl; [| exact Hh ]; intros f h [En Ep Es]; constructor; eauto.
       - eapply Forall2_impl; [| exact Hb ]; intros fhm f' [Eh Hmm Hr Hc]; constructor; eauto. }
  all: first [ eapply fill_cmd_eval_infer; solve [ eauto using equiv_ctx ]
             | econstructor; solve [ eauto using Forall_impl, equiv_sel_ok, equiv_ctx ] ].
Qed.

Lemma equiv_fill_params : forall Θ Θ' Ξ B Δ Δ', gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ ->
    fill_params Θ Ξ B Δ Δ' -> fill_params Θ' Ξ B Δ Δ'.
Proof. intros * He Hg' Ht; apply (equiv_fill_all _ _ _ B He Hg'); exact Ht. Qed.

(** ** Results *)

(** Why a command has no fill. *)
Inductive fill_failure : Set :=
(** The term a member [y] is selected from, in its context: its type is
    not inferred *)
| fill_failure_no_type : string -> ctx -> exp -> fill_failure
(** The term a member [y] is selected from, in its context: its type,
    inferred, is not a record type *)
| fill_failure_not_record : string -> ctx -> exp -> nf -> fill_failure
(** A private member, named by its record's module, reached from outside
    it *)
| fill_failure_private : qname -> string -> fill_failure
(** A mutual definition's functions, their heads filled, have no group:
    why *)
| fill_failure_mdef_group : mdef_group_why -> fill_failure
(** A literal, with no natural-number type bound *)
| fill_failure_literal : literal_failure_reason -> fill_failure
(** An eliminator's scrutinee, filled, in its context: its type, if
    inferred, is not an inductive type *)
| fill_failure_elim_scrutinee : ctx -> exp -> option nf -> fill_failure
(** An eliminator, in its context, whose scrutinee's type is the member
    [k] of the group [pc] at the arguments [Rs], and no reading of which
    fits its blocks: [pc], [k], [Rs], the block marked [at], the
    constructor names of the blocks and the filled scrutinee *)
| fill_failure_elim_none : ctx -> qname -> nat -> list nf -> nat -> list (list string) -> exp -> fill_failure
(** An eliminator, in its context, several readings of which fit its
    blocks: its filled scrutinee and the readings, each its group and its
    uniform parameters *)
| fill_failure_elim_ambiguous : ctx -> exp -> list (qname * list exp) -> fill_failure
(** A local body, in its context, whose entries filled so far have no
    expansion: an open among them generates nothing *)
| fill_failure_body : ctx -> gmod -> fill_failure
(** A term, in its context, of no record type, where a module stands with
    nothing selected from it: the target of an open, an alias or a
    builtin binding *)
| fill_failure_not_module : ctx -> exp -> fill_failure
(** The branch of the constructor [c] of an eliminator, binding [n]
    variables where it needs [k] parameters, [a] arguments and [r]
    recursive results *)
| fill_failure_branch_arity : string -> nat -> nat -> nat -> nat -> fill_failure
(** A type, in its context, whose sort is not inferred, and what it is
    the type of *)
| fill_failure_no_kind : string -> ctx -> exp -> fill_failure
(** Any other reason *)
| fill_failure_message : string -> fill_failure.

(** A fill, or why there is none. *)
Inductive fill_result (A : Type) : Type :=
(** The fill *)
| fill_ok : A -> fill_result A
(** Why there is none *)
| fill_error : fill_failure -> fill_result A.
Arguments fill_ok {A}.
Arguments fill_error {A}.

(** A fill, then what is filled from it. *)
Definition fill_result_bind {A B} (m : fill_result A) (f : A -> fill_result B) : fill_result B :=
  match m with
  | fill_ok a => f a
  | fill_error e => fill_error e
  end.

Notation "'let%a' x ':=' m 'in' f" := (fill_result_bind m (fun x => f))
  (at level 200, x name, m at level 100, f at level 200, right associativity).

Lemma fill_result_bind_ok : forall {A B} (m : fill_result A) (f : A -> fill_result B) b,
    fill_result_bind m f = fill_ok b <-> exists a, m = fill_ok a /\ f a = fill_ok b.
Proof.
  intros; destruct m; cbn; split; intros H.
  - eauto.
  - destruct H as (? & [= <-] & ?); assumption.
  - discriminate.
  - destruct H as (? & ? & _); discriminate.
Qed.

(** ** The Written Syntax, by Induction

    The written terms are nested through lists and options, so their
    induction principle is written by hand, as [syn_mut_ind] is for the
    core syntax. *)

(** A written term with no subterm. *)
Definition surface_atom (M : surface_exp) : Prop :=
  match M with
  | surface_typ _ | surface_level _ | surface_llit _ | surface_ntok | surface_nlit _ | surface_prop | surface_True
  | surface_tt | surface_False | surface_var _ | surface_hole => True
  | _ => False
  end.

(** A property of each term of a written eliminator's block: its
    scrutinee's type, its motive and its branches. *)
Definition surface_block_all (P : surface_exp -> Prop) (b : surface_block) : Prop :=
  match b with
  | surface_eb_mk _ Z A Bs => P Z /\ P A /\ List.Forall (fun br => P (snd br)) Bs
  end.

(** Whether a written term is a hole, an annotation left to the fill. *)
Definition is_surface_hole (M : surface_exp) : bool :=
  match M with
  | surface_hole => true
  | _ => false
  end.

Lemma is_surface_hole_spec : forall M, is_surface_hole M = true <-> M = surface_hole.
Proof. intros []; cbn; split; intros H; try reflexivity; discriminate. Qed.

Lemma is_surface_hole_false : forall M, is_surface_hole M = false <-> M <> surface_hole.
Proof. intros []; cbn; split; intros H; try discriminate; try reflexivity; exfalso; apply H; reflexivity. Qed.

Section surface_mut_ind.
  Variables (Pe : surface_exp -> Prop) (Pm : surface_modexp -> Prop) (Pb : surface_binding -> Prop)
    (Pu : surface_unit -> Prop) (Pd : surface_moddef -> Prop) (Pg : surface_body -> Prop) (Pn : surface_entry -> Prop).

  Hypotheses
    (case_atom : forall M, surface_atom M -> Pe M)
    (case_univ : forall M, Pe M -> Pe (surface_univ M))
    (case_succl : forall M, Pe M -> Pe (surface_succl M))
    (case_maxl : forall M N, Pe M -> Pe N -> Pe (surface_maxl M N))
    (case_absurd : forall C M, Pe C -> Pe M -> Pe (surface_absurd C M))
    (case_and : forall P Q, Pe P -> Pe Q -> Pe (surface_and P Q))
    (case_conj : forall P Q M N, Pe P -> Pe Q -> Pe M -> Pe N -> Pe (surface_conj P Q M N))
    (case_left : forall M, Pe M -> Pe (surface_left M))
    (case_right : forall M, Pe M -> Pe (surface_right M))
    (case_pi : forall A B, Pe A -> Pe B -> Pe (surface_pi A B))
    (case_fn : forall A M, Pe A -> Pe M -> Pe (surface_fn A M))
    (case_app : forall M N, Pe M -> Pe N -> Pe (surface_app M N))
    (case_let : forall b B, Pb b -> Pe B -> Pe (surface_let b B))
    (case_mem : forall H x, Pm H -> Pe (surface_mem H x))
    (case_proj_term : forall M x, Pe M -> Pe (surface_proj_term M x))
    (case_elim : forall m Bks M, List.Forall (surface_block_all Pe) Bks -> Pe M -> Pe (surface_elim m Bks M))
    (case_tuple : forall T fs, Pe T -> List.Forall (fun f => Pe (snd f)) fs -> Pe (surface_tuple T fs))
    (case_me_unit : forall fp, Pm (surface_me_unit fp))
    (case_me_var : forall k, Pm (surface_me_var k))
    (case_me_mem : forall H y, Pm H -> Pm (surface_me_mem H y))
    (case_me_app : forall H N, Pm H -> Pe N -> Pm (surface_me_app H N))
    (case_b_def : forall A M, Pe A -> Pe M -> Pb (surface_b_def A M))
    (case_b_mod : forall U, Pu U -> Pb (surface_b_mod U))
    (case_b_ind_alias : forall E, Pm E -> Pb (surface_b_ind_alias E))
    (case_b_record_alias : forall E, Pm E -> Pb (surface_b_record_alias E))
    (case_gu_mk : forall Δ D, List.Forall Pe Δ -> Pd D -> Pu (surface_gu_mk Δ D))
    (case_md_body : forall Φ, Pg Φ -> Pd (surface_md_body Φ))
    (case_md_alias : forall Et, Pm Et -> Pd (surface_md_alias Et))
    (case_gm_nil : Pg surface_gm_nil)
    (case_gm_ext : forall Φ x Ent, Pg Φ -> Pn Ent -> Pg (surface_gm_ext Φ x Ent))
    (case_gm_open : forall Φ H its, Pg Φ -> Pm H -> Pg (surface_gm_open Φ H its))
    (case_ge_def : forall b pv A oM, Pe A -> (forall M, oM = Some M -> Pe M) -> Pn (surface_ge_def b pv A oM))
    (case_ge_mod : forall pv U, Pu U -> Pn (surface_ge_mod pv U)).

  Fixpoint surface_exp_mut (M : surface_exp) : Pe M :=
    match M with
    | surface_typ n => case_atom (surface_typ n) I
    | surface_level n => case_atom (surface_level n) I
    | surface_llit o => case_atom (surface_llit o) I
    | surface_ntok => case_atom surface_ntok I
    | surface_nlit n => case_atom (surface_nlit n) I
    | surface_prop => case_atom surface_prop I
    | surface_True => case_atom surface_True I
    | surface_tt => case_atom surface_tt I
    | surface_False => case_atom surface_False I
    | surface_var x => case_atom (surface_var x) I
    | surface_hole => case_atom surface_hole I
    | surface_univ M => case_univ M (surface_exp_mut M)
    | surface_succl M => case_succl M (surface_exp_mut M)
    | surface_maxl M N => case_maxl M N (surface_exp_mut M) (surface_exp_mut N)
    | surface_absurd C M => case_absurd C M (surface_exp_mut C) (surface_exp_mut M)
    | surface_and P Q => case_and P Q (surface_exp_mut P) (surface_exp_mut Q)
    | surface_conj P Q M N => case_conj P Q M N (surface_exp_mut P) (surface_exp_mut Q) (surface_exp_mut M) (surface_exp_mut N)
    | surface_left M => case_left M (surface_exp_mut M)
    | surface_right M => case_right M (surface_exp_mut M)
    | surface_pi A B => case_pi A B (surface_exp_mut A) (surface_exp_mut B)
    | surface_fn A M => case_fn A M (surface_exp_mut A) (surface_exp_mut M)
    | surface_app M N => case_app M N (surface_exp_mut M) (surface_exp_mut N)
    | surface_let b B => case_let b B (surface_binding_mut b) (surface_exp_mut B)
    | surface_mem H x => case_mem H x (surface_modexp_mut H)
    | surface_proj_term M x => case_proj_term M x (surface_exp_mut M)
    | surface_elim m Bks0 M =>
        case_elim m Bks0 M
          ((fix blocks_mut (Bks : list surface_block) : List.Forall (surface_block_all Pe) Bks :=
              match Bks with
              | nil => List.Forall_nil _
              | cons (surface_eb_mk nm Z A Bs) Bks' =>
                  List.Forall_cons (surface_eb_mk nm Z A Bs)
                    (conj (surface_exp_mut Z)
                       (conj (surface_exp_mut A)
                          ((fix brs_mut (Bs : list (string * nat * surface_exp)) : List.Forall (fun b => Pe (snd b)) Bs :=
                              match Bs with
                              | nil => List.Forall_nil _
                              | cons b Bs' => List.Forall_cons b (surface_exp_mut (snd b)) (brs_mut Bs')
                              end) Bs)))
                    (blocks_mut Bks')
              end) Bks0)
          (surface_exp_mut M)
    | surface_tuple T fs0 =>
        case_tuple T fs0 (surface_exp_mut T)
          ((fix fields_mut (fs : list (string * surface_exp)) : List.Forall (fun f => Pe (snd f)) fs :=
              match fs with
              | nil => List.Forall_nil _
              | cons f fs' => List.Forall_cons f (surface_exp_mut (snd f)) (fields_mut fs')
              end) fs0)
    end
  with surface_modexp_mut (H : surface_modexp) : Pm H :=
    match H with
    | surface_me_unit fp => case_me_unit fp
    | surface_me_var k => case_me_var k
    | surface_me_mem H y => case_me_mem H y (surface_modexp_mut H)
    | surface_me_app H N => case_me_app H N (surface_modexp_mut H) (surface_exp_mut N)
    end
  with surface_binding_mut (b : surface_binding) : Pb b :=
    match b with
    | surface_b_def A M => case_b_def A M (surface_exp_mut A) (surface_exp_mut M)
    | surface_b_mod U => case_b_mod U (surface_unit_mut U)
    | surface_b_ind_alias E => case_b_ind_alias E (surface_modexp_mut E)
    | surface_b_record_alias E => case_b_record_alias E (surface_modexp_mut E)
    end
  with surface_unit_mut (U : surface_unit) : Pu U :=
    match U with
    | surface_gu_mk Δ0 D =>
        case_gu_mk Δ0 D
          ((fix tele_mut (Δ : list surface_exp) : List.Forall Pe Δ :=
              match Δ with
              | nil => List.Forall_nil _
              | cons A Δ' => List.Forall_cons _ (surface_exp_mut A) (tele_mut Δ')
              end) Δ0)
          (surface_moddef_mut D)
    end
  with surface_moddef_mut (D : surface_moddef) : Pd D :=
    match D with
    | surface_md_body Φ => case_md_body Φ (surface_body_mut Φ)
    | surface_md_alias E => case_md_alias E (surface_modexp_mut E)
    end
  with surface_body_mut (Φ : surface_body) : Pg Φ :=
    match Φ with
    | surface_gm_nil => case_gm_nil
    | surface_gm_ext Φ x E => case_gm_ext Φ x E (surface_body_mut Φ) (surface_entry_mut E)
    | surface_gm_open Φ H its => case_gm_open Φ H its (surface_body_mut Φ) (surface_modexp_mut H)
    end
  with surface_entry_mut (E : surface_entry) : Pn E :=
    match E with
    | surface_ge_def b pv A oM =>
        case_ge_def b pv A oM (surface_exp_mut A)
          (match oM as o return (forall M, o = Some M -> Pe M) with
           | Some M0 => fun M e => match e in _ = o' return match o' with Some M => Pe M | None => True end with
                                  | eq_refl => surface_exp_mut M0 end
           | None => fun M e => False_ind _ (match e in _ = o' return match o' with Some _ => False | None => True end with
                                | eq_refl => I end)
           end)
    | surface_ge_mod pv U => case_ge_mod pv U (surface_unit_mut U)
    end.

  Theorem surface_mut_ind :
    (forall M, Pe M) /\ (forall H, Pm H) /\ (forall b, Pb b) /\ (forall U, Pu U) /\
    (forall D, Pd D) /\ (forall Φ, Pg Φ) /\ (forall E, Pn E).
  Proof.
    repeat split; [ exact surface_exp_mut | exact surface_modexp_mut | exact surface_binding_mut | exact surface_unit_mut
                  | exact surface_moddef_mut | exact surface_body_mut | exact surface_entry_mut ].
  Qed.
End surface_mut_ind.

Section Decide.
  (** The fast context the typed checks look names up in
      ([Extraction.Lookup]); the fill decided is at the Core context it
      stands for. *)
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  (** The literals' binding *)
  Variable B : builtins.
  (** The decision of [levels_abstractable] the checker is given *)
  Variable levels_abstractable_dec : forall G Δ E, ⊢ Θ ⍮ Ξ ⍮ Δ ++ G -> Θ ⍮ Ξ ⍮ Δ ++ G ⊢ᵐ E ≈ E ->
      { levels_abstractable Θ Ξ G Δ E } + { ~ levels_abstractable Θ Ξ G Δ E }.
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** ** What the Fill Reads *)

  (** The type a term infers in a well-formed context. *)
  Definition infer_at (Γ : ctx) (M : exp) : option nf :=
    match check_ctx F levels_abstractable_dec Hg Γ with
    | left HΓ =>
        match type_infer F levels_abstractable_dec Γ HΓ M (type_infer_order_all M) with
        | inleft (exist _ W _) => Some W
        | inright _ => None
        end
    | right _ => None
    end.

  (** The type a term infers in a well-formed context, when the term is a
      type former of an inductive type ([ind] true, [ind_former]) or of a
      record type ([ind] false, [record_former]) at it. *)
  Definition former_at (ind : bool) (Γ : ctx) (M : exp) : option nf :=
    match check_ctx F levels_abstractable_dec Hg Γ with
    | left HΓ =>
        match type_infer F levels_abstractable_dec Γ HΓ M (type_infer_order_all M) with
        | inleft (exist _ W HW) =>
            if ind
            then if ind_former_dec F Γ M W (alg_type_infer_sound HW HΓ) then Some W else None
            else if record_former_dec F Γ M W (alg_type_infer_sound HW HΓ) then Some W else None
        | inright _ => None
        end
    | right _ => None
    end.

  (** Whether the binder [k] of [Γ] holds a term. *)
  Definition term_binder_b (Γ : ctx) (k : nat) : bool :=
    match List.nth_error Γ k with
    | Some (ce_ass _ _) | Some (ce_def _ _) => true
    | _ => false
    end.

  (** Whether the member [y] of [H] is a term. *)
  Definition member_term_b (Γ : ctx) (H : modexp) (y : string) : bool :=
    match mdenote_dec F Hg Γ (me_mem H y) with
    | inleft (exist _ (fmdesc_term _ _ _) _) => true
    | _ => false
    end.

  (** The privacy violation of selecting [y] from a record value's module,
      if any. *)
  Definition sel_check (op : option qname) (y : string) : option (qname * string) :=
    match op with
    | None => None
    | Some p =>
        match glob_check F Hg (qname_mod p) y with
        | inleft (exist _ qx _) => Some qx
        | inright _ => None
        end
    end.

  (** Each of [ys] selected from a record value's module is accessible. *)
  Fixpoint sels_check (op : option qname) (ys : list string) : fill_result unit :=
    match ys with
    | nil => fill_ok tt
    | y :: ys' =>
        match sel_check op y with
        | Some (qd, x) => fill_error (fill_failure_private qd x)
        | None => sels_check op ys'
        end
    end.

  (** The expansion of a body. *)
  Definition body_xp_fn (Γ : ctx) (Φ : gmod) : fill_result gmod :=
    match body_xp_dec F Hg Γ Φ with
    | inleft (exist _ Φx _) => fill_ok Φx
    | inright _ => fill_error (fill_failure_body Γ Φ)
    end.

  (** Every module expression has the termination order of what a local
      open of it generates ([MemberOrder.order_bounded]). *)
  Lemma items_gen_order_any : forall Γ H its, items_gen_order Θ Ξ Γ H its.
  Proof.
    intros; apply (proj2 (proj2 (proj2 (proj2 (order_bounded Θ Ξ Hg (S (S (S (modexp_size (ctx_sizes Γ) H))))))))); lia.
  Qed.

  (** The definitions a local open of [H] generates. *)
  Definition items_gen_fn (Γ : ctx) (H : modexp) (its : list import_item) : fill_result (list generated_item) :=
    match items_gen_impl F Hg Γ H its (items_gen_order_any Γ H its) with
    | inleft (exist _ gs _) => fill_ok gs
    | inright _ => fill_error (fill_failure_body Γ (gm_open gm_nil H its gm_nil))
    end.

  (** A module expression, in module position, read as [r]: the module it
      is, with the record it is the module of a value of, if it has a term
      at its head.  [y] names what is selected from it, for the error; with
      nothing selected ([y] empty), a term of no record type stands where
      a module does. *)
  Definition fill_mod_of (Γ : ctx) (y : string) (r : fill_result module_read) : fill_result (modexp * option qname)%type :=
    match r with
    | fill_error e => fill_error e
    | fill_ok (read_module H') => fill_ok (H', None)
    | fill_ok (read_term M) =>
        match infer_at Γ M with
        | Some (nf_record p Rs) => fill_ok (record_value_module p Rs M, Some p)
        | Some W => fill_error (if String.eqb y "" then fill_failure_not_module Γ M else fill_failure_not_record y Γ M W)
        | None => fill_error (if String.eqb y "" then fill_failure_not_module Γ M else fill_failure_no_type y Γ M)
        end
    end.

  (** The kind of a filled type: that of the sort it infers to
      ([sort_abs_kind]). *)
  Definition kind_at (Γ : ctx) (A : exp) (what : string) : fill_result abs_kind :=
    match infer_at Γ A with
    | Some W => fill_ok (sort_abs_kind W)
    | None => fill_error (fill_failure_no_kind what Γ A)
    end.

  (** ** The Fill, Computed *)

  Fixpoint fill_exp_fn (Γ : ctx) (M : surface_exp) {struct M} : fill_result exp :=
    match M with
    | surface_typ n => fill_ok (a_typ n)
    | surface_level n => fill_ok (a_level n)
    | surface_llit o => fill_ok (a_llit o)
    | surface_prop => fill_ok a_prop
    | surface_True => fill_ok a_True
    | surface_tt => fill_ok a_tt
    | surface_False => fill_ok a_False
    | surface_var x => fill_ok (a_var x)
    | surface_hole => fill_error (fill_failure_message "an annotation is omitted where it may not be")
    | surface_nlit n =>
        match nat_view_f F B with
        | Some (p, z, s) => fill_ok (nat_chain p z s n)
        | None => fill_error (fill_failure_literal (literal_failure_reason_numeral n))
        end
    | surface_ntok =>
        match nat_view_f F B with
        | Some (p, _, _) => fill_ok (a_ind p 0)
        | None => fill_error (fill_failure_literal literal_failure_reason_token)
        end
    | surface_univ M0 => let%a M' := fill_exp_fn Γ M0 in fill_ok (a_univ M')
    | surface_succl M0 => let%a M' := fill_exp_fn Γ M0 in fill_ok (a_succl M')
    | surface_maxl M0 N0 =>
        let%a M' := fill_exp_fn Γ M0 in
        let%a N' := fill_exp_fn Γ N0 in
        fill_ok (a_maxl M' N')
    | surface_absurd C M0 =>
        let%a C' := fill_exp_fn Γ C in
        let%a M' := fill_exp_fn Γ M0 in
        fill_ok (a_absurd C' M')
    | surface_pi A B0 =>
        let%a A' := fill_exp_fn Γ A in
        let%a κA := kind_at Γ A' "the domain of a Π" in
        let%a B' := fill_exp_fn (Γ ▹{κA} A') B0 in
        let%a κB := kind_at (Γ ▹{κA} A') B' "the codomain of a Π" in
        fill_ok (a_pi κA κB A' B')
    | surface_and P Q =>
        let%a P' := fill_exp_fn Γ P in
        let%a Q' := fill_exp_fn (Γ ▹{ak_propositional} P') Q in
        fill_ok (a_and P' Q')
    | surface_conj P Q M0 N0 =>
        let%a P' := fill_exp_fn Γ P in
        let%a M' := fill_exp_fn Γ M0 in
        let%a N' := fill_exp_fn Γ N0 in
        if is_surface_hole Q then
          match infer_at Γ N' with
          | Some W => fill_ok (a_conj P' (exp_wk (nf_to_exp W) wk_shift) M' N')
          | None => fill_error (fill_failure_message "the second component of a proof of a conjunction infers no type")
          end
        else
          let%a Q' := fill_exp_fn (Γ ▹{ak_propositional} P') Q in
          fill_ok (a_conj P' Q' M' N')
    | surface_left M0 => let%a M' := fill_exp_fn Γ M0 in fill_ok (a_left M')
    | surface_right M0 => let%a M' := fill_exp_fn Γ M0 in fill_ok (a_right M')
    | surface_fn A M0 =>
        let%a A' := fill_exp_fn Γ A in
        let%a κA := kind_at Γ A' "the domain of a λ" in
        let%a M' := fill_exp_fn (Γ ▹{κA} A') M0 in
        fill_ok (a_fn A' M')
    | surface_app M0 N0 =>
        let%a M' := fill_exp_fn Γ M0 in
        let%a N' := fill_exp_fn Γ N0 in
        fill_ok (a_app M' N')
    | surface_let (surface_b_def A M0) B0 =>
        let%a M' := fill_exp_fn Γ M0 in
        if is_surface_hole A then
          match infer_at Γ M' with
          | Some W =>
              let%a B' := fill_exp_fn (Γ ▸ nf_to_exp W ≔ M') B0 in
              fill_ok (a_let (b_def (nf_to_exp W) M') B')
          | None => fill_error (fill_failure_message "the definition of an unannotated let infers no type")
          end
        else
          let%a A' := fill_exp_fn Γ A in
          let%a B' := fill_exp_fn (Γ ▸ A' ≔ M') B0 in
          fill_ok (a_let (b_def A' M') B')
    | surface_let (surface_b_mod U) B0 =>
        let%a U' := fill_unit_fn Γ U in
        let%a B' := fill_exp_fn (Γ ▹ₘ U') B0 in
        fill_ok (a_let (b_mod U') B')
    | surface_let (surface_b_ind_alias E) B0 =>
        let%a r := fill_mod_of Γ "" (fill_read_fn Γ E) in
        match snd r, modexp_as_term (fst r) with
        | None, Some M =>
            match former_at true Γ M with
            | Some W =>
                let%a B' := fill_exp_fn (Γ ▸ₘ nf_to_exp W ≔ M ‖ gu_mk nil (md_alias (fst r))) B0 in
                fill_ok (a_let (b_def_mod (nf_to_exp W) M (gu_mk nil (md_alias (fst r)))) B')
            | None => fill_error (fill_failure_message "the target of a local inductive alias is no type former of an inductive type")
            end
        | _, _ => fill_error (fill_failure_message "the target of a local inductive alias is no type former of an inductive type")
        end
    | surface_let (surface_b_record_alias E) B0 =>
        let%a r := fill_mod_of Γ "" (fill_read_fn Γ E) in
        match snd r, modexp_as_term (fst r) with
        | None, Some M =>
            match former_at false Γ M with
            | Some W =>
                let%a B' := fill_exp_fn (Γ ▸ₘ nf_to_exp W ≔ M ‖ gu_mk nil (md_alias (fst r))) B0 in
                fill_ok (a_let (b_def_mod (nf_to_exp W) M (gu_mk nil (md_alias (fst r)))) B')
            | None => fill_error (fill_failure_message "the target of a local record alias is no type former of a record type")
            end
        | _, _ => fill_error (fill_failure_message "the target of a local record alias is no type former of a record type")
        end
    | surface_mem H x =>
        let%a r := fill_mod_of Γ x (fill_read_fn Γ H) in
        match sel_check (snd r) x with
        | Some (qd, y) => fill_error (fill_failure_private qd y)
        | None => fill_ok (a_mem (fst r) x)
        end
    | surface_proj_term M0 x =>
        let%a M' := fill_exp_fn Γ M0 in
        match infer_at Γ M' with
        | Some (nf_record p Rs) =>
            match sel_check (Some p) x with
            | Some (qd, y) => fill_error (fill_failure_private qd y)
            | None => fill_ok (a_mem (record_value_module p Rs M') x)
            end
        | Some W => fill_error (fill_failure_not_record x Γ M' W)
        | None => fill_error (fill_failure_no_type x Γ M')
        end
    | surface_tuple T fs =>
        let%a T' := fill_exp_fn Γ T in
        let%a fs' :=
          (fix fields (fs : list (string * surface_exp)) : fill_result (list (string * exp)) :=
             match fs with
             | nil => fill_ok nil
             | (f, N) :: fs0 =>
                 let%a N' := fill_exp_fn Γ N in
                 let%a fs0' := fields fs0 in
                 fill_ok ((f, N') :: fs0')
             end) fs in
        fill_ok (a_tuple T' fs')
    | surface_elim m Bks M0 =>
        let%a M' := fill_exp_fn Γ M0 in
        match infer_at Γ M' with
        | Some (nf_indty pc k Rs) =>
            match elim_target_f F pc k Rs m (surface_block_names Bks) with
            | elim_target_one p Us =>
                match fc_ind F p with
                | None => fill_error (fill_failure_message "internal error: an eliminator of no group")
                | Some D =>
                    (** first each block's scrutinee's type and motive, at
                        the uniform parameters *)
                    let%a hs :=
                      (fix heads (j : nat) (Bks : list surface_block) : fill_result (list (exp * exp)) :=
                         match Bks with
                         | nil => fill_ok nil
                         | surface_eb_mk nm Z A Bs :: Bks0 =>
                             match ind_member D j with
                             | None => fill_error (fill_failure_message "an eliminator with more blocks than its group has members")
                             | Some Mj =>
                                 if Nat.eqb nm (S (im_nn Mj)) then
                                   let%a Z' :=
                                     if is_surface_hole Z then fill_ok (member_scrutinee_type p D j Mj Us)
                                     else fill_exp_fn (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z in
                                   let%a A' := fill_exp_fn (elim_mctx p D j Mj Us ++ Γ) A in
                                   let%a hs0 := heads (S j) Bks0 in
                                   fill_ok ((Z', A') :: hs0)
                                 else fill_error (fill_failure_message "a block of an eliminator binds the wrong number of variables")
                             end
                         end) 0 Bks in
                    let As := List.map snd hs in
                    (** then the tag, the sort the filled motive of the
                        scrutinee's member infers to *)
                    match ind_member D m, List.nth_error As m with
                    | Some Mm, Some Am =>
                        match infer_at (elim_mctx p D m Mm Us ++ Γ) Am with
                        | Some W =>
                            let r := sort_abs_kind W in
                            (** then the branches, at the filled motives of
                                all the blocks and at the tag *)
                            let%a Bks' :=
                              (fix blocks (j : nat) (Bks : list surface_block) (rest : list (exp * exp)) : fill_result (list eblock) :=
                                 match Bks, rest with
                                 | nil, _ => fill_ok nil
                                 | surface_eb_mk nm _ _ Bs :: Bks0, (Z', A') :: rest0 =>
                                     match ind_member D j with
                                     | None => fill_error (fill_failure_message "an eliminator with more blocks than its group has members")
                                     | Some Mj =>
                                         let%a Bs' :=
                                           (fix brs (Bs : list (string * nat * surface_exp)) : fill_result (list (string * nat * exp)) :=
                                              match Bs with
                                              | nil => fill_ok nil
                                              | (c, n, B0) :: Bs0 =>
                                                  match ind_con Mj c with
                                                  | None => fill_error (fill_failure_message ("a branch of no constructor " ++ c))
                                                  | Some gs =>
                                                      if Nat.eqb n (im_nn Mj + List.length gs + cargs_nrec D gs) then
                                                        let%a B' := fill_exp_fn (elim_bctx r p D Mj gs As Us ++ Γ) B0 in
                                                        let%a Bs0' := brs Bs0 in
                                                        fill_ok ((c, n, B') :: Bs0')
                                                      else fill_error (fill_failure_branch_arity c n (im_nn Mj) (List.length gs) (cargs_nrec D gs))
                                                  end
                                              end) Bs in
                                         let%a Bks0' := blocks (S j) Bks0 rest0 in
                                         fill_ok (eb_mk nm Z' A' Bs' :: Bks0')
                                     end
                                 | _ :: _, nil => fill_error (fill_failure_message "internal error: a block without its motive")
                                 end) 0 Bks hs in
                            fill_ok (a_elim r p Us m Bks' M')
                        | None => fill_error (fill_failure_message "the motive of an eliminator infers no type")
                        end
                    | _, _ => fill_error (fill_failure_message "an eliminator with no block for its scrutinee's member")
                    end
                end
            | elim_target_ambiguous rs => fill_error (fill_failure_elim_ambiguous Γ M' rs)
            | elim_target_none => fill_error (fill_failure_elim_none Γ pc k Rs m (surface_block_names Bks) M')
            end
        | W => fill_error (fill_failure_elim_scrutinee Γ M' W)
        end
    end

  with fill_read_fn (Γ : ctx) (H : surface_modexp) {struct H} : fill_result module_read :=
    match H with
    | surface_me_unit fp => fill_ok (read_module (me_unit fp))
    | surface_me_var k => if term_binder_b Γ k then fill_ok (read_term (a_var k)) else fill_ok (read_module (me_var k))
    | surface_me_mem H0 y =>
        let%a r := fill_mod_of Γ y (fill_read_fn Γ H0) in
        match sel_check (snd r) y with
        | Some (qd, x) => fill_error (fill_failure_private qd x)
        | None =>
            if member_term_b Γ (fst r) y then fill_ok (read_term (a_mem (fst r) y))
            else fill_ok (read_module (me_mem (fst r) y))
        end
    | surface_me_app H0 N =>
        let%a r := fill_read_fn Γ H0 in
        let%a N' := fill_exp_fn Γ N in
        match r with
        | read_module H' => fill_ok (read_module (me_app H' N'))
        | read_term M => fill_ok (read_term (a_app M N'))
        end
    end

  with fill_unit_fn (Γ : ctx) (U : surface_unit) {struct U} : fill_result gunit :=
    match U with
    | surface_gu_mk Δ D =>
        let%a Δ' :=
          (fix tele (Δ : list surface_exp) : fill_result ctx :=
             match Δ with
             | nil => fill_ok nil
             | A :: Δ0 =>
                 let%a Δ0' := tele Δ0 in
                 let%a A' := fill_exp_fn (Δ0' ++ Γ) A in
                 let%a κ := kind_at (Δ0' ++ Γ) A' "the type of a parameter" in
                 fill_ok (ce_ass κ A' :: Δ0')
             end) Δ in
        let%a D' := fill_def_fn (Δ' ++ Γ) D in
        fill_ok (gu_mk Δ' D')
    end

  with fill_def_fn (Γ : ctx) (D : surface_moddef) {struct D} : fill_result moddef :=
    match D with
    | surface_md_alias E => let%a r := fill_mod_of Γ "" (fill_read_fn Γ E) in fill_ok (md_alias (fst r))
    | surface_md_body Φ => let%a Φ' := fill_body_fn Γ Φ in fill_ok (md_body sm_open Φ')
    end

  with fill_body_fn (Γ : ctx) (Φ : surface_body) {struct Φ} : fill_result gmod :=
    match Φ with
    | surface_gm_nil => fill_ok gm_nil
    | surface_gm_ext Φ0 x E =>
        let%a Φ0' := fill_body_fn Γ Φ0 in
        let%a Φx := body_xp_fn Γ Φ0' in
        match E with
        | surface_ge_def b pv A oM =>
            let%a A' := fill_exp_fn (body_ctx Φx ++ Γ) A in
            let%a oM' :=
              match oM with
              | None => fill_ok None
              | Some M => let%a M' := fill_exp_fn (body_ctx Φx ++ Γ) M in fill_ok (Some M')
              end in
            (** its kind, that of the sort its filled type infers to *)
            let%a κ := kind_at (body_ctx Φx ++ Γ) A' "the type of a definition of a local body" in
            fill_ok (gm_ext Φ0' x (ge_def b pv κ A' oM'))
        | surface_ge_mod pv U =>
            let%a U' := fill_unit_fn (body_ctx Φx ++ Γ) U in
            fill_ok (gm_ext Φ0' x (ge_mod pv U'))
        end
    | surface_gm_open Φ0 H its =>
        let%a Φ0' := fill_body_fn Γ Φ0 in
        let%a Φx := body_xp_fn Γ Φ0' in
        let%a r := fill_mod_of (body_ctx Φx ++ Γ) "" (fill_read_fn (body_ctx Φx ++ Γ) H) in
        let%a _ := sels_check (snd r) (items_members its) in
        let%a gs := items_gen_fn (body_ctx Φx ++ Γ) (fst r) its in
        fill_ok (gm_open Φ0' (fst r) its (gens_body gs))
    end.

  (** A module expression in module position. *)
  Definition fill_mod_fn (Γ : ctx) (y : string) (H : surface_modexp) : fill_result (modexp * option qname)%type :=
    fill_mod_of Γ y (fill_read_fn Γ H).

  (** A telescope of assumptions, innermost first, each over the filled
      ones after it, at the kind of the sort its filled type infers to. *)
  Fixpoint fill_tele_fn (Γ : ctx) (Δ : list surface_exp) : fill_result ctx :=
    match Δ with
    | nil => fill_ok nil
    | A :: Δ0 =>
        let%a Δ0' := fill_tele_fn Γ Δ0 in
        let%a A' := fill_exp_fn (Δ0' ++ Γ) A in
        let%a κ := kind_at (Δ0' ++ Γ) A' "the type of a parameter" in
        fill_ok (ce_ass κ A' :: Δ0')
    end.

  (** Named types, outermost first, each over the filled ones before it,
      at the kind of the sort its filled type infers to. *)
  Fixpoint fill_fields_with (kind : ctx -> exp -> string -> fill_result abs_kind) (Γ : ctx) (fs : list (string * surface_exp)) :
      fill_result (list (string * abs_kind * typ)) :=
    match fs with
    | nil => fill_ok nil
    | (f, T) :: fs0 =>
        let%a T' := fill_exp_fn Γ T in
        let%a κ := kind Γ T' "the type of a field" in
        let%a fs0' := fill_fields_with kind (Γ ▹{κ} T') fs0 in
        fill_ok ((f, κ, T') :: fs0')
    end.

  (** The fill of named types: at the kinds of their sorts ([kind_at]) *)
  #[local] Abbreviation fill_fields_fn := (fill_fields_with kind_at).

  (** A term that may be absent. *)
  Definition fill_optional_exp_fn (Γ : ctx) (oM : option surface_exp) : fill_result (option exp) :=
    match oM with
    | None => fill_ok None
    | Some M => let%a M' := fill_exp_fn Γ M in fill_ok (Some M')
    end.

  (** ** The Loops of the Fill

      The loops [fill_exp_fn] runs over the lists inside a term, named, so
      that what they compute can be stated. *)

  (** The fields of a record value. *)
  Definition field_vals_fn (Γ : ctx) :=
    fix fields (fs : list (string * surface_exp)) : fill_result (list (string * exp)) :=
      match fs with
      | nil => fill_ok nil
      | (f, N) :: fs0 =>
          let%a N' := fill_exp_fn Γ N in
          let%a fs0' := fields fs0 in
          fill_ok ((f, N') :: fs0')
      end.

  (** The scrutinee's type of the block of the member [j], [Mj]: the
      member's type when omitted. *)
  Definition scrutinee_type_fn (Γ : ctx) (p : qname) (D : ind_decl) (j : nat) (Mj : imember) (Us : list exp) (Z : surface_exp) :=
    if is_surface_hole Z then fill_ok (member_scrutinee_type p D j Mj Us)
    else fill_exp_fn (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z.

  (** Each block's scrutinee's type and motive. *)
  Definition heads_fn (Γ : ctx) (p : qname) (D : ind_decl) (Us : list exp) :=
    fix heads (j : nat) (Bks : list surface_block) : fill_result (list (exp * exp)) :=
      match Bks with
      | nil => fill_ok nil
      | surface_eb_mk nm Z A Bs :: Bks0 =>
          match ind_member D j with
          | None => fill_error (fill_failure_message "an eliminator with more blocks than its group has members")
          | Some Mj =>
              if Nat.eqb nm (S (im_nn Mj)) then
                let%a Z' := scrutinee_type_fn Γ p D j Mj Us Z in
                let%a A' := fill_exp_fn (elim_mctx p D j Mj Us ++ Γ) A in
                let%a hs0 := heads (S j) Bks0 in
                fill_ok ((Z', A') :: hs0)
              else fill_error (fill_failure_message "a block of an eliminator binds the wrong number of variables")
          end
      end.

  (** A block's branches, at the motives [As] and the tag [r]. *)
  Definition brs_fn (Γ : ctx) (r : abs_kind) (p : qname) (D : ind_decl) (Mj : imember) (As Us : list exp) :=
    fix brs (Bs : list (string * nat * surface_exp)) : fill_result (list (string * nat * exp)) :=
      match Bs with
      | nil => fill_ok nil
      | (c, n, B0) :: Bs0 =>
          match ind_con Mj c with
          | None => fill_error (fill_failure_message ("a branch of no constructor " ++ c))
          | Some gs =>
              if Nat.eqb n (im_nn Mj + List.length gs + cargs_nrec D gs) then
                let%a B' := fill_exp_fn (elim_bctx r p D Mj gs As Us ++ Γ) B0 in
                let%a Bs0' := brs Bs0 in
                fill_ok ((c, n, B') :: Bs0')
              else fill_error (fill_failure_branch_arity c n (im_nn Mj) (List.length gs) (cargs_nrec D gs))
          end
      end.

  (** The blocks, their scrutinees' types and motives filled as [hs], and
      the motives of all of them [As], at the tag [r]. *)
  Definition blocks_fn (Γ : ctx) (r : abs_kind) (p : qname) (D : ind_decl) (As Us : list exp) :=
    fix blocks (j : nat) (Bks : list surface_block) (rest : list (exp * exp)) : fill_result (list eblock) :=
      match Bks, rest with
      | nil, _ => fill_ok nil
      | surface_eb_mk nm _ _ Bs :: Bks0, (Z', A') :: rest0 =>
          match ind_member D j with
          | None => fill_error (fill_failure_message "an eliminator with more blocks than its group has members")
          | Some Mj =>
              let%a Bs' := brs_fn Γ r p D Mj As Us Bs in
              let%a Bks0' := blocks (S j) Bks0 rest0 in
              fill_ok (eb_mk nm Z' A' Bs' :: Bks0')
          end
      | _ :: _, nil => fill_error (fill_failure_message "internal error: a block without its motive")
      end.

  (** An eliminator as written, its scrutinee filled to [M'] in [Γ]: the
      one reading that fits its blocks, then its blocks at it, their
      scrutinees' types and motives first, then its tag, the sort the
      filled motive of the scrutinee's member infers to, then their
      branches at the filled motives and the tag. *)
  Definition elim_fill_fn (Γ : ctx) (m : nat) (Bks : list surface_block) (M' : exp) : fill_result exp :=
    match infer_at Γ M' with
    | Some (nf_indty pc k Rs) =>
        match elim_target_f F pc k Rs m (surface_block_names Bks) with
        | elim_target_one p Us =>
            match fc_ind F p with
            | None => fill_error (fill_failure_message "internal error: an eliminator of no group")
            | Some D =>
                let%a hs := heads_fn Γ p D Us 0 Bks in
                let As := List.map snd hs in
                match ind_member D m, List.nth_error As m with
                | Some Mm, Some Am =>
                    match infer_at (elim_mctx p D m Mm Us ++ Γ) Am with
                    | Some W =>
                        let r := sort_abs_kind W in
                        let%a Bks' := blocks_fn Γ r p D As Us 0 Bks hs in
                        fill_ok (a_elim r p Us m Bks' M')
                    | None => fill_error (fill_failure_message "the motive of an eliminator infers no type")
                    end
                | _, _ => fill_error (fill_failure_message "an eliminator with no block for its scrutinee's member")
                end
            end
        | elim_target_ambiguous rs => fill_error (fill_failure_elim_ambiguous Γ M' rs)
        | elim_target_none => fill_error (fill_failure_elim_none Γ pc k Rs m (surface_block_names Bks) M')
        end
    | W => fill_error (fill_failure_elim_scrutinee Γ M' W)
    end.

  (** An eliminator as written, through the named loops. *)
  Lemma fill_exp_fn_elim : forall Γ m Bks M0,
      fill_exp_fn Γ (surface_elim m Bks M0) = let%a M' := fill_exp_fn Γ M0 in elim_fill_fn Γ m Bks M'.
  Proof. reflexivity. Qed.

  (** A record value, through the named loop. *)
  Lemma fill_exp_fn_tuple : forall Γ T fs,
      fill_exp_fn Γ (surface_tuple T fs) = let%a T' := fill_exp_fn Γ T in let%a fs' := field_vals_fn Γ fs in fill_ok (a_tuple T' fs').
  Proof. reflexivity. Qed.

  (** A unit, through [fill_tele_fn]. *)
  Lemma fill_unit_fn_mk : forall Γ Δ D,
      fill_unit_fn Γ (surface_gu_mk Δ D) =
        let%a Δ' := fill_tele_fn Γ Δ in let%a D' := fill_def_fn (Δ' ++ Γ) D in fill_ok (gu_mk Δ' D').
  Proof.
    intros; cbn [fill_unit_fn]; f_equal.
    induction Δ as [| A Δ IH]; cbn; [ reflexivity | rewrite IH; reflexivity ].
  Qed.

  (** ** What the Fill Reads, Specified *)

  (** The inference found, at the global context the fill relation reads
      it at ([gc_mk Θ Ξ], [fc_gctx_eta]) *)
  Lemma infer_at_sound : forall Γ M W, infer_at Γ M = Some W -> ⊢ Θ ⍮ Ξ ⍮ Γ /\ @alg_type_infer (gc_mk Θ Ξ) Γ W M.
  Proof.
    intros * E; unfold infer_at in E.
    destruct (check_ctx F levels_abstractable_dec Hg Γ) as [HΓ |]; [| discriminate ].
    destruct (type_infer F levels_abstractable_dec Γ HΓ M (type_infer_order_all M)) as [[W0 HW] |]; [| discriminate ].
    injection E as <-; rewrite (fc_gctx_eta F) in HW; split; assumption.
  Qed.

  Lemma infer_at_complete : forall Γ M W, ⊢ Θ ⍮ Ξ ⍮ Γ -> @alg_type_infer (gc_mk Θ Ξ) Γ W M -> infer_at Γ M = Some W.
  Proof.
    intros * HΓ HW; rewrite <- (fc_gctx_eta F) in HW; unfold infer_at.
    destruct (check_ctx F levels_abstractable_dec Hg Γ) as [HΓ' | Hn]; [| contradiction ].
    destruct (type_infer F levels_abstractable_dec Γ HΓ' M (type_infer_order_all M)) as [[W0 HW0] | Hn];
      [| exfalso; exact (Hn _ HW) ].
    rewrite (@functional_alg_type_infer (fc_gctx F) _ _ _ _ Hg HW0 HW); reflexivity.
  Qed.

  (** What [former_at] decides: the inference and the former check. *)
  Definition former_of (ind : bool) (Γ : ctx) (M : exp) (W : nf) : Prop :=
    if ind then ind_former Θ Ξ Γ M W else record_former Θ Ξ Γ M W.

  Lemma former_at_sound : forall ind Γ M W, former_at ind Γ M = Some W ->
      ⊢ Θ ⍮ Ξ ⍮ Γ /\ @alg_type_infer (gc_mk Θ Ξ) Γ W M /\ former_of ind Γ M W.
  Proof.
    intros * E; unfold former_at in E.
    destruct (check_ctx F levels_abstractable_dec Hg Γ) as [HΓ |]; [| discriminate ].
    destruct (type_infer F levels_abstractable_dec Γ HΓ M (type_infer_order_all M)) as [[W0 HW] |]; [| discriminate ].
    destruct ind; cbn [former_of];
      [ destruct (ind_former_dec F Γ M W0 (alg_type_infer_sound HW HΓ)) as [Hf |]
      | destruct (record_former_dec F Γ M W0 (alg_type_infer_sound HW HΓ)) as [Hf |] ]; try discriminate;
      injection E as <-; rewrite (fc_gctx_eta F) in HW; repeat split; assumption.
  Qed.

  Lemma former_at_complete : forall ind Γ M W, ⊢ Θ ⍮ Ξ ⍮ Γ -> @alg_type_infer (gc_mk Θ Ξ) Γ W M ->
      former_of ind Γ M W -> former_at ind Γ M = Some W.
  Proof.
    intros * HΓ HW Hf; rewrite <- (fc_gctx_eta F) in HW; unfold former_at.
    destruct (check_ctx F levels_abstractable_dec Hg Γ) as [HΓ' | Hn]; [| contradiction ].
    destruct (type_infer F levels_abstractable_dec Γ HΓ' M (type_infer_order_all M)) as [[W0 HW0] | Hn];
      [| exfalso; exact (Hn _ HW) ].
    pose proof (@functional_alg_type_infer (fc_gctx F) _ _ _ _ Hg HW0 HW) as <-.
    destruct ind; cbn [former_of] in Hf;
      [ destruct (ind_former_dec F Γ M W0 (alg_type_infer_sound HW0 HΓ')) as [| Hn]
      | destruct (record_former_dec F Γ M W0 (alg_type_infer_sound HW0 HΓ')) as [| Hn] ];
      [ reflexivity | contradiction | reflexivity | contradiction ].
  Qed.

  Lemma kind_at_sound : forall Γ A what κ, kind_at Γ A what = fill_ok κ ->
      exists W, κ = sort_abs_kind W /\ ⊢ Θ ⍮ Ξ ⍮ Γ /\ @alg_type_infer (gc_mk Θ Ξ) Γ W A.
  Proof.
    intros * E; unfold kind_at in E; destruct (infer_at Γ A) as [W |] eqn:Ei; [| discriminate ].
    injection E as <-; apply infer_at_sound in Ei as [HΓ HW]; eauto.
  Qed.

  Lemma kind_at_complete : forall Γ A what W, ⊢ Θ ⍮ Ξ ⍮ Γ -> @alg_type_infer (gc_mk Θ Ξ) Γ W A ->
      kind_at Γ A what = fill_ok (sort_abs_kind W).
  Proof. intros * HΓ HW; unfold kind_at; rewrite (infer_at_complete _ _ _ HΓ HW); reflexivity. Qed.

  Lemma term_binder_b_spec : forall Γ k, term_binder_b Γ k = true <-> term_binder Γ k.
  Proof.
    intros; unfold term_binder_b, term_binder.
    destruct (List.nth_error Γ k) as [[] |]; split; intros H; first [ exact I | reflexivity | discriminate | destruct H ].
  Qed.

  Lemma member_term_b_spec : forall Γ H y,
      member_term_b Γ H y = true <-> exists r A oM, mdenote Θ Ξ Γ (me_mem H y) (mdesc_term r A oM).
  Proof.
    intros; unfold member_term_b.
    destruct (mdenote_dec F Hg Γ (me_mem H y)) as [[R HR] | Hn].
    - destruct R; split; intros E; try discriminate; eauto;
        destruct E as (r & A & oM & HA); pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ HA); discriminate.
    - split; [ discriminate | intros (r & A & oM & HA); exfalso; exact (Hn _ HA) ].
  Qed.

  Lemma sel_check_spec : forall op y, sel_check op y = None <-> sel_ok Θ Ξ op y.
  Proof.
    intros [p |] y; cbn; [| split; auto ].
    destruct (glob_check F Hg (qname_mod p) y) as [[qx Hn] | Hok]; split; auto; [ discriminate | contradiction ].
  Qed.

  Lemma sels_check_spec : forall op ys, sels_check op ys = fill_ok tt <-> Forall (sel_ok Θ Ξ op) ys.
  Proof.
    intros op; induction ys as [| y ys IH]; cbn; [ split; auto |].
    destruct (sel_check op y) as [[qd x] |] eqn:E.
    - split; [ discriminate | intros Hf; inversion Hf; subst; apply sel_check_spec in H1; congruence ].
    - rewrite IH, Forall_cons_iff; apply sel_check_spec in E; tauto.
  Qed.

  Lemma body_xp_fn_spec : forall Γ Φ Φx, body_xp_fn Γ Φ = fill_ok Φx <-> body_xp Θ Ξ Γ Φ Φx.
  Proof.
    intros; unfold body_xp_fn; destruct (body_xp_dec F Hg Γ Φ) as [[Φx0 HΦ] | Hn]; split; try discriminate.
    - intros [= <-]; exact HΦ.
    - intros HΦ'; f_equal; exact (proj1 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ HΦ _ HΦ').
    - intros HΦ'; exfalso; exact (Hn _ HΦ').
  Qed.

  Lemma items_gen_fn_spec : forall Γ H its gs, items_gen_fn Γ H its = fill_ok gs <-> items_gen Θ Ξ Γ H its gs.
  Proof.
    intros; unfold items_gen_fn; destruct (items_gen_impl F Hg Γ H its _) as [[gs0 Hgs] | Hn]; split; try discriminate.
    - intros [= <-]; exact Hgs.
    - intros Hgs'; f_equal; exact (proj2 (proj2 (proj2 (proj2 (mdenote_functional_all _ _ Hg)))) _ _ _ _ Hgs _ Hgs').
    - intros Hgs'; exfalso; exact (Hn _ Hgs').
  Qed.

  (** A read module expression, as a module. *)
  Lemma fill_mod_of_sound : forall Γ y r H' op,
      fill_mod_of Γ y (fill_ok r) = fill_ok (H', op) ->
      match r with
      | read_module H0 => H' = H0 /\ op = None
      | read_term M => ⊢ Θ ⍮ Ξ ⍮ Γ /\ exists p Rs, @alg_type_infer (gc_mk Θ Ξ) Γ (nf_record p Rs) M /\ H' = record_value_module p Rs M /\ op = Some p
      end.
  Proof.
    intros * E; destruct r as [H0 | M]; cbn in E; [ injection E as <- <-; auto |].
    destruct (infer_at Γ M) as [W |] eqn:Ei; [| discriminate ].
    apply infer_at_sound in Ei as [HΓ HW].
    destruct W; try discriminate; injection E as <- <-; eauto 6.
  Qed.

  (** ** The Computed Fill Is the Relation's *)

  Definition exp_fill_sound (M : surface_exp) : Prop :=
    forall Γ M', fill_exp_fn Γ M = fill_ok M' -> fill_exp Θ Ξ B Γ M M'.
  Definition read_fill_sound (H : surface_modexp) : Prop :=
    forall Γ r, fill_read_fn Γ H = fill_ok r -> fill_read Θ Ξ B Γ H r.
  Definition unit_fill_sound (U : surface_unit) : Prop :=
    forall Γ U', fill_unit_fn Γ U = fill_ok U' -> fill_unit Θ Ξ B Γ U U'.
  Definition def_fill_sound (D : surface_moddef) : Prop :=
    forall Γ D', fill_def_fn Γ D = fill_ok D' -> fill_def Θ Ξ B Γ D D'.
  Definition body_fill_sound (Φ : surface_body) : Prop :=
    forall Γ Φ', fill_body_fn Γ Φ = fill_ok Φ' -> fill_body Θ Ξ B Γ Φ Φ'.
  Definition binding_fill_sound (b : surface_binding) : Prop :=
    match b with
    | surface_b_def A M => exp_fill_sound A /\ exp_fill_sound M
    | surface_b_mod U => unit_fill_sound U
    | surface_b_ind_alias E | surface_b_record_alias E => read_fill_sound E
    end.
  Definition entry_fill_sound (E : surface_entry) : Prop :=
    match E with
    | surface_ge_def _ _ A oM => exp_fill_sound A /\ (forall M, oM = Some M -> exp_fill_sound M)
    | surface_ge_mod _ U => unit_fill_sound U
    end.

  Ltac bind_inv :=
    repeat match goal with
      | E : fill_result_bind _ _ = fill_ok _ |- _ => apply fill_result_bind_ok in E as (? & ? & E)
      | E : fill_ok _ = fill_ok _ |- _ => injection E as E; subst
      end.

  (** A module position, as [fill_mod]. *)
  Lemma fill_mod_of_read_sound : forall Γ y H H' op, read_fill_sound H ->
      fill_mod_of Γ y (fill_read_fn Γ H) = fill_ok (H', op) -> fill_mod Θ Ξ B Γ H H' op.
  Proof.
    intros * IH E.
    destruct (fill_read_fn Γ H) as [r | e] eqn:Er; [| discriminate ].
    pose proof (IH _ _ Er) as Hr; apply fill_mod_of_sound in E.
    destruct r as [H0 | M]; [ destruct E as [-> ->]; constructor; exact Hr |].
    destruct E as (HΓ & p & Rs & HW & -> & ->); econstructor; eassumption.
  Qed.

  Lemma optional_exp_fill_sound : forall Γ oM oM', (forall M, oM = Some M -> exp_fill_sound M) ->
      fill_optional_exp_fn Γ oM = fill_ok oM' -> fill_optional_exp Θ Ξ B Γ oM oM'.
  Proof.
    intros Γ [M |] oM' IH E; cbn in E; bind_inv; constructor; [ exact (IH _ eq_refl _ _ H) ].
  Qed.

  Lemma tele_fill_sound : forall Γ Δ Δ', Forall exp_fill_sound Δ -> fill_tele_fn Γ Δ = fill_ok Δ' ->
      fill_tele Θ Ξ B Γ Δ Δ'.
  Proof.
    intros Γ; induction Δ as [| A Δ IH]; intros Δ' HΔ E; cbn in E; bind_inv; [ constructor |].
    inversion HΔ as [| ? ? HA HΔ0]; subst.
    destruct (kind_at_sound _ _ _ _ H1) as (W & -> & HG & HW).
    econstructor; [ exact (IH _ HΔ0 H) | exact (HA _ _ H0) | exact HG | exact HW ].
  Qed.

  Lemma field_vals_fill_sound : forall Γ fs fs', Forall (fun f => exp_fill_sound (snd f)) fs ->
      field_vals_fn Γ fs = fill_ok fs' -> fill_field_vals Θ Ξ B Γ fs fs'.
  Proof.
    intros Γ; induction fs as [| [f N] fs IH]; intros fs' Hf E; cbn in E; bind_inv; constructor;
      inversion Hf; subst; auto.
  Qed.

  Lemma brs_fill_sound : forall Γ r p D Mj As Us Bs Bs', Forall (fun br => exp_fill_sound (snd br)) Bs ->
      brs_fn Γ r p D Mj As Us Bs = fill_ok Bs' -> fill_brs Θ Ξ B r Γ p D Mj Us As Bs Bs'.
  Proof.
    intros Γ r p D Mj As Us; induction Bs as [| [[c n] B0] Bs IH]; intros Bs' HB E; cbn in E; bind_inv; [ constructor |].
    inversion HB; subst.
    destruct (ind_con Mj c) as [gs |] eqn:Ec; [| discriminate ].
    destruct (Nat.eqb_spec n (im_nn Mj + List.length gs + cargs_nrec D gs)); [| discriminate ].
    bind_inv; econstructor; eauto.
  Qed.

  Lemma scrutinee_type_fill_sound : forall Γ p D j Mj Us Z Z', exp_fill_sound Z ->
      scrutinee_type_fn Γ p D j Mj Us Z = fill_ok Z' -> fill_scrutinee_type Θ Ξ B Γ p D j Mj Us Z Z'.
  Proof.
    intros * HZ E; unfold scrutinee_type_fn in E.
    destruct (is_surface_hole Z) eqn:Eh.
    - apply is_surface_hole_spec in Eh as ->; injection E as <-; apply fill_scrutinee_type_omitted.
    - apply is_surface_hole_false in Eh; apply fill_scrutinee_type_written; [ exact Eh | exact (HZ _ _ E) ].
  Qed.

  (** The blocks of an eliminator: the motives they end with are the
      ones the branches were read at. *)
  Lemma blocks_fill_sound : forall Γ r p D Us As j Bks hs Bks',
      Forall (surface_block_all exp_fill_sound) Bks ->
      heads_fn Γ p D Us j Bks = fill_ok hs -> blocks_fn Γ r p D As Us j Bks hs = fill_ok Bks' ->
      fill_blocks Θ Ξ B r Γ p D Us As j Bks Bks' /\ blocks_motives Bks' = List.map snd hs.
  Proof.
    intros Γ r p D Us As j Bks; revert j; induction Bks as [| [nm Z A Bs] Bks IH]; intros j hs Bks' HB Eh Eb;
      cbn in Eh; bind_inv; [ cbn in Eb; bind_inv; split; [ constructor | reflexivity ] |].
    inversion HB as [| ? ? Hb0 HB0]; subst; cbn [surface_block_all] in Hb0; destruct Hb0 as (HZ & HA & HBs).
    destruct (ind_member D j) as [Mj |] eqn:Ej; [| discriminate ].
    destruct (Nat.eqb_spec nm (S (im_nn Mj))) as [-> |]; [| discriminate ].
    bind_inv; cbn in Eb; rewrite Ej in Eb; bind_inv.
    destruct (IH _ _ _ HB0 H1 H3) as [Hb Hm].
    split; [| cbn; f_equal; exact Hm ].
    econstructor; [ exact Ej | reflexivity | eapply scrutinee_type_fill_sound; eassumption | exact (HA _ _ H0)
                  | eapply brs_fill_sound; eassumption | exact Hb ].
  Qed.

  (** An eliminator as written, its scrutinee filled. *)
  Lemma elim_fill_fn_sound : forall Γ m Bks M M',
      Forall (surface_block_all exp_fill_sound) Bks ->
      fill_exp Θ Ξ B Γ M M' -> forall E, elim_fill_fn Γ m Bks M' = fill_ok E ->
      fill_exp Θ Ξ B Γ (surface_elim m Bks M) E.
  Proof.
    intros * HB HM E Ee; unfold elim_fill_fn in Ee.
    destruct (infer_at Γ M') as [W |] eqn:Ei; [| discriminate ].
    destruct W; try discriminate.
    apply infer_at_sound in Ei as [HΓ HW].
    match type of Ee with context [elim_target_f F ?pc ?k ?Rs m ?Bns] =>
      destruct (elim_target_f F pc k Rs m Bns) as [p Us | rs |] eqn:Et; rewrite elim_target_f_ok in Et; try discriminate end.
    destruct (fc_ind F p) as [D |] eqn:El; rewrite <- fc_ind_ok in El; [| discriminate ].
    bind_inv.
    destruct (ind_member D m) as [Mm |] eqn:HMm; [| discriminate ].
    destruct (List.nth_error (List.map snd x) m) as [Am |] eqn:HAm; [| discriminate ].
    destruct (infer_at (elim_mctx p D m Mm Us ++ Γ) Am) as [Wm |] eqn:EWm; [| discriminate ].
    apply infer_at_sound in EWm as [HΓm HWm].
    bind_inv.
    destruct (blocks_fill_sound _ _ _ _ _ _ _ _ _ _ HB H H0) as [Hbk Hm].
    (** the block of the scrutinee's member, whose motive is the one read *)
    rewrite <- Hm in HAm; unfold blocks_motives in HAm; rewrite List.nth_error_map in HAm.
    destruct (List.nth_error x0 m) as [bm |] eqn:Hbm; cbn in HAm; [ injection HAm as HAm | discriminate ].
    subst Am.
    eapply fill_exp_elim; [ exact HM | exact HΓ | exact HW | exact Et | exact El | exact HMm | exact Hbm
                          | exact HΓm | exact HWm | rewrite Hm; exact Hbk ].
  Qed.

  (** A term filled part by part, by its rule: the leaf rule
      [fill_exp_leaf] matches any term, so the rule is named. *)
  Ltac fill_struct :=
    first [ eapply fill_exp_univ | eapply fill_exp_succl | eapply fill_exp_maxl | eapply fill_exp_absurd
          | eapply fill_exp_and | eapply fill_exp_left | eapply fill_exp_right | eapply fill_exp_app ]; eauto.

  Lemma fill_fn_sound_all :
    (forall M, exp_fill_sound M) /\ (forall H, read_fill_sound H) /\ (forall b, binding_fill_sound b) /\
    (forall U, unit_fill_sound U) /\ (forall D, def_fill_sound D) /\ (forall Φ, body_fill_sound Φ) /\
    (forall E, entry_fill_sound E).
  Proof.
    apply surface_mut_ind; unfold exp_fill_sound, read_fill_sound, unit_fill_sound, def_fill_sound, body_fill_sound,
      binding_fill_sound, entry_fill_sound; intros; try (split; assumption); try assumption;
      try match goal with
        | Hx : fill_exp_fn _ _ = fill_ok _ |- _ => rename Hx into E
        | Hx : fill_read_fn _ _ = fill_ok _ |- _ => rename Hx into E
        | Hx : fill_unit_fn _ _ = fill_ok _ |- _ => rename Hx into E
        | Hx : fill_def_fn _ _ = fill_ok _ |- _ => rename Hx into E
        | Hx : fill_body_fn _ _ = fill_ok _ |- _ => rename Hx into E
        end.
    - (* a term with no subterm *)
      destruct M; try contradiction; cbn [fill_exp_fn] in E; try discriminate; bind_inv;
        try (apply fill_exp_leaf; reflexivity).
      + destruct (nat_view_f F B) as [[[p z] s] |] eqn:Ev; rewrite nat_view_f_ok in Ev; [| discriminate ]; bind_inv; econstructor; exact Ev.
      + destruct (nat_view_f F B) as [[[p z] s] |] eqn:Ev; rewrite nat_view_f_ok in Ev; [| discriminate ]; bind_inv; econstructor; exact Ev.
    - cbn [fill_exp_fn] in E; bind_inv; fill_struct.
    - cbn [fill_exp_fn] in E; bind_inv; fill_struct.
    - cbn [fill_exp_fn] in E; bind_inv; fill_struct.
    - cbn [fill_exp_fn] in E; bind_inv; fill_struct.
    - cbn [fill_exp_fn] in E; bind_inv; fill_struct.
    - (* a proof of a conjunction: its second proposition written, or left
         to the type of the second component *)
      cbn [fill_exp_fn] in E; bind_inv.
      destruct (is_surface_hole Q) eqn:Eh.
      + apply is_surface_hole_spec in Eh as ->.
        destruct (infer_at Γ x1) as [W |] eqn:Ei; [| discriminate ]; bind_inv.
        apply infer_at_sound in Ei as [HG HW].
        eapply fill_exp_conj_right_inferred; eauto.
      + apply is_surface_hole_false in Eh; bind_inv; apply fill_exp_conj; eauto.
    - cbn [fill_exp_fn] in E; bind_inv; fill_struct.
    - cbn [fill_exp_fn] in E; bind_inv; fill_struct.
    - (* a [Π]: its kinds, those of the sorts its filled domain and
         codomain infer to *)
      cbn [fill_exp_fn] in E; bind_inv.
      destruct (kind_at_sound _ _ _ _ H2) as (WA & -> & HGA & HWA).
      destruct (kind_at_sound _ _ _ _ H4) as (WB & -> & HGB & HWB).
      eapply fill_exp_pi; eauto.
    - (* a [λ]: its binder at the kind of the sort its domain infers to *)
      cbn [fill_exp_fn] in E; bind_inv.
      destruct (kind_at_sound _ _ _ _ H2) as (WA & -> & HGA & HWA).
      (** the rule [fill_exp_fn] of [Core.TypedElab.Fill], not this
          file's function *)
      eapply Core.TypedElab.Fill.fill_exp_fn; eauto.
    - cbn [fill_exp_fn] in E; bind_inv; fill_struct.
    - (* a let *)
      destruct b as [A M0 | U | E0 | E0].
      + destruct H as [HA HM]; cbn [fill_exp_fn] in E; bind_inv.
        destruct (is_surface_hole A) eqn:Eh.
        * apply is_surface_hole_spec in Eh as ->.
          destruct (infer_at Γ x) as [W |] eqn:Ei; [| discriminate ]; bind_inv.
          apply infer_at_sound in Ei as [? ?].
          eapply fill_exp_let_infer; [ apply HM; eassumption | eassumption | eassumption | apply H0; assumption ].
        * apply is_surface_hole_false in Eh; bind_inv.
          apply fill_exp_let_ann; [ exact Eh | apply HA; assumption | apply HM; assumption | apply H0; assumption ].
      + cbn [fill_exp_fn] in E; bind_inv; apply fill_exp_let_mod; [ apply H; assumption | apply H0; assumption ].
      + (* a local alias of a type: its target a module, whose term is a
           type former at the type it infers *)
        cbn [fill_exp_fn] in E; bind_inv.
        destruct x as [E' op]; cbn [fst snd] in E.
        destruct op; [ discriminate |]; destruct (modexp_as_term E') as [M |] eqn:Et; [| discriminate ].
        destruct (former_at true Γ M) as [W |] eqn:Ef; [| discriminate ]; bind_inv.
        apply former_at_sound in Ef as (HΓ & HW & Hf).
        eapply fill_exp_let_ind_alias;
          [ eapply fill_mod_of_read_sound; eassumption | exact Et | exact HΓ | exact HW | exact Hf | apply H0; assumption ].
      + cbn [fill_exp_fn] in E; bind_inv.
        destruct x as [E' op]; cbn [fst snd] in E.
        destruct op; [ discriminate |]; destruct (modexp_as_term E') as [M |] eqn:Et; [| discriminate ].
        destruct (former_at false Γ M) as [W |] eqn:Ef; [| discriminate ]; bind_inv.
        apply former_at_sound in Ef as (HΓ & HW & Hf).
        eapply fill_exp_let_record_alias;
          [ eapply fill_mod_of_read_sound; eassumption | exact Et | exact HΓ | exact HW | exact Hf | apply H0; assumption ].
    - (* a member *)
      cbn [fill_exp_fn] in E; bind_inv.
      destruct (sel_check (snd x0) x) as [[qd y] |] eqn:Es; [ discriminate |]; bind_inv.
      destruct x0 as [H' op]; econstructor; [ eapply fill_mod_of_read_sound; eassumption | apply sel_check_spec; exact Es ].
    - (* a member of a term *)
      cbn [fill_exp_fn] in E; bind_inv.
      destruct (infer_at Γ x0) as [W |] eqn:Ei; [| discriminate ].
      destruct W; try discriminate.
      match type of E with context [sel_check ?o x] => destruct (sel_check o x) as [[qd y] |] eqn:Es end;
        [ discriminate |]; bind_inv.
      apply infer_at_sound in Ei as [HG HW].
      eapply fill_exp_proj_term; [ apply H; eassumption | exact HG | exact HW | apply sel_check_spec; exact Es ].
    - (* an eliminator: its scrutinee, then the reading and its blocks *)
      rewrite fill_exp_fn_elim in E; bind_inv.
      eapply elim_fill_fn_sound; [ eassumption | eauto | exact E ].
    - (* a record value *)
      rewrite fill_exp_fn_tuple in E; bind_inv.
      constructor; [ apply H; assumption | eapply field_vals_fill_sound; eassumption ].
    - cbn [fill_read_fn] in E; bind_inv; constructor.
    - (* a binder in module position *)
      cbn [fill_read_fn] in E; destruct (term_binder_b Γ k) eqn:Et; bind_inv.
      + apply term_binder_b_spec in Et; econstructor; exact Et.
      + apply fill_read_slot; intros HA.
        assert (term_binder_b Γ k = true) by (apply term_binder_b_spec; exact HA); congruence.
    - (* a member in module position *)
      cbn [fill_read_fn] in E; bind_inv.
      destruct (sel_check (snd x) y) as [[qd x0] |] eqn:Es; [ discriminate |].
      destruct x as [H' op]; cbn [fst snd] in *.
      destruct (member_term_b Γ H' y) eqn:Em; bind_inv.
      + apply member_term_b_spec in Em as (r0 & A & oM & HA).
        eapply fill_read_mem_term; [ eapply fill_mod_of_read_sound; eassumption | apply sel_check_spec; exact Es | exact HA ].
      + eapply fill_read_mem_module; [ eapply fill_mod_of_read_sound; eassumption | apply sel_check_spec; exact Es |].
        intros r0 A oM HA; assert (member_term_b Γ H' y = true) by (apply member_term_b_spec; eauto); congruence.
    - (* an application in module position *)
      cbn [fill_read_fn] in E; bind_inv.
      destruct x; bind_inv; [ apply fill_read_app_module | apply fill_read_app_term ];
        first [ apply H0; assumption | apply H1; assumption ].
    - (* a unit: its telescope, then its definition *)
      rewrite fill_unit_fn_mk in E; bind_inv.
      constructor; [ eapply tele_fill_sound; eassumption | apply H0; assumption ].
    - cbn [fill_def_fn] in E; bind_inv; constructor; apply H; assumption.
    - cbn [fill_def_fn] in E; bind_inv; destruct x as [E' op]; econstructor; eapply fill_mod_of_read_sound; eassumption.
    - cbn [fill_body_fn] in E; bind_inv; constructor.
    - (* an entry of a body, in the expansion of the body before it *)
      cbn [fill_body_fn] in E; bind_inv.
      apply body_xp_fn_spec in H2.
      destruct Ent as [b pv A oM | pv U]; bind_inv.
      + destruct H0 as [HA HoM].
        destruct (kind_at_sound _ _ _ _ H5) as (W & -> & HG & HW).
        eapply fill_body_def; [ apply H; eassumption | eassumption | apply HA; assumption | | exact HG | exact HW ].
        destruct oM as [M |]; bind_inv;
          [ apply fill_optional_exp_some; eapply HoM; [ reflexivity | eassumption ] | apply fill_optional_exp_none ].
      + eapply fill_body_mod; [ apply H; eassumption | eassumption | apply H0; assumption ].
    - (* a local open: its target, its items accessible, what it
         generates *)
      cbn [fill_body_fn] in E; bind_inv.
      apply body_xp_fn_spec in H3; destruct x2; apply sels_check_spec in H5; destruct x1 as [H' op]; cbn [fst snd] in *.
      apply items_gen_fn_spec in H6.
      eapply fill_body_open; [ apply H0; eassumption | eassumption | eapply fill_mod_of_read_sound; eassumption | exact H5 | exact H6 ].
  Qed.

  (** ** The Relation's Fill Is Computed *)

  (** The scrutinee's type and motive of each block. *)
  Definition block_heads (Bks : list eblock) : list (exp * exp) :=
    List.map (fun b => (eb_scrutinee_type b, eb_motive b)) Bks.

  (** The induction hypothesis of a module position, at the member [y]
      selected from it. *)
  Ltac use_mod_ih y :=
    match goal with Hm : forall y0, fill_mod_fn _ y0 _ = fill_ok _ |- _ => unfold fill_mod_fn in Hm; rewrite (Hm y) end.

  (** One step of computing a fill the relation has: a part filled by
      the induction hypothesis, a decision made by its specification, a
      written annotation, a binder count. *)
  Ltac complete_step :=
    first
      [ match goal with E : ?a = fill_ok _ |- context [?a] => rewrite E end
      | match goal with HG : ⊢ _ ⍮ _ ⍮ ?G, HW : @alg_type_infer _ ?G ?W ?A |- context [kind_at ?G ?A ?s] =>
          rewrite (kind_at_complete G A s W HG HW) end
      | match goal with HG : ⊢ _ ⍮ _ ⍮ ?G, HW : @alg_type_infer _ ?G ?W ?A |- context [infer_at ?G ?A] =>
          rewrite (infer_at_complete G A W HG HW) end
      | match goal with HG : ⊢ _ ⍮ _ ⍮ ?G, HW : @alg_type_infer _ ?G ?W ?A, Hf : ind_former _ _ ?G ?A ?W
          |- context [former_at true ?G ?A] => rewrite (former_at_complete true G A W HG HW Hf) end
      | match goal with HG : ⊢ _ ⍮ _ ⍮ ?G, HW : @alg_type_infer _ ?G ?W ?A, Hf : record_former _ _ ?G ?A ?W
          |- context [former_at false ?G ?A] => rewrite (former_at_complete false G A W HG HW Hf) end
      | match goal with Hs : sel_ok _ _ ?op ?y |- context [sel_check ?op ?y] => rewrite (proj2 (sel_check_spec op y) Hs) end
      | match goal with Hm : forall y0, fill_mod_fn ?G y0 ?H = fill_ok _ |- context [fill_mod_of ?G ?y (fill_read_fn ?G ?H)] =>
          unfold fill_mod_fn in Hm; rewrite (Hm y) end
      | match goal with Hm : forall y0, fill_mod_of ?G y0 (fill_read_fn ?G ?H) = fill_ok _ |- context [fill_mod_of ?G ?y (fill_read_fn ?G ?H)] =>
          rewrite (Hm y) end
      | match goal with Hb : body_xp _ _ ?G ?P ?X |- context [body_xp_fn ?G ?P] => rewrite (proj2 (body_xp_fn_spec G P X) Hb) end
      | match goal with Hf : Forall (sel_ok _ _ ?op) ?ys |- context [sels_check ?op ?ys] => rewrite (proj2 (sels_check_spec op ys) Hf) end
      | match goal with Hi : items_gen _ _ ?G ?H ?its ?gs |- context [items_gen_fn ?G ?H ?its] =>
          rewrite (proj2 (items_gen_fn_spec G H its gs) Hi) end
      | match goal with Ee : ?a = Some _ |- context [?a] => rewrite Ee end
      | match goal with Ee : ?n = ?m |- context [Nat.eqb ?n ?m] => rewrite Ee, Nat.eqb_refl end
      | match goal with Hn : ?Q <> surface_hole |- context [is_surface_hole ?Q] => rewrite (proj2 (is_surface_hole_false Q) Hn) end
      | progress cbn [fill_result_bind is_surface_hole fst snd fill_mod_of] ].

  Lemma block_heads_cons : forall b Bks, block_heads (b :: Bks) = (eb_scrutinee_type b, eb_motive b) :: block_heads Bks.
  Proof. reflexivity. Qed.

  Lemma fill_fn_complete_all :
    (forall Γ M M', fill_exp Θ Ξ B Γ M M' -> fill_exp_fn Γ M = fill_ok M') /\
    (forall Γ fs fs', fill_field_vals Θ Ξ B Γ fs fs' -> field_vals_fn Γ fs = fill_ok fs') /\
    (forall r Γ p D Us As j Bks Bks', fill_blocks Θ Ξ B r Γ p D Us As j Bks Bks' ->
       heads_fn Γ p D Us j Bks = fill_ok (block_heads Bks') /\
       blocks_fn Γ r p D As Us j Bks (block_heads Bks') = fill_ok Bks') /\
    (forall Γ p D j Mj Us Z Z', fill_scrutinee_type Θ Ξ B Γ p D j Mj Us Z Z' -> scrutinee_type_fn Γ p D j Mj Us Z = fill_ok Z') /\
    (forall r Γ p D Mj Us As Bs Bs', fill_brs Θ Ξ B r Γ p D Mj Us As Bs Bs' -> brs_fn Γ r p D Mj As Us Bs = fill_ok Bs') /\
    (forall Γ oM oM', fill_optional_exp Θ Ξ B Γ oM oM' -> fill_optional_exp_fn Γ oM = fill_ok oM') /\
    (forall Γ H r, fill_read Θ Ξ B Γ H r -> fill_read_fn Γ H = fill_ok r) /\
    (forall Γ H H' op, fill_mod Θ Ξ B Γ H H' op -> forall y, fill_mod_fn Γ y H = fill_ok (H', op)) /\
    (forall Γ U U', fill_unit Θ Ξ B Γ U U' -> fill_unit_fn Γ U = fill_ok U') /\
    (forall Γ D D', fill_def Θ Ξ B Γ D D' -> fill_def_fn Γ D = fill_ok D') /\
    (forall Γ Δ Δ', fill_tele Θ Ξ B Γ Δ Δ' -> fill_tele_fn Γ Δ = fill_ok Δ') /\
    (forall Γ Φ Φ', fill_body Θ Ξ B Γ Φ Φ' -> fill_body_fn Γ Φ = fill_ok Φ').
  Proof.
    apply fill_mut_ind; intros;
      try match goal with |- fill_exp_fn _ (surface_elim _ _ _) = _ => rewrite fill_exp_fn_elim end;
      try match goal with |- fill_exp_fn _ (surface_tuple _ _) = _ => rewrite fill_exp_fn_tuple end;
      try match goal with |- fill_unit_fn _ (surface_gu_mk _ _) = _ => rewrite fill_unit_fn_mk end;
      try match goal with |- fill_mod_fn _ _ _ = _ => unfold fill_mod_fn end;
      try match goal with |- scrutinee_type_fn _ _ _ _ _ _ _ = _ => unfold scrutinee_type_fn end;
      try match goal with Ho : fill_optional_exp_fn _ _ = _ |- _ => unfold fill_optional_exp_fn in Ho end;
      cbn [fill_exp_fn fill_read_fn fill_def_fn fill_body_fn fill_tele_fn field_vals_fn brs_fn heads_fn blocks_fn
           fill_optional_exp_fn];
      repeat complete_step; try reflexivity.
    (* a term with no subterm *)
    all: try solve [ match goal with Hl : surface_exp_leaf ?M = Some _ |- _ => destruct M; try discriminate; injection Hl as <-; reflexivity end ].
    (* a numeral, the token [ℕ] *)
    all: try solve [ rewrite nat_view_f_ok; match goal with Hv : nat_view _ _ _ = _ |- _ => rewrite Hv end; reflexivity ].
    (* a block: its heads, then its branches *)
    all: try match goal with Hb : heads_fn _ _ _ _ _ _ = _ /\ blocks_fn _ _ _ _ _ _ _ _ _ = _ |- _ /\ _ =>
           destruct Hb as [Hh Hb]; rewrite !block_heads_cons; cbn [eb_scrutinee_type eb_motive];
           split; repeat complete_step; reflexivity end.
    all: try (split; reflexivity).
    (* an eliminator: the reading, then its blocks' heads, then its tag,
       then its blocks, whose motives are those its branches are read at *)
    all: try match goal with |- elim_fill_fn _ _ _ _ = _ =>
      unfold elim_fill_fn; rewrite (infer_at_complete _ _ _ w a), elim_target_f_ok, e, <- fc_ind_ok, e0;
      destruct H0 as [Hh Hb]; rewrite Hh; cbn [fill_result_bind];
      replace (List.map snd (block_heads Bks')) with (blocks_motives Bks')
        by (clear; induction Bks' as [| [] ? IH]; cbn; [ reflexivity | f_equal; exact IH ]);
      rewrite e1;
      assert (Hm : List.nth_error (blocks_motives Bks') m = Some (eb_motive bm))
        by (unfold blocks_motives; rewrite List.nth_error_map, e2; reflexivity);
      rewrite Hm, (infer_at_complete _ _ _ w0 a0); cbn [fill_result_bind];
      rewrite Hb; reflexivity end.
    (* a binder in module position, holding no term or a term *)
    all: try solve [ match goal with Hn : ~ term_binder ?G ?k |- _ =>
           destruct (term_binder_b G k) eqn:Et; [ apply term_binder_b_spec in Et; exfalso; exact (Hn Et) | reflexivity ] end ].
    all: try solve [ match goal with Ht : term_binder ?G ?k |- _ => rewrite (proj2 (term_binder_b_spec G k) Ht); reflexivity end ].
    (* a member in module position, no term or a term *)
    all: try solve [ match goal with Hn : forall r A oM, ~ mdenote _ _ ?G (me_mem ?H ?y) _ |- _ =>
           destruct (member_term_b G H y) eqn:Em;
           [ apply member_term_b_spec in Em as (r0 & A & oM & HA); exfalso; exact (Hn _ _ _ HA) | reflexivity ] end ].
    all: try solve [ match goal with Hm : mdenote _ _ ?G (me_mem ?H ?y) (mdesc_term ?r ?A ?oM) |- _ =>
           rewrite (proj2 (member_term_b_spec G H y) (ex_intro _ r (ex_intro _ A (ex_intro _ oM Hm)))); reflexivity end ].
  Qed.

  (** ** The Parts of Commands *)

  Lemma fill_exp_fn_sound : forall Γ M M', fill_exp_fn Γ M = fill_ok M' -> fill_exp Θ Ξ B Γ M M'.
  Proof. intros; apply (proj1 fill_fn_sound_all); assumption. Qed.

  Lemma fill_optional_exp_fn_sound : forall Γ oM oM', fill_optional_exp_fn Γ oM = fill_ok oM' -> fill_optional_exp Θ Ξ B Γ oM oM'.
  Proof. intros; eapply optional_exp_fill_sound; [ intros; apply (proj1 fill_fn_sound_all) | eassumption ]. Qed.

  Lemma fill_tele_fn_sound : forall Γ Δ Δ', fill_tele_fn Γ Δ = fill_ok Δ' -> fill_tele Θ Ξ B Γ Δ Δ'.
  Proof.
    intros; eapply tele_fill_sound; [ apply Forall_forall; intros; apply fill_fn_sound_all | eassumption ].
  Qed.

  Lemma fill_mod_fn_sound : forall Γ y H H' op, fill_mod_fn Γ y H = fill_ok (H', op) -> fill_mod Θ Ξ B Γ H H' op.
  Proof. intros; eapply fill_mod_of_read_sound; [ apply fill_fn_sound_all | eassumption ]. Qed.

  Lemma fill_fields_fn_sound : forall Γ fs fs', fill_fields_fn Γ fs = fill_ok fs' -> fill_fields Θ Ξ B Γ fs fs'.
  Proof.
    intros Γ fs; revert Γ; induction fs as [| [f T] fs IH]; intros Γ fs' E; cbn in E; bind_inv; [ constructor |].
    destruct (kind_at_sound _ _ _ _ H0) as (W & -> & HG & HW).
    econstructor; [ apply fill_exp_fn_sound; eassumption | exact HG | exact HW | apply IH; assumption ].
  Qed.

  Lemma fill_fields_fn_complete : forall Γ fs fs', fill_fields Θ Ξ B Γ fs fs' -> fill_fields_fn Γ fs = fill_ok fs'.
  Proof.
    induction 1 as [| Γ f T T' W fs fs' HT HG HW _ IH]; cbn; [ reflexivity |].
    rewrite (proj1 fill_fn_complete_all _ _ _ HT); cbn; rewrite (kind_at_complete _ _ _ _ HG HW); cbn; rewrite IH; reflexivity.
  Qed.

  (** ** Mutual Definitions *)

  (** The heads of a mutual definition's functions over [Γ]: each one's
      parameters, then its scrutinee over them. *)
  Fixpoint fill_raw_fun_heads_fn (Γ : ctx) (fs : list surface_raw_fun) : fill_result (list raw_fun_head) :=
    match fs with
    | nil => fill_ok nil
    | f :: fs0 =>
        let%a ys' := fill_tele_fn Γ (surface_raw_fun_nparams f) in
        let%a Z' := fill_exp_fn (ys' ++ Γ) (surface_raw_fun_scrut f) in
        let%a fs0' := fill_raw_fun_heads_fn Γ fs0 in
        fill_ok (mk_raw_fun_head (surface_raw_fun_name f) ys' Z' :: fs0')
    end.

  (** The results of functions, each with its filled head and its
      member, in the motive's context; their clauses are left empty. *)
  Fixpoint fill_raw_fun_results_fn (Γ : ctx) (pq : qname) (D : ind_decl) (Us : list exp)
      (fhms : list (surface_raw_fun * raw_fun_head * nat)) : fill_result (list raw_fun) :=
    match fhms with
    | nil => fill_ok nil
    | (f, h, m) :: fhms0 =>
        match ind_member D m with
        | None => fill_error (fill_failure_message "internal error: a function of no member")
        | Some Mm =>
            let%a A' := fill_exp_fn (elim_mctx pq D m Mm Us ++ Γ) (surface_raw_fun_res f) in
            let%a fs0' := fill_raw_fun_results_fn Γ pq D Us fhms0 in
            fill_ok (mk_rfun (raw_fun_head_name h) (raw_fun_head_nparams h) (raw_fun_head_scrut h) A' nil :: fs0')
        end
    end.

  (** The clauses of functions, each with its head and its member, its
      result filled in [rs], in their branches' contexts at the motives
      [As]. *)
  Fixpoint fill_raw_fun_clauses_fn (Γ : ctx) (pq : qname) (D : ind_decl) (Us As : list exp)
      (fhms : list (surface_raw_fun * raw_fun_head * nat)) (rs : list raw_fun) : fill_result (list raw_fun) :=
    match fhms, rs with
    | (f, _, m) :: fhms0, rf :: rs0 =>
        match ind_member D m with
        | None => fill_error (fill_failure_message "internal error: a function of no member")
        | Some Mm =>
            let%a Bs' := brs_fn Γ ak_relevant pq D Mm As Us (surface_raw_fun_clauses f) in
            let%a fs0' := fill_raw_fun_clauses_fn Γ pq D Us As fhms0 rs0 in
            fill_ok (mk_rfun (raw_fun_name rf) (raw_fun_nparams rf) (raw_fun_scrut rf) (raw_fun_res rf) Bs' :: fs0')
        end
    | _, _ => fill_ok nil
    end.

  (** A mutual definition's functions [fs] over [Γ], the block's
      parameters [Δ'], their heads filled as [hs]: their group, then
      their results, then their clauses at the motives of the blocks of
      the functions with their results filled. *)
  Definition fill_raw_fun_bodies_fn (Γ : ctx) (Δ' : ctx) (fs : list surface_raw_fun) (hs : list raw_fun_head) :
      fill_result (list raw_fun) :=
    match hs with
    | nil => fill_error (fill_failure_message "a mutual definition with no function")
    | h0 :: hs0 =>
        match mdef_group_dec F levels_abstractable_dec Hg Δ' h0 hs0 with
        | inr e => fill_error (fill_failure_mdef_group e)
        | inl (exist _ (pq, m0, Ps, D, Us, ms) _) =>
            let l := List.combine (List.combine fs hs) ms in
            let%a rs := fill_raw_fun_results_fn Γ pq D Us l in
            fill_raw_fun_clauses_fn Γ pq D Us (blocks_motives (mdef_blocks 0 (ind_nblk D) rs ms)) l rs
        end
    end.

  (** A mutual definition's heads, filled as the relation fills them. *)
  Lemma fill_raw_fun_heads_fn_sound : forall Γ fs hs,
      fill_raw_fun_heads_fn Γ fs = fill_ok hs -> Forall2 (fill_raw_fun_head Θ Ξ B Γ) fs hs.
  Proof.
    intros Γ fs; induction fs as [| f fs IH]; intros hs E; cbn in E; bind_inv; constructor; [| apply IH; assumption ].
    constructor; cbn; [ reflexivity | apply fill_tele_fn_sound; assumption | apply fill_exp_fn_sound; assumption ].
  Qed.

  Lemma fill_raw_fun_heads_fn_complete : forall Γ fs hs,
      Forall2 (fill_raw_fun_head Θ Ξ B Γ) fs hs -> fill_raw_fun_heads_fn Γ fs = fill_ok hs.
  Proof.
    pose proof fill_fn_complete_all as (Ce & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
    induction 1 as [| f [n ys Z] fs hs [En Ep Es] _ IH]; cbn in *; [ reflexivity |].
    rewrite (Ct _ _ _ Ep); cbn; rewrite (Ce _ _ _ Es); cbn; rewrite IH; cbn; subst; reflexivity.
  Qed.

  (** A mutual definition's results, then its clauses, filled as the
      relation fills them: the results keep the heads, which, with them,
      fix the motives. *)
  Lemma fill_raw_fun_bodies_parts_sound : forall Γ pq D Us As l rs fs',
      fill_raw_fun_results_fn Γ pq D Us l = fill_ok rs ->
      fill_raw_fun_clauses_fn Γ pq D Us As l rs = fill_ok fs' ->
      Forall2 (fun fhm f' => fill_raw_fun_body Θ Ξ B pq D Us Γ As (fst (fst fhm)) (snd (fst fhm)) (snd fhm) f') l fs' /\
      Forall2 (fun f1 f2 => raw_fun_nparams f1 = raw_fun_nparams f2 /\ raw_fun_res f1 = raw_fun_res f2) fs' rs.
  Proof.
    intros Γ pq D Us As; induction l as [| [[f h] m] l IH]; intros rs fs' Er Ec.
    - cbn in Er, Ec; injection Er as <-; injection Ec as <-; split; constructor.
    - cbn in Er; destruct (ind_member D m) as [Mm |] eqn:Hj; [| discriminate ].
      apply fill_result_bind_ok in Er as (A' & EA & Er); apply fill_result_bind_ok in Er as (rs0 & Ers & Er); injection Er as <-.
      cbn in Ec; rewrite Hj in Ec.
      apply fill_result_bind_ok in Ec as (Bs' & EB & Ec); apply fill_result_bind_ok in Ec as (fs0' & Efs & Ec); injection Ec as <-.
      destruct (IH _ _ Ers Efs) as [Hb Hrs].
      split; constructor; cbn; [| exact Hb | split; reflexivity | exact Hrs ].
      constructor; cbn; [ destruct h; reflexivity | congruence | | ].
      + intros Mm' Hj'; rewrite Hj in Hj'; injection Hj' as <-; apply fill_exp_fn_sound; assumption.
      + intros Mm' Hj'; rewrite Hj in Hj'; injection Hj' as <-; eapply brs_fill_sound; [| eassumption ].
        apply Forall_forall; intros; apply fill_fn_sound_all.
  Qed.

  Lemma fill_raw_fun_bodies_parts_complete : forall Γ pq D Us As l fs',
      Forall2 (fun fhm f' => fill_raw_fun_body Θ Ξ B pq D Us Γ As (fst (fst fhm)) (snd (fst fhm)) (snd fhm) f') l fs' ->
      exists rs, fill_raw_fun_results_fn Γ pq D Us l = fill_ok rs /\
        Forall2 (fun f1 f2 => raw_fun_nparams f1 = raw_fun_nparams f2 /\ raw_fun_res f1 = raw_fun_res f2) rs fs' /\
        fill_raw_fun_clauses_fn Γ pq D Us As l rs = fill_ok fs'.
  Proof.
    pose proof fill_fn_complete_all as (Ce & _ & _ & _ & Cb & _).
    intros Γ pq D Us As l; induction l as [| [[f h] m] l IH]; intros fs' Hb;
      inversion Hb as [| ? f' ? fs'' [Eh Hm Hr Hc] Hb']; subst; try (exists nil; repeat split; constructor).
    cbn [fst snd] in *.
    destruct (ind_member D m) as [Mm |] eqn:Hj; [| contradiction ].
    destruct (IH _ Hb') as (rs & Er & Hrs & Ec).
    exists (mk_rfun (raw_fun_name f') (raw_fun_nparams f') (raw_fun_scrut f') (raw_fun_res f') nil :: rs).
    destruct f' as [n ys Z A Bs]; cbn in Eh |- *; subst h.
    rewrite Hj, (Ce _ _ _ (Hr Mm eq_refl)); cbn [fill_result_bind]; rewrite Er; cbn [fill_result_bind].
    split; [ reflexivity | split; [ constructor; [ cbn; split; reflexivity | exact Hrs ] |] ].
    rewrite (Cb _ _ _ _ _ _ _ _ _ (Hc Mm eq_refl)); cbn [fill_result_bind]; rewrite Ec; reflexivity.
  Qed.

  (** A mutual definition's bodies, filled as the relation fills them. *)
  Lemma fill_raw_fun_bodies_fn_sound : forall Γ Δ' f0 fs0 h0 hs0 fs',
      fill_raw_fun_bodies_fn Γ Δ' (f0 :: fs0) (h0 :: hs0) = fill_ok fs' ->
      exists f0' fs0' pq m0 Ps D Us ms, fs' = f0' :: fs0' /\
        mdef_group Θ Ξ Δ' h0 hs0 pq m0 Ps D Us ms /\
        Forall2 (fun fhm f' => fill_raw_fun_body Θ Ξ B pq D Us Γ
                                 (blocks_motives (mdef_blocks 0 (ind_nblk D) (f0' :: fs0') ms))
                                 (fst (fst fhm)) (snd (fst fhm)) (snd fhm) f')
          (List.combine (List.combine (f0 :: fs0) (h0 :: hs0)) ms) (f0' :: fs0').
  Proof.
    intros * E; unfold fill_raw_fun_bodies_fn in E.
    destruct (mdef_group_dec F levels_abstractable_dec Hg Δ' h0 hs0) as [[[[[[[pq m0] Ps] D] Us] ms] Hgp] | e]; [| discriminate ].
    bind_inv.
    destruct (fill_raw_fun_bodies_parts_sound _ _ _ _ _ _ _ _ H E) as [Hb Hrs].
    pose proof (mdef_group_members _ _ _ _ _ _ _ _ _ _ _ Hgp) as Hms.
    destruct ms as [| m ms]; [ inversion Hms |]; cbn in Hb.
    inversion Hb as [| ? f0' ? fs0' ? ?]; subst.
    exists f0', fs0', pq, m0, Ps, D, Us, (m :: ms); split; [ reflexivity | split; [ exact Hgp |] ].
    rewrite (mdef_blocks_motives_eq _ _ _ _ _ Hrs); exact Hb.
  Qed.

  Lemma fill_raw_fun_bodies_fn_complete : forall Δ' f0 fs0 h0 hs0 f0' fs0' pq m0 Ps D Us ms,
      mdef_group Θ Ξ Δ' h0 hs0 pq m0 Ps D Us ms ->
      Forall2 (fun fhm f' => fill_raw_fun_body Θ Ξ B pq D Us (Δ' ++ gs_tele Ξ)%list
                               (blocks_motives (mdef_blocks 0 (ind_nblk D) (f0' :: fs0') ms))
                               (fst (fst fhm)) (snd (fst fhm)) (snd fhm) f')
        (List.combine (List.combine (f0 :: fs0) (h0 :: hs0)) ms) (f0' :: fs0') ->
      fill_raw_fun_bodies_fn (Δ' ++ gs_tele Ξ)%list Δ' (f0 :: fs0) (h0 :: hs0) = fill_ok (f0' :: fs0').
  Proof.
    intros * Hgp Hb; unfold fill_raw_fun_bodies_fn.
    destruct (mdef_group_dec_complete _ levels_abstractable_dec Hg _ _ _ _ _ _ _ _ _ Hgp) as [Hp ->].
    destruct (fill_raw_fun_bodies_parts_complete _ _ _ _ _ _ _ Hb) as (rs & Er & Hrs & Ec).
    cbv zeta; rewrite Er; cbn; rewrite (mdef_blocks_motives_eq _ _ _ _ _ Hrs); exact Ec.
  Qed.

  (** ** Groups *)

  (** Constructors' arguments over [Γ], their names kept. *)
  Fixpoint fill_raw_cons_with (kind : ctx -> exp -> string -> fill_result abs_kind) (Γ : ctx)
      (cs : list (string * list (string * surface_exp))) : fill_result (list (string * list (string * abs_kind * exp))) :=
    match cs with
    | nil => fill_ok nil
    | (c, args) :: cs0 =>
        let%a args' := fill_fields_with kind Γ args in
        let%a cs0' := fill_raw_cons_with kind Γ cs0 in
        fill_ok ((c, args') :: cs0')
    end.

  #[local] Abbreviation fill_raw_cons_fn := (fill_raw_cons_with kind_at).

  (** Declared members' parameters and sorts over [Γ], the uniform
      parameters and the frames'; their constructors are left empty. *)
  Fixpoint fill_raw_heads_fn (Γ : ctx) (ms : list surface_raw_member) : fill_result (list raw_member) :=
    match ms with
    | nil => fill_ok nil
    | Mr :: ms0 =>
        let%a ys' := fill_tele_fn Γ (surface_raw_member_nparams Mr) in
        let%a S' := fill_exp_fn Γ (surface_raw_member_sort Mr) in
        let%a ms0' := fill_raw_heads_fn Γ ms0 in
        fill_ok (mk_rmem (surface_raw_member_name Mr) ys' S' nil :: ms0')
    end.

  (** The context of a member's constructors ([raw_member_args_ctx]),
      over the frames' parameters [Γt]. *)
  Definition raw_member_args_ctx_at (Γt : ctx) (R : raw_decl) (Mr : raw_member) : ctx :=
    tele_wk (raw_member_nparams Mr ++ raw_decl_uparams R) (wk_shiftn (raw_decl_nmembers R)) ++ raw_decl_selfs R ++ Γt.

  (** The fills below of a command and of what it is made of, over the
      frames' parameters [Γt]: the extracted checker computes them over
      the fast telescope of the frames ([fc_tele]), the lemmas read them
      over the Core one ([gs_tele]), which it is ([fc_tele_ok]). *)

  (** Declared members' constructors, each over the member's context in
      the group [Rh], whose parameters and sorts [hs] are filled. *)
  Fixpoint fill_raw_bodies_with (kind : ctx -> exp -> string -> fill_result abs_kind) (Γt : ctx) (Rh : raw_decl)
      (ms : list surface_raw_member) (hs : list raw_member) : fill_result (list raw_member) :=
    match ms, hs with
    | Mr :: ms0, Mh :: hs0 =>
        let%a cs' := fill_raw_cons_with kind (raw_member_args_ctx_at Γt Rh Mh) (surface_raw_member_cons Mr) in
        let%a ms0' := fill_raw_bodies_with kind Γt Rh ms0 hs0 in
        fill_ok (mk_rmem (raw_member_name Mh) (raw_member_nparams Mh) (raw_member_sort Mh) cs' :: ms0')
    | _, _ => fill_ok nil
    end.

  #[local] Abbreviation fill_raw_bodies_at := (fill_raw_bodies_with kind_at).

  (** A group as written, filled: its uniform parameters, its members'
      parameters and sorts, then their constructors' arguments in the
      group with those filled. *)
  Definition fill_raw_decl_with (kind : ctx -> exp -> string -> fill_result abs_kind) (Γt : ctx) (R : surface_raw_decl) :
      fill_result raw_decl :=
    let%a ups' := fill_tele_fn Γt (surface_raw_decl_uparams R) in
    let%a hs := fill_raw_heads_fn (ups' ++ Γt) (surface_raw_decl_members R) in
    let%a ms' := fill_raw_bodies_with kind Γt (mk_raw ups' hs (surface_raw_decl_rec_field R)) (surface_raw_decl_members R) hs in
    fill_ok (mk_raw ups' ms' (surface_raw_decl_rec_field R)).

  #[local] Abbreviation fill_raw_decl_at := (fill_raw_decl_with kind_at).

  (** *** A Group Filled for Its Error

      Where a field's type has no sort, the group is filled with a junk
      kind there ([ak_relevant]), only so that the checks of the group
      name what is wrong with it (a recursive argument at the wrong
      parameters, say); it is never run. *)

  (** The kind of a filled type's sort, or a junk one *)
  Definition kind_or_junk (Γ : ctx) (A : exp) : abs_kind :=
    match infer_at Γ A with
    | Some W => sort_abs_kind W
    | None => ak_relevant
    end.

  (** The kind of a field for the error: that of its sort, or a junk one *)
  Definition kind_diagnostic (Γ : ctx) (A : exp) (_ : string) : fill_result abs_kind := fill_ok (kind_or_junk Γ A).

  (** A group as written, as [fill_raw_decl_at], at [kind_diagnostic],
      for its error *)
  Definition fill_raw_decl_diagnostic_at (Γt : ctx) (R : surface_raw_decl) : fill_result raw_decl :=
    fill_raw_decl_with kind_diagnostic Γt R.

  Lemma fill_raw_cons_fn_sound : forall Γ cs cs', fill_raw_cons_fn Γ cs = fill_ok cs' ->
      Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_fields Θ Ξ B Γ (snd rc) (snd rc')) cs cs'.
  Proof.
    intros Γ cs; induction cs as [| [c args] cs IH]; intros cs' E; cbn in E; bind_inv; [ constructor |].
    constructor; [ split; [ reflexivity | apply fill_fields_fn_sound; assumption ] | apply IH; assumption ].
  Qed.

  Lemma fill_raw_cons_fn_complete : forall Γ cs cs',
      Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_fields Θ Ξ B Γ (snd rc) (snd rc')) cs cs' ->
      fill_raw_cons_fn Γ cs = fill_ok cs'.
  Proof.
    induction 1 as [| [c args] [c' args'] cs cs' [Ef Ha] _ IH]; cbn; [ reflexivity |].
    cbn in Ef, Ha; subst; rewrite (fill_fields_fn_complete _ _ _ Ha); cbn [fill_result_bind]; rewrite IH; reflexivity.
  Qed.

  (** The members' heads, filled. *)
  Lemma fill_raw_heads_fn_sound : forall Γ ms hs, fill_raw_heads_fn Γ ms = fill_ok hs ->
      Forall2 (fun Mr Mh => raw_member_name Mh = surface_raw_member_name Mr /\
                            fill_tele Θ Ξ B Γ (surface_raw_member_nparams Mr) (raw_member_nparams Mh) /\
                            fill_exp Θ Ξ B Γ (surface_raw_member_sort Mr) (raw_member_sort Mh)) ms hs.
  Proof.
    intros Γ ms; induction ms as [| Mr ms IH]; intros hs E; cbn in E; bind_inv; [ constructor |].
    constructor; [ cbn; repeat split; [ apply fill_tele_fn_sound | apply fill_exp_fn_sound ]; assumption
                 | apply IH; assumption ].
  Qed.

  (** The members' constructors, filled, keep the heads. *)
  Lemma fill_raw_bodies_fn_sound : forall Rh ms hs ms', List.length ms = List.length hs ->
      fill_raw_bodies_at (gs_tele Ξ) Rh ms hs = fill_ok ms' ->
      Forall2 (fun Mh Mr' => raw_member_name Mr' = raw_member_name Mh /\ raw_member_nparams Mr' = raw_member_nparams Mh /\
                             raw_member_sort Mr' = raw_member_sort Mh) hs ms' /\
      Forall2 (fun Mr Mr' => Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_fields Θ Ξ B (raw_member_args_ctx Ξ Rh Mr') (snd rc) (snd rc'))
                               (surface_raw_member_cons Mr) (raw_member_cons Mr')) ms ms'.
  Proof.
    intros Rh ms; induction ms as [| Mr ms IH]; intros [| Mh hs] ms' Hl E; cbn in Hl; try discriminate;
      cbn in E; bind_inv; [ split; constructor |].
    destruct (IH hs _ ltac:(lia) H0) as [Hh Hc].
    split; constructor; cbn; [ repeat split | exact Hh | | exact Hc ].
    change (raw_member_args_ctx_at (gs_tele Ξ)) with (raw_member_args_ctx Ξ) in H.
    replace (raw_member_args_ctx Ξ Rh (mk_rmem (raw_member_name Mh) (raw_member_nparams Mh) (raw_member_sort Mh) x))
      with (raw_member_args_ctx Ξ Rh Mh) by reflexivity.
    apply fill_raw_cons_fn_sound; assumption.
  Qed.

  (** The members of a group [R''], their heads filled as [hs] and their
      constructors over their contexts in [R''], are the relation's. *)
  Lemma fill_raw_members_zip : forall R'' ms hs ms',
      Forall2 (fun Mr Mh => raw_member_name Mh = surface_raw_member_name Mr /\
                            fill_tele Θ Ξ B (raw_decl_uparams R'' ++ gs_tele Ξ) (surface_raw_member_nparams Mr) (raw_member_nparams Mh) /\
                            fill_exp Θ Ξ B (raw_decl_uparams R'' ++ gs_tele Ξ) (surface_raw_member_sort Mr) (raw_member_sort Mh)) ms hs ->
      Forall2 (fun Mh Mr' => raw_member_name Mr' = raw_member_name Mh /\ raw_member_nparams Mr' = raw_member_nparams Mh /\
                             raw_member_sort Mr' = raw_member_sort Mh) hs ms' ->
      Forall2 (fun Mr Mr' => Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_fields Θ Ξ B (raw_member_args_ctx Ξ R'' Mr') (snd rc) (snd rc'))
                               (surface_raw_member_cons Mr) (raw_member_cons Mr')) ms ms' ->
      Forall2 (fill_raw_member Θ Ξ B R'') ms ms'.
  Proof.
    intros R'' ms hs ms' Hh; revert ms'; induction Hh as [| Mr Mh ms hs (En & Hn & Hs) _ IH]; intros ms' Hhm Hc;
      inversion Hhm as [| ? Mr' ? ms1' (En' & Ep' & Es') Hhm0]; subst; inversion Hc as [| ? ? ? ? Hc1 Hc0]; subst;
      constructor; [| exact (IH _ Hhm0 Hc0) ].
    constructor; [ congruence | rewrite Ep'; exact Hn | rewrite Es'; exact Hs | exact Hc1 ].
  Qed.

  (** The computed fill of a group is the relation's. *)
  Lemma fill_raw_decl_fn_sound : forall R R', fill_raw_decl_at (gs_tele Ξ) R = fill_ok R' -> fill_raw_decl Θ Ξ B R R'.
  Proof.
    intros R R' E; unfold fill_raw_decl_with in E; bind_inv.
    rename x into ups', x0 into hs, x1 into ms'.
    pose proof (fill_raw_heads_fn_sound _ _ _ H0) as Hh.
    destruct (fill_raw_bodies_fn_sound _ _ _ _ (Forall2_length Hh) H1) as [Hhm Hc].
    assert (Hhb : Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2) hs ms').
    { eapply Forall2_impl; [| exact Hhm ]; intros Mh Mr' (_ & Ep & Es); split; symmetry; assumption. }
    constructor; cbn; [ apply fill_tele_fn_sound; assumption | reflexivity |].
    (** the members' context in the group of the filled heads is the one
        in the filled group *)
    assert (Hctx : forall Mr', raw_member_args_ctx Ξ (mk_raw ups' hs (surface_raw_decl_rec_field R)) Mr' =
                               raw_member_args_ctx Ξ (mk_raw ups' ms' (surface_raw_decl_rec_field R)) Mr')
      by (intros Mr'; exact (raw_member_args_ctx_heads_eq Ξ (mk_raw ups' hs (surface_raw_decl_rec_field R))
                               (mk_raw ups' ms' (surface_raw_decl_rec_field R)) Mr' Mr' eq_refl Hhb eq_refl)).
    apply (fill_raw_members_zip _ _ hs); [ exact Hh | exact Hhm |].
    eapply Forall2_impl; [| exact Hc ]; intros Mr Mr' Hx; rewrite <- Hctx; exact Hx.
  Qed.

  (** The relation's fill of a group is computed. *)
  Lemma fill_raw_heads_fn_complete : forall R' ms ms', Forall2 (fill_raw_member Θ Ξ B R') ms ms' ->
      fill_raw_heads_fn (raw_decl_uparams R' ++ gs_tele Ξ) ms =
        fill_ok (List.map (fun Mr' => mk_rmem (raw_member_name Mr') (raw_member_nparams Mr') (raw_member_sort Mr') nil) ms').
  Proof.
    pose proof fill_fn_complete_all as (Ce & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
    induction 1 as [| Mr Mr' ms ms' [En Hn Hs Hc] _ IH]; [ reflexivity |]; cbn.
    rewrite (Ct _ _ _ Hn); cbn [fill_result_bind]; rewrite (Ce _ _ _ Hs); cbn [fill_result_bind]; rewrite IH; cbn.
    rewrite En; reflexivity.
  Qed.

  Lemma fill_raw_bodies_fn_complete : forall Rh R' ms ms', raw_decl_uparams Rh = raw_decl_uparams R' ->
      Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2)
        (raw_decl_members Rh) (raw_decl_members R') ->
      Forall2 (fill_raw_member Θ Ξ B R') ms ms' ->
      fill_raw_bodies_at (gs_tele Ξ) Rh ms
        (List.map (fun Mr' => mk_rmem (raw_member_name Mr') (raw_member_nparams Mr') (raw_member_sort Mr') nil) ms') = fill_ok ms'.
  Proof.
    intros * Eu HG; induction 1 as [| Mr Mr' ms ms' [En Hn Hs Hc] _ IH]; cbn [fill_raw_bodies_with List.map]; [ reflexivity |].
    change (raw_member_args_ctx_at (gs_tele Ξ)) with (raw_member_args_ctx Ξ).
    rewrite (raw_member_args_ctx_heads_eq Ξ Rh R' (mk_rmem (raw_member_name Mr') (raw_member_nparams Mr') (raw_member_sort Mr') nil)
               Mr' Eu HG eq_refl), (fill_raw_cons_fn_complete _ _ _ Hc); cbn [fill_result_bind].
    rewrite IH; cbn [fill_result_bind].
    destruct Mr'; reflexivity.
  Qed.

  Lemma fill_raw_decl_fn_complete : forall R R', fill_raw_decl Θ Ξ B R R' -> fill_raw_decl_at (gs_tele Ξ) R = fill_ok R'.
  Proof.
    pose proof fill_fn_complete_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
    intros R R' [Hu Hr Hm]; unfold fill_raw_decl_with; rewrite (Ct _ _ _ Hu); cbn [fill_result_bind].
    rewrite (fill_raw_heads_fn_complete _ _ _ Hm); cbn [fill_result_bind].
    rewrite (fill_raw_bodies_fn_complete
               (mk_raw (raw_decl_uparams R')
                  (List.map (fun Mr' => mk_rmem (raw_member_name Mr') (raw_member_nparams Mr') (raw_member_sort Mr') nil)
                     (raw_decl_members R')) (surface_raw_decl_rec_field R)) R' _ _ eq_refl); cbn [fill_result_bind].
    - destruct R'; cbn in *; subst; reflexivity.
    - cbn; clear; induction (raw_decl_members R') as [| M ms IH]; constructor; [ split; reflexivity | exact IH ].
    - exact Hm.
  Qed.

  (** ** Commands, Filled *)

  (** A command filled, part by part, over the frames' parameters [Γt],
      to the items it runs as. *)
  Definition fill_cmd_at (Γt : ctx) (c : surface_cmd) : fill_result (list cmd_item) :=
    match c with
    | surface_cmd_def x b pv A oM =>
        let%a A' := fill_exp_fn Γt A in
        let%a κ := kind_at Γt A' ("the type of " ++ x) in
        let%a oM' := fill_optional_exp_fn Γt oM in
        fill_ok (ci_core (core_cmd_def x b pv κ A' oM') :: nil)
    | surface_cmd_mod x pv Δ cs =>
        let%a Δ' := fill_tele_fn Γt Δ in
        fill_ok (ci_core (core_cmd_mod_open x pv Δ') :: List.map ci_written cs ++ ci_core (core_cmd_close x pv) :: nil)
    | surface_cmd_alias x pv Δ E =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a r := fill_mod_fn (Δ' ++ Γt) "" E in
        fill_ok (ci_core (core_cmd_alias x pv Δ' (fst r)) :: nil)
    | surface_cmd_inductive_alias x pv Δ E =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a r := fill_mod_fn (Δ' ++ Γt) "" E in
        match snd r with
        | None => fill_ok (ci_core (core_cmd_inductive_alias x pv Δ' (fst r)) :: nil)
        | Some _ => fill_error (fill_failure_message ("the inductive alias " ++ x ++ " names a record value, not an inductive type"))
        end
    | surface_cmd_record_alias x pv Δ E =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a r := fill_mod_fn (Δ' ++ Γt) "" E in
        match snd r with
        | None => fill_ok (ci_core (core_cmd_record_alias x pv Δ' (fst r)) :: nil)
        | Some _ => fill_error (fill_failure_message ("the record alias " ++ x ++ " names a record value, not a record type"))
        end
    | surface_cmd_load fp => fill_ok (ci_core (core_cmd_load fp) :: nil)
    | surface_cmd_open E its =>
        let%a r := fill_mod_fn Γt "" E in
        let%a _ := sels_check (snd r) (items_members its) in
        fill_ok (ci_core (core_cmd_open (fst r) its) :: nil)
    | surface_cmd_builtin k E =>
        let%a r := fill_mod_fn Γt "" E in
        match snd r with
        | None => fill_ok (ci_core (core_cmd_builtin k (fst r)) :: nil)
        | Some _ => fill_error (fill_failure_message "a builtin binding names a record value, not an inductive type")
        end
    | surface_cmd_eval M A =>
        let%a M' := fill_exp_fn Γt M in
        if is_surface_hole A then
          match infer_at Γt M' with
          | Some W => fill_ok (ci_core (core_cmd_eval M' (nf_to_exp W)) :: nil)
          | None => fill_error (fill_failure_message "the term of an evaluation infers no type")
          end
        else
          let%a A' := fill_exp_fn Γt A in
          fill_ok (ci_core (core_cmd_eval M' A') :: nil)
    | surface_cmd_inductive pv R =>
        let%a R' := fill_raw_decl_at Γt R in
        fill_ok (ci_core (core_cmd_inductive pv R') :: nil)
    | surface_cmd_mdef b pv Δ fs =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a hs := fill_raw_fun_heads_fn (Δ' ++ Γt) fs in
        let%a fs' := fill_raw_fun_bodies_fn (Δ' ++ Γt) Δ' fs hs in
        fill_ok (ci_core (core_cmd_mdef b pv Δ' fs') :: nil)
    | surface_cmd_record x pv Δ Srt fs cs =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a Srt' := fill_exp_fn (Δ' ++ Γt) Srt in
        let%a fs' := fill_fields_fn (Δ' ++ Γt) fs in
        fill_ok (ci_core (core_cmd_record_open x pv Δ' Srt' fs') :: List.map ci_written cs ++ ci_core (core_cmd_close x pv) :: nil)
    end.

  (** A command filled, over the fast telescope of the frames *)
  Definition fill_cmd_fn (c : surface_cmd) : fill_result (list cmd_item) := fill_cmd_at (fc_tele F) c.

  (** It is the fill over the Core telescope. *)
  Lemma fill_cmd_fn_core : forall c, fill_cmd_fn c = fill_cmd_at (gs_tele Ξ) c.
  Proof. intros; unfold fill_cmd_fn; rewrite fc_tele_ok; reflexivity. Qed.

  (** A unit's parameter telescope filled. *)
  Definition fill_params_fn (Δ : list surface_exp) : fill_result ctx := fill_tele_fn (fc_tele F) Δ.

  (** It is the fill over the Core telescope. *)
  Lemma fill_params_fn_core : forall Δ, fill_params_fn Δ = fill_tele_fn (gs_tele Ξ) Δ.
  Proof. intros; unfold fill_params_fn; rewrite fc_tele_ok; reflexivity. Qed.

  (** The computed fill of a command is the relation's. *)
  Theorem fill_cmd_fn_sound : forall c its, fill_cmd_fn c = fill_ok its -> fill_cmd Θ Ξ B c its.
  Proof.
    intros c its; rewrite fill_cmd_fn_core; destruct c; cbn [fill_cmd_at]; intros E; bind_inv; try discriminate.
    - destruct (kind_at_sound _ _ _ _ H0) as (W & -> & HG & HW).
      econstructor; [ apply fill_exp_fn_sound; eassumption | exact HG | exact HW | apply fill_optional_exp_fn_sound; assumption ].
    - constructor; apply fill_tele_fn_sound; assumption.
    - destruct x0 as [E' op]; econstructor; [ apply fill_tele_fn_sound | eapply fill_mod_fn_sound ]; eassumption.
    - constructor.
    - destruct x as [E' op]; destruct x0; apply sels_check_spec in H0.
      econstructor; [ eapply fill_mod_fn_sound; eassumption | exact H0 ].
    - (* an evaluation: its type written, or the one its term infers *)
      destruct (is_surface_hole s0) eqn:Eh.
      + apply is_surface_hole_spec in Eh as ->.
        destruct (infer_at (gs_tele Ξ) x) as [W |] eqn:Ei; [| discriminate ]; bind_inv.
        apply infer_at_sound in Ei as [HG HW].
        econstructor; [ apply fill_exp_fn_sound; eassumption | exact HG | exact HW ].
      + apply is_surface_hole_false in Eh; bind_inv.
        constructor; [ exact Eh | apply fill_exp_fn_sound; assumption | apply fill_exp_fn_sound; assumption ].
    - (* a group *)
      constructor; apply fill_raw_decl_fn_sound; assumption.
    - (* a mutual definition: its telescope, its heads, then its bodies *)
      match goal with
      | Ht : fill_tele_fn _ _ = fill_ok _, Hh : fill_raw_fun_heads_fn _ ?fs = fill_ok ?hs,
        Hb : fill_raw_fun_bodies_fn _ _ _ ?hs = fill_ok _ |- _ =>
          pose proof (fill_raw_fun_heads_fn_sound _ _ _ Hh) as Hh';
          destruct fs as [| f0 fs]; [ inversion Hh'; subst; discriminate |];
          inversion Hh' as [| ? h0 ? hs0 _ _]; subst;
          destruct (fill_raw_fun_bodies_fn_sound _ _ _ _ _ _ _ Hb)
            as (f0' & fs0' & pq & m0 & Ps & D & Us & ms & -> & Hgp & Hb');
          eapply fill_cmd_mdef; [ apply fill_tele_fn_sound; exact Ht | exact Hh' | exact Hgp | exact Hb' ]
      end.
    - destruct x as [E' [p |]]; cbn [fst snd] in *; bind_inv; try discriminate.
      constructor; eapply fill_mod_fn_sound; eassumption.
    - destruct x0 as [E' [p |]]; cbn [fst snd] in *; bind_inv; try discriminate.
      constructor; [ apply fill_tele_fn_sound | eapply fill_mod_fn_sound ]; eassumption.
    - destruct x0 as [E' [p |]]; cbn [fst snd] in *; bind_inv; try discriminate.
      constructor; [ apply fill_tele_fn_sound | eapply fill_mod_fn_sound ]; eassumption.
    - constructor; [ apply fill_tele_fn_sound | apply fill_exp_fn_sound | apply fill_fields_fn_sound ]; assumption.
  Qed.

  (** The relation's fill of a command is computed. *)
  Theorem fill_cmd_fn_complete : forall c its, fill_cmd Θ Ξ B c its -> fill_cmd_fn c = fill_ok its.
  Proof.
    pose proof fill_fn_complete_all as (Ce & _ & _ & _ & _ & Co & _ & Cm & _ & _ & Ct & _).
    intros c its H; rewrite fill_cmd_fn_core; inversion H; subst; cbn [fill_cmd_at]; try reflexivity.
    - rewrite (Ce _ _ _ H0); cbn; rewrite (kind_at_complete _ _ _ _ H1 H2); cbn; rewrite (Co _ _ _ H3); reflexivity.
    - rewrite (Ct _ _ _ H0); reflexivity.
    - rewrite (Ct _ _ _ H0); cbn; rewrite (Cm _ _ _ _ H1 ""); reflexivity.
    - rewrite (Ct _ _ _ H0); cbn; rewrite (Cm _ _ _ _ H1 ""); reflexivity.
    - rewrite (Ct _ _ _ H0); cbn; rewrite (Cm _ _ _ _ H1 ""); reflexivity.
    - rewrite (Cm _ _ _ _ H0 ""); cbn; rewrite (proj2 (sels_check_spec _ _) H1); reflexivity.
    - rewrite (Cm _ _ _ _ H0 ""); reflexivity.
    - rewrite (Ce _ _ _ H1); cbn; rewrite (proj2 (is_surface_hole_false A) H0); cbn; rewrite (Ce _ _ _ H2); reflexivity.
    - rewrite (Ce _ _ _ H0); cbn; rewrite (infer_at_complete _ _ _ H1 H2); reflexivity.
    - (* a group *)
      rewrite (fill_raw_decl_fn_complete _ _ H0); reflexivity.
    - (* a mutual definition: its telescope, its heads, then its bodies *)
      rewrite (Ct _ _ _ H0); cbn [fill_result_bind]; rewrite (fill_raw_fun_heads_fn_complete _ _ _ H1);
        cbn [fill_result_bind].
      rewrite (fill_raw_fun_bodies_fn_complete _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H3); reflexivity.
    - rewrite (Ct _ _ _ H0); cbn; rewrite (Ce _ _ _ H1); cbn; rewrite (fill_fields_fn_complete _ _ _ H2); reflexivity.
  Qed.

  (** A unit's parameters, likewise. *)
  Theorem fill_params_fn_sound : forall Δ Δ', fill_params_fn Δ = fill_ok Δ' -> fill_params Θ Ξ B Δ Δ'.
  Proof. intros * E; rewrite fill_params_fn_core in E; apply fill_tele_fn_sound; exact E. Qed.

  Theorem fill_params_fn_complete : forall Δ Δ', fill_params Θ Ξ B Δ Δ' -> fill_params_fn Δ = fill_ok Δ'.
  Proof.
    pose proof fill_fn_complete_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
    intros * H; rewrite fill_params_fn_core; exact (Ct _ _ _ H).
  Qed.
End Decide.
