From Stdlib Require Import Lia List Morphisms String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution GlobalCtx.
From Mctt.Core.Semantic Require Export Domain.
Import Domain_Notations.
Import Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

Reserved Notation "'⟦' M '⟧' Θ '⍮' Ξ '⍮' κ '⍮' ρ '↘' r" (at level 70, M at level 69, Θ at level 69, Ξ at level 69, κ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' Ξ '⍮' κ '⍮' ρ '↘' r" (at level 70, m at level 69, A at level 69, MZ at level 69, MS at level 69, Θ at level 69, Ξ at level 69, κ at level 69, ρ at level 69, r at level 69).
Reserved Notation "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" (at level 70, m at level 69, n at level 69, Θ at level 69, Ξ at level 69, r at level 69).
Reserved Notation "'⟦' σ '⟧s' Θ '⍮' Ξ '⍮' κ '⍮' ρ '↘' ρσ" (at level 70, σ at level 69, Θ at level 69, Ξ at level 69, κ at level 69, ρ at level 69, ρσ at level 69).

Generalizable All Variables.

(** * Raw Lookup in the Global Context

    Evaluation reads entries exactly as they are stored: no module substitution
    is applied to them.  [frame_at] finds the module at an address — a unit or
    an open frame, then a chain of nested modules — with its parameter
    telescope; [gm_find] an entry of it, the newest of that name. *)
Fixpoint gm_find (Φ : gmod) (x : string) : option gentry :=
  match Φ with
  | gm_nil => None
  | gm_ext Φ' y E => if String.eqb x y then Some E else gm_find Φ' x
  end.

Fixpoint gm_walk (Δ : ctx) (Φ : gmod) (cs : list string) : option (ctx * gmod) :=
  match cs with
  | nil => Some (Δ, Φ)
  | x :: cs' =>
      match gm_find Φ x with
      | Some (ge_mod Δ' Φ') => gm_walk Δ' Φ' cs'
      | _ => None
      end
  end.

Definition frame_at (Θ : gdeps) (Ξ : gstack) (a : path) : option (ctx * gmod) :=
  match p_qual a with
  | qu_rel j =>
      match List.nth_error Ξ j with
      | Some U => gm_walk (gu_params U) (gu_mod U) (p_mems a)
      | None => None
      end
  | qu_abs fp =>
      match gds_lookup Θ fp with
      | Some U => gm_walk (gu_params U) (gu_mod U) (p_mems a)
      | None => None
      end
  end.

(** The closed frames on the chain of a module: those of its nested modules,
    and, in a filed unit, the unit's own. *)
Definition addr_depth (a : path) : nat :=
  List.length (p_mems a) + match p_qual a with qu_abs _ => 1 | qu_rel _ => 0 end.

(** * Evaluation of Expressions

    Evaluation is relative to the global context [Θ ⍮ Ξ], which does not change
    during NbE, and to a module environment [κ], which says which frames are in
    scope and what their parameters are.  It applies no substitution of any
    kind to a term: a parameter is looked up in [κ]; a global is resolved
    *raw*, relative to [κ] — [p_rel m] enters frame [m] of [κ], [p_abs fp] a
    pending frame for the unit — and a nested module or a unit with
    parameters collects them as arguments before its member is evaluated, in
    the module environment extended by that frame. *)
Inductive eval_exp (Θ : gdeps) (Ξ : gstack) : menv -> exp -> env -> domain -> Prop :=
| eval_exp_typ :
  `( ⟦ Type@i ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ 𝕌@i )
| eval_exp_var :
  `( ⟦ #x ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρ x )
| eval_exp_nat :
  `( ⟦ ℕ ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ℕᵈ )
| eval_exp_zero :
  `( ⟦ zero ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ zeroᵈ )
| eval_exp_succ :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m ->
     ⟦ succ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ succᵈ m )
| eval_exp_natrec :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m ->
     ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r ->
     ⟦ rec M return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r )
| eval_exp_pi :
  `( ⟦ A ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ a ->
     ⟦ Π A B ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ Πᵈ a κ ρ B )
| eval_exp_fn :
  `( ⟦ λ A M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ λᵈ κ ρ M )
| eval_exp_app :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m ->
     ⟦ N ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ n ->
     $| m & n | Θ ⍮ Ξ ↘ r ->
     ⟦ M $ N ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r )
(** A parameter of a closed frame is its argument. *)
| eval_exp_param_closed :
  `( me_drop (lp_mod lp) κ = me_frame a args κ' ->
     ⟦ a_param lp ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ args (lp_param lp) )
(** One of the open frame [j] is a neutral, at its type evaluated where the
    frame was checked. *)
| eval_exp_param_open :
  `( me_drop (lp_mod lp) κ = me_base j ->
     List.nth_error Ξ j = Some U ->
     eval_ptele Θ Ξ (me_base (S j)) j (List.length (gu_params U)) (gu_params U) ρp ->
     ⟦ a_param lp ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρp (lp_param lp) )
| eval_exp_glob_rel :
  `( eval_ent Θ Ξ (me_drop m κ) ip r ->
     ⟦ a_glob (p_rel m ip) ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r )
| eval_exp_glob_abs :
  `( gds_lookup Θ fp = Some U ->
     eval_pend Θ Ξ (me_base 0) (p_abs fp nil) (List.length (gu_params U)) nil ip r ->
     ⟦ a_glob (p_abs fp ip) ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r )
where "'⟦' e '⟧' Θ '⍮' Ξ '⍮' κ '⍮' ρ '↘' r" := (eval_exp Θ Ξ κ e ρ r)
with eval_natrec (Θ : gdeps) (Ξ : gstack) : menv -> exp -> exp -> exp -> domain -> env -> domain -> Prop :=
| eval_natrec_zero :
  `( ⟦ MZ ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ mz ->
     ⟦rec zeroᵈ return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ mz )
| eval_natrec_succ :
  `( ⟦rec b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ r ->
     ⟦ MS ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↦ b ↦ r ↘ ms ->
     ⟦rec succᵈ b return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ms )
| eval_natrec_neut :
  `( ⟦ MZ ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ mz ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↦ ⇑ b m ↘ a ->
     ⟦rec ⇑ b m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ⇑ a recᵈ m under κ ρ return A | zero -> mz | succ -> MS end )
where "'⟦rec' m 'return' A | 'zero' -> MZ | 'succ' -> MS 'end' '⟧' Θ '⍮' Ξ '⍮' κ '⍮' ρ '↘' r" := (eval_natrec Θ Ξ κ A MZ MS m ρ r)
with eval_app (Θ : gdeps) (Ξ : gstack) : domain -> domain -> domain -> Prop :=
| eval_app_fn :
  `( ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↦ n ↘ m ->
     $| λᵈ κ ρ M & n | Θ ⍮ Ξ ↘ m )
| eval_app_neut :
  `( ⟦ B ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↦ n ↘ b ->
     $| ⇑ (Πᵈ a κ ρ B) m & n | Θ ⍮ Ξ ↘ ⇑ b (m $ᵈ ⇓ a n) )
(** A global waiting for a frame's parameters takes one more. *)
| eval_app_gfn :
  `( eval_pend Θ Ξ κ a c (n :: args) ip r ->
     $| d_gfn κ a c args ip & n | Θ ⍮ Ξ ↘ r )
where "'$|' m '&' n '|' Θ '⍮' Ξ '↘' r" := (eval_app Θ Ξ m n r)
(** A frame at [a], outside of which is [κ], with [c] parameters of which
    [args] are given: still waiting, or complete and entered. *)
with eval_pend (Θ : gdeps) (Ξ : gstack) : menv -> path -> nat -> env -> list string -> domain -> Prop :=
| eval_pend_wait :
  `( List.length args < c ->
     eval_pend Θ Ξ κ a c args ip (d_gfn κ a c args ip) )
| eval_pend_enter :
  `( List.length args = c ->
     eval_ent Θ Ξ (me_frame a args κ) ip r ->
     eval_pend Θ Ξ κ a c args ip r )
(** Resolving a member chain inside the innermost frame of [κ]. *)
with eval_ent (Θ : gdeps) (Ξ : gstack) : menv -> list string -> domain -> Prop :=
(** δ: a transparent definition is its body, where it was checked. *)
| eval_ent_delta :
  `( frame_at Θ Ξ (me_addr κ) = Some (Δ, Φ) ->
     gm_find Φ y = Some (ge_def true pv A (Some M)) ->
     ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ nil ↘ r ->
     eval_ent Θ Ξ κ (y :: nil) r )
(** An opaque definition or an axiom is a neutral, applied to the arguments of
    the closed frames it was read out of, at its type. *)
| eval_ent_neut :
  `( frame_at Θ Ξ (me_addr κ) = Some (Δ, Φ) ->
     gm_find Φ y = Some (ge_def b pv A B) ->
     b = false \/ B = None ->
     ⟦ A ⟧ Θ ⍮ Ξ ⍮ κ ⍮ nil ↘ a ->
     eval_gne Θ Ξ κ (addr_depth (me_addr κ)) (d_glob (path_in (me_addr κ) y)) m ->
     eval_ent Θ Ξ κ (y :: nil) (⇑ a m) )
(** A nested module is a frame with its own parameters. *)
| eval_ent_mod :
  `( frame_at Θ Ξ (me_addr κ) = Some (Δ, Φ) ->
     gm_find Φ x = Some (ge_mod Δ' Φ') ->
     ip <> nil ->
     eval_pend Θ Ξ κ (path_in (me_addr κ) x) (List.length Δ') nil ip r ->
     eval_ent Θ Ξ κ (x :: ip) r )
(** The parameters of the open frame [j], as neutrals at their types: the
    environment of a suffix of the telescope, of length [c] in full. *)
with eval_ptele (Θ : gdeps) (Ξ : gstack) : menv -> nat -> nat -> ctx -> env -> Prop :=
| eval_ptele_nil :
  `( eval_ptele Θ Ξ κ j c nil nil )
| eval_ptele_cons :
  `( eval_ptele Θ Ξ κ j c Γ ρ ->
     ⟦ T ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ a ->
     eval_ptele Θ Ξ κ j c (T :: Γ) (⇑ a (d_param (lp_mk j (c - S (List.length Γ)))) :: ρ) )
(** A neutral head applied to the arguments of the innermost [n] frames,
    outermost first. *)
with eval_gne (Θ : gdeps) (Ξ : gstack) : menv -> nat -> domain_ne -> domain_ne -> Prop :=
| eval_gne_zero :
  `( eval_gne Θ Ξ κ 0 h h )
| eval_gne_succ :
  `( eval_gne Θ Ξ κ n h h1 ->
     frame_at Θ Ξ a = Some (Δ, Φ) ->
     eval_fargs Θ Ξ κ Δ args h1 h2 ->
     eval_gne Θ Ξ (me_frame a args κ) (S n) h h2 )
(** The arguments of one frame, outermost first, each at its parameter type
    evaluated outside the frame. *)
with eval_fargs (Θ : gdeps) (Ξ : gstack) : menv -> ctx -> env -> domain_ne -> domain_ne -> Prop :=
| eval_fargs_nil :
  `( eval_fargs Θ Ξ κ nil nil h h )
| eval_fargs_cons :
  `( eval_fargs Θ Ξ κ Δ args h h1 ->
     ⟦ T ⟧ Θ ⍮ Ξ ⍮ κ ⍮ args ↘ t ->
     eval_fargs Θ Ξ κ (T :: Δ) (v :: args) h (h1 $ᵈ ⇓ t v) )
.

Scheme eval_exp_mut_ind := Induction for eval_exp Sort Prop
with eval_natrec_mut_ind := Induction for eval_natrec Sort Prop
with eval_app_mut_ind := Induction for eval_app Sort Prop
with eval_pend_mut_ind := Induction for eval_pend Sort Prop
with eval_ent_mut_ind := Induction for eval_ent Sort Prop
with eval_ptele_mut_ind := Induction for eval_ptele Sort Prop
with eval_gne_mut_ind := Induction for eval_gne Sort Prop
with eval_fargs_mut_ind := Induction for eval_fargs Sort Prop.
Combined Scheme eval_mut_ind from
  eval_exp_mut_ind,
  eval_natrec_mut_ind,
  eval_app_mut_ind,
  eval_pend_mut_ind,
  eval_ent_mut_ind,
  eval_ptele_mut_ind,
  eval_gne_mut_ind,
  eval_fargs_mut_ind.

#[export]
Hint Constructors eval_exp eval_natrec eval_app eval_pend eval_ent eval_ptele eval_gne eval_fargs : mctt.

(** [eval_exp_var] up to conversion: its value [ρ x] is a flexible
    application, which unification would read [ρ] and [x] off the wrong term
    of. *)
Proposition eval_exp_var_eq : forall {Θ Ξ κ} x (ρ : env) m,
    ρ x = m ->
    ⟦ #x ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m.
Proof. intros * <-; apply eval_exp_var. Qed.

(** * Evaluation of Substitutions

    Pointwise, at every variable: each value of [ρσ] is what the substitution
    computes from [ρ].  A list ends, so past its end [ρσ] reads [zeroᵈ]; a result
    therefore exists only when [σ] is, far enough out, a variable past [ρ]. *)
Definition eval_sub (Θ : gdeps) (Ξ : gstack) (κ : menv) (σ : sub) (ρ ρσ : env) : Prop :=
  forall x, ⟦ σ x ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ x.
Arguments eval_sub : simpl never.

Notation "'⟦' σ '⟧s' Θ '⍮' Ξ '⍮' κ '⍮' ρ '↘' ρσ" := (eval_sub Θ Ξ κ σ ρ ρσ) : mctt_scope.

Lemma eval_sub_id : forall {Θ Ξ κ} ρ, ⟦ Id ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρ.
Proof. intros * x; constructor. Qed.

Lemma eval_sub_shift : forall {Θ Ξ κ} ρ, ⟦ Wk ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρ↯.
Proof. intros * x; rewrite env_var_drop; constructor. Qed.

Lemma eval_sub_extend : forall {Θ Ξ κ} σ ρ ρσ M m,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ->
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m ->
    ⟦ σ,,M ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ↦ m.
Proof.
  intros * H HM [| x]; [ assumption | apply H ].
Qed.

Corollary eval_sub_single : forall {Θ Ξ κ} ρ M m,
    ⟦ M ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m ->
    ⟦ Id,,M ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρ ↦ m.
Proof.
  intros; apply eval_sub_extend; [ apply eval_sub_id | assumption ].
Qed.

Proposition eval_sub_intro : forall {Θ Ξ κ} σ (ρ ρσ : env),
    (forall x, ⟦ σ x ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ x) ->
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ.
Proof. intros * H. exact H. Qed.

Proposition eval_sub_index : forall {Θ Ξ κ} σ (ρ ρσ : env),
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ->
    forall x, ⟦ σ x ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ x.
Proof. intros * H. exact H. Qed.

(** Both arguments that [eval_sub] inspects pointwise may be replaced by
    pointwise-equal ones; the input environment may not — a closure captures
    it. *)
#[export]
Instance eval_sub_Proper : forall {Θ Ξ κ}, Proper (sb_eq ==> eq ==> env_eq ==> iff) (eval_sub Θ Ξ κ).
Proof.
  intros Θ Ξ κ σ σ' Hσ ρ ρ0 <- ρσ ρσ' Hρσ.
  split; intros H x; [ rewrite <- (Hσ x), <- (Hρσ x) | rewrite (Hσ x), (Hρσ x) ]; apply H.
Qed.

(** ** The Substitutions that Compute

    The image of a weakening under [ι] — one that moves no variable down, so
    that [⟪φ⟫ ρ] is [ρ ∘ φ] everywhere — the identity, and an extension. *)
Lemma eval_sub_of_wk : forall {Θ Ξ κ} φ ρ `{Hφ : WkMono φ},
    ⟦ ι φ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ⟪φ⟫ ρ.
Proof.
  intros Θ Ξ κ φ ρ Hφ x; cbn; rewrite (eval_wk_eq _ _ Hφ x); apply eval_exp_var.
Qed.

(** The weakening of an extension. *)
Lemma eval_sub_wk_extend : forall {Θ Ξ κ} σ M φ ρ ρσ m,
    ⟦ sb_wk σ φ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ->
    ⟦ M[φ]ʷ ⟧ Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ m ->
    ⟦ sb_wk (σ,,M) φ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ↦ m.
Proof. intros * ? ? [| x]; [ assumption | apply H ]. Qed.

(** The two evaluations of a lifted substitution: [q σ] extends [σ[↑]] by
    [#0], so its head is a value already in [ρ]. *)
Lemma eval_sub_q : forall {Θ Ξ κ} σ ρ ρσ,
    ⟦ sb_wk σ ↑ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ->
    ⟦ q σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ↦ ρ 0.
Proof.
  intros * H [| x]; [ cbn; apply eval_exp_var |].
  rewrite sb_q_succ; exact (H x).
Qed.

Lemma eval_sub_wk_q : forall {Θ Ξ κ} σ φ ρ ρσ,
    ⟦ sb_wk (sb_wk σ ↑) φ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ->
    ⟦ sb_wk (q σ) φ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ↦ ρ (φ 0).
Proof.
  intros * H [| x]; cbn [sb_wk]; [ rewrite sb_q_zero; cbn; apply eval_exp_var |].
  rewrite sb_q_succ; exact (H x).
Qed.

(** Precomposition by a weakening reindexes the environment [σ] evaluates to. *)
Lemma eval_sub_wk_pre : forall {Θ Ξ κ} φ σ ρ ρσ `{Hφ : WkMono φ},
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ->
    ⟦ (ι φ) ⨟ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ⟪φ⟫ ρσ.
Proof.
  intros Θ Ξ κ φ σ ρ ρσ Hφ H x; rewrite (eval_wk_eq _ _ Hφ x); exact (H (φ x)).
Qed.

Corollary eval_sub_shift_pre : forall {Θ Ξ κ} σ ρ ρσ,
    ⟦ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ ->
    ⟦ Wk ⨟ σ ⟧s Θ ⍮ Ξ ⍮ κ ⍮ ρ ↘ ρσ↯.
Proof. intros * H x; rewrite env_var_drop; exact (H (S x)). Qed.

#[export]
Hint Resolve eval_sub_id eval_sub_shift eval_sub_extend eval_sub_single eval_sub_wk_extend
             eval_sub_q eval_sub_wk_q eval_sub_shift_pre : mctt.
#[export]
Hint Resolve eval_sub_index : mctt.
