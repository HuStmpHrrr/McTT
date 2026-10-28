From Stdlib Require Import List String Bool.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Import Lookup LookupTwins.
Import ListNotations.

(** * The Run's Fast State

    What the command interpreter keeps of the global context, fast
    ([Extraction.Command]): the filed units ([funits]), the paths the unit
    being run imported, and the open frames ([fstack]).  Its Core reading,
    by the decodings, appears in types and proofs only.  This file has the
    operations on the fast state the interpreter runs, each with the Core
    operation it stands for, and how the fast context of a command
    ([fctx_cmd]) is kept a translation of a canonical Core context
    ([fctx_ok]) as frames are opened, filled and closed and units are
    filed. *)

(** ** The Frames, Fast *)

(** [gs_def]'s twin: a definition closed over the frames' parameters *)
Definition fs_def (b pv : bool) (fs : fstack) (A M : exp) : gentry :=
  ge_def b pv (ctx_pi (fs_tele fs) A) (Some (ctx_fn (fs_tele fs) M)).

Lemma fs_def_dec : forall b pv fs A M, fs_def b pv fs A M = gs_def b pv (dec_stack fs) A M.
Proof. intros; unfold fs_def, gs_def; rewrite fs_tele_dec; reflexivity. Qed.

(** [gs_axiom]'s twin *)
Definition fs_axiom (b pv : bool) (fs : fstack) (A : exp) : gentry :=
  ge_def b pv (ctx_pi (fs_tele fs) A) None.

Lemma fs_axiom_dec : forall b pv fs A, fs_axiom b pv fs A = gs_axiom b pv (dec_stack fs) A.
Proof. intros; unfold fs_axiom, gs_axiom; rewrite fs_tele_dec; reflexivity. Qed.

(** [dm_entry]'s twin *)
Definition fs_dm_entry (fs : fstack) (pv : bool) (Δ : ctx) (A M : exp) (H : modexp) : gentry :=
  ge_def_mod pv (ctx_pi (fs_tele fs) (ctx_pi Δ A)) (ctx_fn (fs_tele fs) (ctx_fn Δ M)) (gu_mk (Δ ++ fs_tele fs) (md_alias H)).

Lemma fs_dm_entry_dec : forall fs pv Δ A M H, fs_dm_entry fs pv Δ A M H = dm_entry (dec_stack fs) pv Δ A M H.
Proof. intros; unfold fs_dm_entry, dm_entry; rewrite fs_tele_dec; reflexivity. Qed.

(** [ind_qname]'s twin: a name in the innermost frame *)
Definition fs_ind_qname (fs : fstack) (x : string) : qname := qname_in (fs_path fs) x.

Lemma fs_ind_qname_dec : forall fs x, fs_ind_qname fs x = ind_qname (dec_stack fs) x.
Proof. intros; unfold fs_ind_qname, ind_qname; rewrite fs_path_dec; reflexivity. Qed.

(** [record_at]'s twin *)
Definition fs_record_at (fs : fstack) (Δ : ctx) (S : typ) (fds : list (string * typ)) : record_decl :=
  mk_record_decl (Δ ++ fs_tele fs) S fds.

Lemma fs_record_at_dec : forall fs Δ S fds, fs_record_at fs Δ S fds = record_at (dec_stack fs) Δ S fds.
Proof. intros; unfold fs_record_at, record_at; rewrite fs_tele_dec; reflexivity. Qed.

(** [rms_filed]'s twin *)
Fixpoint rms_filed_f (fs : fstack) (n : nat) (Vs : list view_key) (ms : list raw_member)
    (css : list (list (string * list rcarg))) : option (list imember) :=
  match ms, css with
  | nil, nil => Some nil
  | Mr :: ms', cs :: css' =>
      match rcons_num n Vs cs, rms_filed_f fs n Vs ms' css' with
      | Some cs', Some Ms => Some (mk_imember (mh_decl (fs_ind_qname fs (raw_member_name Mr))) (raw_member_nparams Mr) cs' :: Ms)
      | _, _ => None
      end
  | _, _ => None
  end.

Lemma rms_filed_f_dec : forall fs n Vs ms css, rms_filed_f fs n Vs ms css = rms_filed (dec_stack fs) n Vs ms css.
Proof.
  intros fs n Vs; induction ms as [| Mr ms IH]; intros [| cs css]; cbn; try reflexivity.
  rewrite IH, fs_ind_qname_dec; reflexivity.
Qed.

(** ** A Fast Context Kept a Translation *)

(** The frames of a fast context are those of the Core stack they decode
    to, which is canonical. *)
Lemma fctx_ok_frames : forall v fs, fctx_ok v fs -> fs = fs_of (dec_stack fs) /\ canon_stack (dec_stack fs).
Proof.
  intros v fs [Θ Ξ _ HcΞ _ _ ->]; rewrite dec_stack_ok by exact HcΞ; split; [ reflexivity | exact HcΞ ].
Qed.

(** Whether [x] is fresh in the innermost frame, decided fast *)
Definition fs_fresh_sum (x : string) (fs : fstack) (Hr : fs = fs_of (dec_stack fs)) (Hc : canon_stack (dec_stack fs)) :
    {gs_fresh x (dec_stack fs)} + {~ gs_fresh x (dec_stack fs)}.
Proof.
  destruct (fs_fresh_dec x fs) eqn:E; [ left | right ].
  - abstract (rewrite Hr in E; exact (proj1 (fs_fresh_dec_of _ _ Hc) E)).
  - abstract (intros H; apply (fs_fresh_dec_of _ _ Hc) in H; rewrite <- Hr in H; congruence).
Defined.

(** Adding a canonical entry to the innermost frame *)
Lemma dec_stack_add : forall fs x E, fs = fs_of (dec_stack fs) -> canon_stack (gs_add x E (dec_stack fs)) ->
    dec_stack (fs_add x (tr_entry E) fs) = gs_add x E (dec_stack fs).
Proof.
  intros fs x E Hr Hc.
  assert (Ea : fs_add x (tr_entry E) fs = fs_of (gs_add x E (dec_stack fs))) by (rewrite Hr at 1; apply fs_add_of).
  rewrite Ea; apply dec_stack_ok, Hc.
Qed.

Lemma fctx_ok_add : forall v fs x E, fctx_ok v fs -> canon_stack (gs_add x E (dec_stack fs)) ->
    fctx_ok v (fs_add x (tr_entry E) fs).
Proof.
  intros v fs x E Hok Hc; destruct (fctx_ok_frames _ _ Hok) as [Hr _].
  destruct Hok as [Θ Ξ HcΘ HcΞ Hu Hv Hf].
  apply (mk_fctx_ok _ _ Θ (gs_add x E (dec_stack fs)) HcΘ Hc Hu Hv).
  rewrite Hr at 1; apply fs_add_of.
Qed.

(** An empty body is canonical. *)
Lemma canon_frame_empty : forall Δ, canon_frame (gu_body Δ gm_nil).
Proof. intros; exact I. Qed.

(** Opening a frame keeps a fast context a translation. *)
Lemma fctx_ok_cons : forall v fs f, fctx_ok v fs -> canon_frame (snd (dec_frame f)) -> f = tr_frame (dec_frame f) ->
    fctx_ok v (f :: fs).
Proof.
  intros v fs f Hok Hc Hf; destruct (fctx_ok_frames _ _ Hok) as [Hr HcΞ].
  destruct Hok as [Θ Ξ HcΘ _ Hu Hv _].
  apply (mk_fctx_ok _ _ Θ (dec_frame f :: dec_stack fs) HcΘ); [ constructor; assumption | exact Hu | exact Hv |].
  change (f :: fs = tr_frame (dec_frame f) :: fs_of (dec_stack fs)); rewrite <- Hf, <- Hr; reflexivity.
Qed.

Lemma fctx_ok_push : forall v fs mp Δ, fctx_ok v fs -> fctx_ok v (fs_push mp Δ fs).
Proof. intros; apply fctx_ok_cons; [ assumption | exact I | reflexivity ]. Qed.

Lemma fctx_ok_push_ind : forall v fs mp pq k D Δ, fctx_ok v fs -> fctx_ok v (fs_push_ind mp pq k D Δ fs).
Proof. intros; apply fctx_ok_cons; [ assumption | exact I | reflexivity ]. Qed.

Lemma fctx_ok_push_record : forall v fs mp R Δ, fctx_ok v fs -> fctx_ok v (fs_push_record mp R Δ fs).
Proof. intros; apply fctx_ok_cons; [ assumption | exact I | reflexivity ]. Qed.

(** Closing the innermost frame *)
Lemma fctx_ok_tail : forall v f fs, fctx_ok v (f :: fs) -> fctx_ok v fs.
Proof.
  intros v f fs [Θ Ξ HcΘ HcΞ Hu Hv Hf].
  destruct Ξ as [| e Ξ]; [ discriminate |]; injection Hf as _ Hf.
  inversion HcΞ; subst; exact (mk_fctx_ok _ _ Θ Ξ HcΘ ltac:(assumption) Hu Hv eq_refl).
Qed.

(** Filing a canonical unit, read in Core *)
Lemma dec_units_file : forall s fp U, units_rep s (dec_units s) -> canon_deps ((fp, U) :: dec_units s) ->
    dec_units (fus_file fp (tr_unit U) s) = (fp, U) :: dec_units s.
Proof. intros s fp U Hr Hc; exact (dec_units_ok _ _ Hc (units_rep_file _ _ _ _ Hr)). Qed.

(** ** The Units a Command Sees *)

(** A restriction reads its paths as a set. *)
Lemma gds_restrict_ext : forall L L' Θ, (forall x, In x L <-> In x L') -> gds_restrict L Θ = gds_restrict L' Θ.
Proof.
  intros L L' Θ H; unfold gds_restrict; apply filter_ext; intros [fp U]; cbn [fst].
  destruct (existsb (path_beq fp) L) eqn:E1, (existsb (path_beq fp) L') eqn:E2; try reflexivity.
  - apply existsb_path_beq in E1; apply H, existsb_path_beq in E1; congruence.
  - apply existsb_path_beq in E2; apply H, existsb_path_beq in E2; congruence.
Qed.

(** What a command sees: the units filed, restricted to the paths
    imported; nothing is built, the units seen are kept in [s]. *)
Definition cmd_view (s : funits) (D : list path) : fview := mk_fview s D.

Lemma cmd_view_deps : forall s D, view_deps (cmd_view s D) = gds_restrict D (dec_units s).
Proof. reflexivity. Qed.

(** The fast context of a command at [s], [D] and the frames [fs], the
    declaration of the natural numbers of [B] looked up already *)
Definition fctx_cmd (B : builtins) (s : funits) (D : list path) (fs : fstack) (Hok : fctx_ok (cmd_view s D) fs) : FCtx :=
  fctx_at (cmd_view s D) fs Hok (builtins_nat B).

(** It stands for the restriction and the decoded stack. *)
Lemma fc_gctx_cmd : forall B s D fs Hok,
    fc_gctx (fctx_cmd B s D fs Hok) = gc_mk (gds_restrict D (dec_units s)) (dec_stack fs).
Proof. intros; rewrite fc_gctx_eq; unfold fctx_cmd, fctx_at; cbn [fc_view fc_frames]; rewrite cmd_view_deps; reflexivity. Qed.

Lemma fc_tele_cmd : forall B s D fs Hok, fc_tele (fctx_cmd B s D fs Hok) = gs_tele (dec_stack fs).
Proof. intros; unfold fc_tele, fctx_cmd, fctx_at; cbn [fc_frames]; symmetry; apply fs_tele_dec. Qed.

Lemma fc_path_cmd : forall B s D fs Hok, fc_path (fctx_cmd B s D fs Hok) = gs_path (dec_stack fs).
Proof. intros; unfold fc_path, fctx_cmd, fctx_at; cbn [fc_frames]; symmetry; apply fs_path_dec. Qed.

(** The Core reading of the facts found at a command's fast context: its
    decodings rewritten to the restriction and the decoded stack *)
Ltac cmd_core :=
  repeat match goal with
    | |- context [fc_gctx (fctx_cmd ?B ?s ?D ?fs ?Hok)] => rewrite (fc_gctx_cmd B s D fs Hok)
    | H : context [fc_gctx (fctx_cmd ?B ?s ?D ?fs ?Hok)] |- _ => rewrite (fc_gctx_cmd B s D fs Hok) in H
    | |- context [fc_tele (fctx_cmd ?B ?s ?D ?fs ?Hok)] => rewrite (fc_tele_cmd B s D fs Hok)
    | H : context [fc_tele (fctx_cmd ?B ?s ?D ?fs ?Hok)] |- _ => rewrite (fc_tele_cmd B s D fs Hok) in H
    end;
  cbn [gc_deps gc_stack] in *.
