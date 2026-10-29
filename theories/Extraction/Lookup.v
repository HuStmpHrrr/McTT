From Stdlib Require Import List String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Members.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Export FastGlobal FastContext Decoding.

(** * What the Implementations Look Up

    The lookups of a fast context ([FCtx], [Extraction.FastContext]), each
    with the Core lookup of the context it stands for ([fc_gctx],
    [Extraction.Decoding]) it agrees with. *)

Export FcDecoding.

(** The Core filed units a fast context stands for, the units of
    [fc_gctx]: one and the same term in the statements written with either *)
Abbreviation fc_deps F := (@gc_deps (fc_gctx F)).
(** The Core stack a fast context stands for, alike *)
Abbreviation fc_stack F := (@gc_stack (fc_gctx F)).

(** The Core filed units are the decoding of the view. *)
Lemma fc_deps_view : forall F, fc_deps F = view_deps (fc_view F).
Proof. intros; rewrite fc_gctx_eq; reflexivity. Qed.

(** The Core stack is the decoding of the frames. *)
Lemma fc_stack_frames : forall F, fc_stack F = dec_stack (fc_frames F).
Proof. intros; rewrite fc_gctx_eq; reflexivity. Qed.

(** The declaration a fast context starts from, at its Core context *)
Definition fc_seed (F : FCtx) : lk_cache (fc_deps F) (fc_stack F) :=
  match fc_seed_found F with
  | Some (exist _ x E) =>
      Some (exist _ x (eq_ind_r (fun Θ => ind_lookup Θ (fc_stack F) (fst x) = Some (snd x))
                         (eq_ind_r (fun Ξ => ind_lookup (view_deps (fc_view F)) Ξ (fst x) = Some (snd x))
                            E (fc_stack_frames F))
                         (fc_deps_view F)))
  | None => None
  end.

(** The decoded units are the view of the Core units [fc_ok] names. *)
Lemma fc_deps_eq : forall F Θ, units_rep (funits_drop (fv_units (fc_view F))) Θ -> canon_deps Θ ->
    fc_deps F = gds_restrict (fv_dom (fc_view F)) Θ.
Proof.
  intros * Hu Hc; rewrite fc_deps_view; unfold view_deps; rewrite <- dec_units_drop, (dec_units_ok _ _ Hc Hu); reflexivity.
Qed.

(** The decoded stack is the Core stack [fc_ok] names. *)
Lemma fc_stack_eq : forall F Ξ, fstack_drop (fc_frames F) = fs_of Ξ -> canon_stack Ξ -> fc_stack F = Ξ.
Proof. intros * Hf Hc; rewrite fc_stack_frames, <- dec_stack_drop, Hf; apply dec_stack_ok, Hc. Qed.

(** Decoding a lookup's result forgets the values dropped. *)
Lemma option_map_dec_entry_drop : forall o, option_map dec_entry (option_map fentry_drop o) = option_map dec_entry o.
Proof. intros [e |]; cbn; [ rewrite dec_entry_drop |]; reflexivity. Qed.

Lemma option_map_dec_loc_drop : forall o, option_map dec_loc (option_map loc_drop o) = option_map dec_loc o.
Proof. intros [r |]; cbn; [ rewrite dec_loc_drop |]; reflexivity. Qed.

Lemma option_map_dec_unit_drop : forall o, option_map dec_unit (option_map funit_drop o) = option_map dec_unit o.
Proof. intros [u |]; cbn; [ rewrite dec_unit_drop |]; reflexivity. Qed.

(** ** The Lookups of a Fast Context *)

Section Lookups.
  Variable F : FCtx.

  (** The unit at a path, if the unit being run sees it *)
  Definition fc_unit_at (fp : path) : option funit := fv_find (fc_view F) fp.

  (** [gc_entry] *)
  Definition fc_entry (p : qname) : option fentry := fgc_entry fc_unit_at (fc_frames F) p.
  (** [gc_resolve] *)
  Definition fc_resolve (p : qname) : option gentry := fgc_resolve fc_unit_at (fc_frames F) p.
  (** [gc_module] *)
  Definition fc_module (p : qname) : option modres := fgc_module fc_unit_at (fc_frames F) p.
  (** [gc_body] *)
  Definition fc_body (p : qname) : option (ctx * ftrie) := fgc_body fc_unit_at (fc_frames F) p.
  (** [gc_frame] *)
  Definition fc_frame (p : qname) : option (ctx * ftrie) := fgc_frame (fc_frames F) p.
  (** [gc_loc] *)
  Definition fc_loc (p : qname) : option (ctx * ftrie) := fgc_loc fc_unit_at (fc_frames F) p.
  (** [ind_mlookup] *)
  Definition fc_mlookup (p : qname) : option indref := fgc_mlookup fc_unit_at (fc_frames F) p.
  (** [ind_lookup] *)
  Definition fc_ind (p : qname) : option ind_decl := fgc_ind fc_unit_at (fc_frames F) p.
  (** [gc_term] *)
  Definition fc_term (p : qname) : option exp := fgc_term fc_unit_at (fc_frames F) p.
  (** [record_lookup] *)
  Definition fc_record (p : qname) : option record_decl := fgc_record fc_unit_at (fc_frames F) p.
  (** [gc_unit] *)
  Definition fc_unit (H : modexp) : option (ctx * ftrie) := fgc_unit fc_unit_at (fc_frames F) H.
  (** [gs_find_ind] *)
  Definition fc_find_ind (p : qname) : option (qname * nat * ind_decl) := fs_find_ind (fc_frames F) p.
  (** [gs_find_record] *)
  Definition fc_find_record (p : qname) : option record_decl := fs_find_record (fc_frames F) p.
  (** [gs_tele] *)
  Definition fc_tele : ctx := fs_tele (fc_frames F).
  (** [gs_path] *)
  Definition fc_path : qname := fs_path (fc_frames F).

  (** The lemmas, through the Core context [fc_ok] names *)
  Section Ok.
    (** Name the Core context of [fc_ok], rewrite the decodings to it, and
        state that the units seen are the translations of its view *)
    #[local] Ltac fc_open :=
      let Θ := fresh "Θ" in let Ξ := fresh "Ξ" in let HcΘ := fresh "HcΘ" in let HcΞ := fresh "HcΞ" in
      let Hu := fresh "Hu" in let Hv := fresh "Hv" in let Hf := fresh "Hf" in
      destruct (fc_ok F) as [Θ Ξ HcΘ HcΞ Hu Hv Hf];
      unfold fc_unit_at in *;
      rewrite ?(fc_deps_eq F Θ Hu HcΘ), ?(fc_stack_eq F Ξ Hf HcΞ);
      pose proof (fun fp => fv_find_ok (fview_drop (fc_view F)) Θ fp Hu (vis_rep_drop _ _ Hv)) as Huf;
      cbn [fview_drop fv_dom] in Huf;
      pose proof (canon_restrict (fv_dom (fc_view F)) Θ HcΘ) as HcR.

    (** The fast data, its values dropped *)
    #[local] Abbreviation drop_units := (fv_find_drop (fc_view F)).

    Lemma fc_unit_at_ok : forall fp, gds_lookup (fc_deps F) fp = option_map dec_unit (fc_unit_at fp).
    Proof.
      intros; destruct (fc_ok F) as [Θ Ξ _ _ Hu Hv Hf]; rewrite fc_deps_view, <- view_deps_drop.
      unfold fc_unit_at; rewrite <- option_map_dec_unit_drop, <- fv_find_drop.
      exact (view_deps_lookup (fview_drop (fc_view F)) _ _ Hu (vis_rep_drop _ _ Hv)).
    Qed.

    Lemma fc_entry_ok : forall p, gc_entry (fc_deps F) (fc_stack F) p = option_map dec_entry (fc_entry p).
    Proof.
      intros; unfold fc_entry; fc_open.
      rewrite <- option_map_dec_entry_drop, <- (fgc_entry_drop _ _ drop_units), Hf, (fgc_entry_ok _ _ Huf HcR _ _ HcΞ).
      destruct (gc_entry _ _ p) eqn:E; cbn [option_map]; [| reflexivity ].
      rewrite dec_tr_entry by exact (canon_gc_entry _ _ HcR HcΞ _ _ E); reflexivity.
    Qed.

    Lemma fc_resolve_ok : forall p, gc_resolve (fc_deps F) (fc_stack F) p = fc_resolve p.
    Proof.
      intros; unfold fc_resolve; fc_open.
      rewrite <- (fgc_resolve_drop _ _ drop_units), Hf, (fgc_resolve_ok _ _ Huf HcR _ _ HcΞ); reflexivity.
    Qed.

    Lemma fc_module_ok : forall p, gc_module (fc_deps F) (fc_stack F) p = fc_module p.
    Proof.
      intros; unfold fc_module; fc_open.
      rewrite <- (fgc_module_drop _ _ drop_units), Hf, (fgc_module_ok _ _ Huf HcR _ _ HcΞ); reflexivity.
    Qed.

    Lemma fc_body_ok : forall p, gc_body (fc_deps F) (fc_stack F) p = option_map dec_loc (fc_body p).
    Proof.
      intros; unfold fc_body; fc_open.
      rewrite <- option_map_dec_loc_drop, <- (fgc_body_drop _ _ drop_units), Hf, (fgc_body_ok _ _ Huf HcR _ _ HcΞ).
      destruct (gc_body _ _ p) as [[T Φ] |] eqn:E; cbn [option_map]; [| reflexivity ].
      rewrite dec_tr_loc by exact (canon_gc_body _ _ HcR HcΞ _ _ _ E); reflexivity.
    Qed.

    Lemma fc_frame_ok : forall p, gc_frame (fc_stack F) p = option_map dec_loc (fc_frame p).
    Proof.
      intros; unfold fc_frame; fc_open.
      rewrite <- option_map_dec_loc_drop, <- fgc_frame_drop, Hf, (fgc_frame_ok _ _ (canon_stack_closed _ HcΞ)).
      destruct (gc_frame _ p) as [[T Φ] |] eqn:E; cbn [option_map]; [| reflexivity ].
      rewrite dec_tr_loc by exact (canon_gc_frame _ HcΞ _ _ _ E); reflexivity.
    Qed.

    Lemma fc_loc_ok : forall p, gc_loc (fc_deps F) (fc_stack F) p = option_map dec_loc (fc_loc p).
    Proof.
      intros; unfold fc_loc; fc_open.
      rewrite <- option_map_dec_loc_drop, <- (fgc_loc_drop _ _ drop_units), Hf, (fgc_loc_ok _ _ Huf HcR _ _ HcΞ).
      destruct (gc_loc _ _ p) as [[T Φ] |] eqn:E; cbn [option_map]; [| reflexivity ].
      rewrite dec_tr_loc by exact (canon_gc_loc _ _ HcR HcΞ _ _ _ E); reflexivity.
    Qed.

    Lemma fc_mlookup_ok : forall p, ind_mlookup (fc_deps F) (fc_stack F) p = fc_mlookup p.
    Proof.
      intros; unfold fc_mlookup; fc_open.
      rewrite <- (fgc_mlookup_drop _ _ drop_units), Hf, (fgc_mlookup_ok _ _ Huf HcR _ _ HcΞ); reflexivity.
    Qed.

    Lemma fc_ind_ok : forall p, ind_lookup (fc_deps F) (fc_stack F) p = fc_ind p.
    Proof.
      intros; unfold fc_ind; fc_open.
      rewrite <- (fgc_ind_drop _ _ drop_units), Hf, (fgc_ind_ok _ _ Huf HcR _ _ HcΞ); reflexivity.
    Qed.

    Lemma fc_term_ok : forall p, gc_term (fc_deps F) (fc_stack F) p = fc_term p.
    Proof.
      intros; unfold fc_term; fc_open.
      rewrite <- (fgc_term_drop _ _ drop_units), Hf, (fgc_term_ok _ _ Huf HcR _ _ HcΞ); reflexivity.
    Qed.

    Lemma fc_record_ok : forall p, record_lookup (fc_deps F) (fc_stack F) p = fc_record p.
    Proof.
      intros; unfold fc_record; fc_open.
      rewrite <- (fgc_record_drop _ _ drop_units), Hf, (fgc_record_ok _ _ Huf HcR _ _ HcΞ); reflexivity.
    Qed.

    Lemma fc_unit_ok : forall H, gc_unit (fc_deps F) (fc_stack F) H = option_map dec_loc (fc_unit H).
    Proof.
      intros; unfold fc_unit; fc_open.
      rewrite <- option_map_dec_loc_drop, <- (fgc_unit_drop _ _ drop_units), Hf, (fgc_unit_ok _ _ Huf _ _ HcΞ).
      destruct (gc_unit _ _ H) as [[T Φ] |] eqn:E; cbn [option_map]; [| reflexivity ].
      rewrite dec_tr_loc by exact (canon_gc_unit _ _ HcR HcΞ _ _ _ E); reflexivity.
    Qed.

    Lemma fc_find_ind_ok : forall p, gs_find_ind (fc_stack F) p = fc_find_ind p.
    Proof. intros; unfold fc_find_ind; fc_open; rewrite <- fs_find_ind_drop, Hf, fs_find_ind_of; reflexivity. Qed.

    Lemma fc_find_record_ok : forall p, gs_find_record (fc_stack F) p = fc_find_record p.
    Proof. intros; unfold fc_find_record; fc_open; rewrite <- fs_find_record_drop, Hf, fs_find_record_of; reflexivity. Qed.

    Lemma fc_tele_ok : gs_tele (fc_stack F) = fc_tele.
    Proof. rewrite fc_stack_frames; apply fs_tele_dec. Qed.

    Lemma fc_path_ok : gs_path (fc_stack F) = fc_path.
    Proof. rewrite fc_stack_frames; apply fs_path_dec. Qed.
  End Ok.

  (** The values an entry found stores are right. *)
  Lemma fc_entry_values : forall p e, fc_entry p = Some e -> fentry_values_ok (fc_deps F) (fc_stack F) e.
  Proof.
    intros p e He; rewrite fc_deps_view, fc_stack_frames.
    exact (fgc_entry_values _ _ _ _ _ _ (fo_unit_values _ _ (fc_ok F)) (fo_frame_values _ _ (fc_ok F)) He).
  Qed.

  (** The lookups with their equations, as the implementations call
      them *)
  Definition gc_entry_f p : { o | gc_entry (fc_deps F) (fc_stack F) p = option_map dec_entry o } :=
    exist _ (fc_entry p) (fc_entry_ok p).
  (** Alike, with the values the entry stores right *)
  Definition gc_entry_vf p :
      { o | gc_entry (fc_deps F) (fc_stack F) p = option_map dec_entry o /\
            forall e, o = Some e -> fentry_values_ok (fc_deps F) (fc_stack F) e } :=
    exist _ (fc_entry p) (conj (fc_entry_ok p) (fc_entry_values p)).
  Definition gc_resolve_f p : { o | gc_resolve (fc_deps F) (fc_stack F) p = o } :=
    exist _ (fc_resolve p) (fc_resolve_ok p).
  Definition gc_module_f p : { o | gc_module (fc_deps F) (fc_stack F) p = o } :=
    exist _ (fc_module p) (fc_module_ok p).
  Definition gc_body_f p : { o | gc_body (fc_deps F) (fc_stack F) p = option_map dec_loc o } :=
    exist _ (fc_body p) (fc_body_ok p).
  Definition gc_frame_f p : { o | gc_frame (fc_stack F) p = option_map dec_loc o } :=
    exist _ (fc_frame p) (fc_frame_ok p).
  Definition gc_loc_f p : { o | gc_loc (fc_deps F) (fc_stack F) p = option_map dec_loc o } :=
    exist _ (fc_loc p) (fc_loc_ok p).
  Definition ind_lookup_f p : { o | ind_lookup (fc_deps F) (fc_stack F) p = o } :=
    exist _ (fc_ind p) (fc_ind_ok p).
  (** The member of a group whose module is at [p] *)
  Definition ind_mlookup_f p : { o | ind_mlookup (fc_deps F) (fc_stack F) p = o } :=
    exist _ (fc_mlookup p) (fc_mlookup_ok p).
  (** The record type at [p] *)
  Definition record_lookup_f p : { o | record_lookup (fc_deps F) (fc_stack F) p = o } :=
    exist _ (fc_record p) (fc_record_ok p).
  Definition gc_term_f p : { o | gc_term (fc_deps F) (fc_stack F) p = o } :=
    exist _ (fc_term p) (fc_term_ok p).
  Definition gc_unit_f H : { o | gc_unit (fc_deps F) (fc_stack F) H = option_map dec_loc o } :=
    exist _ (fc_unit H) (fc_unit_ok H).
  Definition gs_find_ind_f p : { o | gs_find_ind (fc_stack F) p = o } :=
    exist _ (fc_find_ind p) (fc_find_ind_ok p).
  Definition gs_find_record_f p : { o | gs_find_record (fc_stack F) p = o } :=
    exist _ (fc_find_record p) (fc_find_record_ok p).

  (** A declaration looked up through the cache [ck]: a comparison of names
      when it is the cached one *)
  Definition cache_lookup (ck : lk_cache (fc_deps F) (fc_stack F)) (p : qname) : { o | ind_lookup (fc_deps F) (fc_stack F) p = o } :=
    match ck with
    | Some (exist _ (pc, D) E) =>
        match qname_dec pc p with
        | left Hq => exist _ (Some D) (eq_rect pc (fun r => ind_lookup (fc_deps F) (fc_stack F) r = Some D) E p Hq)
        | right _ => ind_lookup_f p
        end
    | None => ind_lookup_f p
    end.
End Lookups.

(** ** Building a Fast Context *)

(** A declaration looked up fast is the one of the decoding. *)
Lemma seed_ok : forall v fs (Hok : fctx_ok v fs) p D, fgc_ind (fv_find v) fs p = Some D ->
    ind_lookup (view_deps v) (dec_stack fs) p = Some D.
Proof.
  intros v fs Hok p D E; pose proof (fc_ind_ok (mk_fctx v fs Hok None) p) as H.
  rewrite fc_deps_view, fc_stack_frames in H; cbn [fc_view fc_frames] in H; rewrite H; exact E.
Qed.

(** The declaration at [op], looked up fast, as a seed *)
Definition seed_at (v : fview) (fs : fstack) (Hok : fctx_ok v fs) (op : option qname) : lk_cache (view_deps v) (dec_stack fs) :=
  match op with
  | Some p =>
      match inspect (fgc_ind (fv_find v) fs p) with
      | exist _ (Some D) E =>
          Some (exist _ (p, D) (seed_ok v fs Hok p D E))
      | exist _ None _ => None
      end
  | None => None
  end.

(** The fast context of a view and frames, seeded with the declaration at
    [op] *)
Definition fctx_at (v : fview) (fs : fstack) (Hok : fctx_ok v fs) (op : option qname) : FCtx :=
  mk_fctx v fs Hok (seed_at v fs Hok op).

(** ** The Fast Context of a Core Context

    For the reference implementations only, which are not extracted: the
    translation of [Θ ⍮ Ξ], seeing every unit of [Θ].  Its decoding is
    [Θ ⍮ Ξ] when they are canonical ([fctx_of_deps], [fctx_of_stack]),
    which well-formedness gives ([canon_of_wf]). *)

(** The translation of filed units *)
Fixpoint tr_units (Θ : gdeps) : funits :=
  match Θ with
  | nil => funits_empty
  | (fp, U) :: Θ' => fus_file fp (tr_unit U) (tr_units Θ')
  end.

Lemma tr_units_rep : forall Θ, units_rep (tr_units Θ) Θ.
Proof. induction Θ as [| [fp U] Θ IH]; [ apply units_rep_empty | apply units_rep_file, IH ]. Qed.

(** The translation of filed units, seeing all of them *)
Definition tr_units_all (Θ : gdeps) : funits := fus_see (map fst Θ) (fus_with_vis (tr_units Θ) (PM.empty _)).

Lemma tr_units_all_rep : forall Θ, units_rep (tr_units_all Θ) Θ.
Proof. intros; apply units_rep_see, units_rep_with_vis, tr_units_rep. Qed.

Lemma tr_units_all_vis : forall Θ, vis_rep (tr_units_all Θ) (map fst Θ).
Proof. intros; exact (vis_rep_see (map fst Θ) _ nil (vis_rep_nil _)). Qed.

(** The units the translation sees store no value. *)
Lemma tr_units_all_values : forall Θ Θ' Ξ fp u, pk_find fp (fus_vis (tr_units_all Θ)) = Some u -> funit_values_ok Θ' Ξ u.
Proof.
  intros * Hu; destruct (fus_see_vis _ _ _ _ Hu) as [Hf | Hf]; [| cbn in Hf; unfold pk_find in Hf; cbn in Hf; discriminate ].
  change (fus_find (tr_units Θ) fp = Some u) in Hf; rewrite (ur_find _ _ (tr_units_rep Θ)) in Hf.
  destruct (gds_lookup Θ fp); cbn in Hf; [ injection Hf as <-; apply tr_unit_values | discriminate ].
Qed.

(** The fast context of [Θ ⍮ Ξ], seeing all of [Θ] *)
Definition fctx_of (Θ : gdeps) (Ξ : gstack) (HcΘ : canon_deps Θ) (HcΞ : canon_stack Ξ) : FCtx :=
  mk_fctx (mk_fview (tr_units_all Θ) (map fst Θ)) (fs_of Ξ)
    (mk_fctx_ok (mk_fview (tr_units_all Θ) (map fst Θ)) (fs_of Ξ) Θ Ξ HcΘ HcΞ
       (units_rep_drop_of_rep _ _ (tr_units_all_rep Θ)) (tr_units_all_vis Θ) (fs_of_drop Ξ)
       (fun fp u => tr_units_all_values Θ _ _ fp u) (fs_of_values_all _ _ Ξ)) None.

(** Restricting to paths that include all filed ones changes nothing. *)
Lemma gds_restrict_all : forall L Θ, (forall x, In x (map fst Θ) -> In x L) -> gds_restrict L Θ = Θ.
Proof.
  intros L; induction Θ as [| [fp U] Θ IH]; intros H; [ reflexivity |]; unfold gds_restrict in *; cbn [filter fst].
  assert (Hin : existsb (path_beq fp) L = true) by (apply existsb_path_beq, H; left; reflexivity).
  rewrite Hin, IH; [ reflexivity |]; intros; apply H; right; assumption.
Qed.

(** The decoded filed units of the fast context of canonical [Θ] *)
Lemma fctx_of_deps : forall Θ Ξ HcΘ HcΞ, fc_deps (fctx_of Θ Ξ HcΘ HcΞ) = Θ.
Proof.
  intros; rewrite fc_deps_view; unfold fctx_of, view_deps; cbn [fv_dom fv_units fc_view].
  rewrite (dec_units_ok _ _ HcΘ (tr_units_all_rep Θ)).
  apply gds_restrict_all; intros; assumption.
Qed.

(** The decoded stack of the fast context of a canonical [Ξ] *)
Lemma fctx_of_stack : forall Θ Ξ HcΘ HcΞ, fc_stack (fctx_of Θ Ξ HcΘ HcΞ) = Ξ.
Proof. intros; rewrite fc_stack_frames; unfold fctx_of; cbn [fc_frames]; apply dec_stack_ok, HcΞ. Qed.

(** The fast context of a well-formed [Θ ⍮ Ξ] *)
Definition fctx_of_wf (Θ : gdeps) (Ξ : gstack) (H : ⊢ᵍ Θ ⍮ Ξ) : FCtx :=
  fctx_of Θ Ξ (proj1 (canon_of_wf _ _ H)) (proj2 (canon_of_wf _ _ H)).

(** Its decodings *)
Lemma fctx_of_wf_eq : forall Θ Ξ H, fc_deps (fctx_of_wf Θ Ξ H) = Θ /\ fc_stack (fctx_of_wf Θ Ξ H) = Ξ.
Proof. intros; split; [ apply fctx_of_deps | apply fctx_of_stack ]. Qed.
