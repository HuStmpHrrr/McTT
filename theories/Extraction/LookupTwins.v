From Stdlib Require Import Arith List String PeanoNat Bool.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core.Syntactic Require Import Builtin.
From Mctt.Core.TypedElab Require Import ElimTarget.
From Mctt.Extraction Require Import Lookup.

(** * Fast Twins of the Core Functions That Look Names Up

    The Core functions the extracted checker runs that take the global
    context [Θ ⍮ Ξ] and look names up in it, with every lookup through the
    fast context [F] ([Extraction.Lookup]) instead.  Each twin is equal to
    the Core function at the Core context [F] stands for ([_f_ok]), which
    is how the proofs use it; Core is unchanged. *)

(** The Core context of a fast context, rebuilt from its parts: how a
    judgment found at [fc_gctx F] is read where Core states it at
    [gc_mk Θ Ξ]. *)
Lemma fc_gctx_eta : forall F, fc_gctx F = gc_mk (fc_deps F) (fc_stack F).
Proof. intros; destruct (fc_gctx F); reflexivity. Qed.

(** ** Entries *)

(** [ge_private] of the entry a fast one stands for *)
Lemma fe_private_dec : forall e, fe_private e = ge_private (dec_entry e).
Proof. intros []; reflexivity. Qed.

(** [entry_alias]'s twin: the module an alias entry names *)
Definition fe_alias (e : fentry) : option modexp :=
  match e with
  | fe_mod _ (fu_core (gu_mk _ (md_alias E'))) => Some E'
  | fe_def_mod _ _ _ (fu_core (gu_mk _ (md_alias E'))) => Some E'
  | _ => None
  end.

Lemma fe_alias_dec : forall e, fe_alias e = entry_alias (dec_entry e).
Proof. intros [| pv [Δ [t] | [Δ [sm Φ | E]]] | | pv A M [Δ [t] | [Δ [sm Φ | E]]] |]; reflexivity. Qed.

(** Whether an entry has a body: [entry_is_body], decided, on fast
    entries *)
Definition fe_is_body_b (e : fentry) : bool :=
  match e with
  | fe_mod _ (fu_mk _ _) | fe_mod _ (fu_core (gu_mk _ (md_body _ _))) | fe_ind _ _ _ _ _ | fe_record _ _ _ _ => true
  | _ => false
  end.

Lemma fe_is_body_b_spec : forall e, fe_is_body_b e = true <-> entry_is_body (dec_entry e).
Proof.
  intros [| pv [Δ [t] | [Δ [sm Φ | E]]] | | pv A M [Δ [t] | [Δ [sm Φ | E]]] |]; cbn;
    split; intros; first [ exact I | reflexivity | discriminate | contradiction ].
Qed.

(** ** Walks of Fast Bodies

    For the checker's messages only: every group filed in a body, its
    submodules' included, and their paths, in the order of the trie
    rather than in filing order (the messages read them as sets). *)

(** The groups of a Core body, where a fast unit keeps Core's *)
Fixpoint gmod_inds_core (Φ : gmod) : list ind_decl :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ _ E =>
      match E with
      | ge_ind _ _ _ D Φi => D :: gmod_inds_core Φi
      | ge_mod _ (gu_mk _ (md_body _ Φi)) => gmod_inds_core Φi
      | _ => nil
      end ++ gmod_inds_core Φ
  | gm_open Φ _ _ => gmod_inds_core Φ
  end.

(** The paths of the groups of a Core body *)
Fixpoint gmod_groups_core (Φ : gmod) : list qname :=
  match Φ with
  | gm_nil => nil
  | gm_ext Φ _ E =>
      match E with
      | ge_ind _ p _ _ Φi => p :: gmod_groups_core Φi
      | ge_mod _ (gu_mk _ (md_body _ Φi)) => gmod_groups_core Φi
      | _ => nil
      end ++ gmod_groups_core Φ
  | gm_open Φ _ _ => gmod_groups_core Φ
  end.

(** The groups filed in a fast body *)
Fixpoint ft_inds (t : ftrie) : list ind_decl :=
  match t with
  | ft_mk m _ =>
      (fix tree_inds (m : SRaw.tree fentry) : list ind_decl :=
         match m with
         | SRaw.Leaf _ => nil
         | SRaw.Node l _ e r _ => tree_inds l ++ fe_inds e ++ tree_inds r
         end) m
  end
(** The groups an entry files *)
with fe_inds (e : fentry) : list ind_decl :=
  match e with
  | fe_ind _ _ _ D t => D :: ft_inds t
  | fe_mod _ u => fu_inds u
  | _ => nil
  end
(** The groups a unit's body files *)
with fu_inds (u : funit) : list ind_decl :=
  match u with
  | fu_mk _ (fmd_body t) => ft_inds t
  | fu_core (gu_mk _ (md_body _ Φ)) => gmod_inds_core Φ
  | fu_core _ => nil
  end.

(** The paths of the groups filed in a fast body *)
Fixpoint ft_groups (t : ftrie) : list qname :=
  match t with
  | ft_mk m _ =>
      (fix tree_groups (m : SRaw.tree fentry) : list qname :=
         match m with
         | SRaw.Leaf _ => nil
         | SRaw.Node l _ e r _ => tree_groups l ++ fe_groups e ++ tree_groups r
         end) m
  end
(** The paths of the groups an entry files *)
with fe_groups (e : fentry) : list qname :=
  match e with
  | fe_ind _ p _ _ t => p :: ft_groups t
  | fe_mod _ u => fu_groups u
  | _ => nil
  end
(** The paths of the groups a unit's body files *)
with fu_groups (u : funit) : list qname :=
  match u with
  | fu_mk _ (fmd_body t) => ft_groups t
  | fu_core (gu_mk _ (md_body _ Φ)) => gmod_groups_core Φ
  | fu_core _ => nil
  end.

(** The units a view sees, newest first *)
Definition fv_units_seen (v : fview) : list funit :=
  flat_map (fun fp => match fv_find v fp with Some u => u :: nil | None => nil end) (fus_order (fv_units v)).

(** The groups of the units a fast context sees and of its frames *)
Definition fc_all_inds (F : FCtx) : list ind_decl :=
  flat_map fu_inds (fv_units_seen (fc_view F)) ++ flat_map (fun f => ft_inds (ff_body f)) (fc_frames F).

(** Their paths *)
Definition fc_all_groups (F : FCtx) : list qname :=
  flat_map fu_groups (fv_units_seen (fc_view F)) ++ flat_map (fun f => ft_groups (ff_body f)) (fc_frames F).

(** Two tests that agree everywhere agree on a list. *)
Lemma forallb_pointwise : forall {X} (f g : X -> bool) l, (forall x, f x = g x) -> forallb f l = forallb g l.
Proof. intros X f g l H; induction l as [| x l IH]; cbn; [ reflexivity | rewrite H, IH; reflexivity ]. Qed.

Section Twins.
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).

  (** [grp_info] *)
  Definition grp_info_f (qc : qname) (k : nat) : option nat :=
    match fc_ind F qc with
    | Some D' => if k <? ind_ndecl D' then Some (ind_nu D') else None
    | None => None
    end.

  Lemma grp_info_f_ok : forall qc k, grp_info_f qc k = grp_info Θ Ξ qc k.
  Proof. intros; unfold grp_info_f, grp_info; rewrite fc_ind_ok; reflexivity. Qed.

  (** [member_nest_targets] *)
  Definition member_nest_targets_f (D : ind_decl) (M : imember) : list nat :=
    match im_head M with
    | mh_decl _ => nil
    | mh_record _ _ _ => List.concat (List.map (fun cg => cargs_rec_mems (snd cg)) (im_cons M))
    | mh_view qc _ _ vm =>
        match fc_ind F qc with
        | Some D' =>
            List.concat
              (List.map (fun iM =>
                 match List.nth_error vm (fst iM) with
                 | Some v =>
                     match ind_member D v with
                     | Some Mv =>
                         List.concat (List.map (fun cg =>
                           match ind_con Mv (fst cg) with
                           | Some gs => cargs_nest_targets D D' (snd cg) gs
                           | None => nil
                           end) (im_cons (snd iM)))
                     | None => nil
                     end
                 | None => nil
                 end) (List.combine (List.seq 0 (List.length (ind_members D'))) (ind_members D')))
        | None => nil
        end
    end.

  Lemma member_nest_targets_f_ok : forall D M, member_nest_targets_f D M = member_nest_targets Θ Ξ D M.
  Proof.
    intros; unfold member_nest_targets_f, member_nest_targets.
    destruct (im_head M); [ reflexivity | | reflexivity ]; rewrite fc_ind_ok; reflexivity.
  Qed.

  (** [grp_rank_iter] *)
  Fixpoint grp_rank_iter_f (D : ind_decl) (m : nat) (k : nat) : nat :=
    match m with
    | 0 => 0
    | S m' =>
        match ind_member D k with
        | Some M =>
            match im_head M with
            | mh_decl _ => 0
            | mh_view _ _ _ _ | mh_record _ _ _ =>
                S (List.fold_right Nat.max 0 (List.map (grp_rank_iter_f D m') (member_nest_targets_f D M)))
            end
        | None => 0
        end
    end.

  Lemma grp_rank_iter_f_ok : forall D m k, grp_rank_iter_f D m k = grp_rank_iter Θ Ξ D m k.
  Proof.
    intros D m; induction m as [| m IH]; intros k; [ reflexivity |]; cbn [grp_rank_iter_f grp_rank_iter].
    destruct (ind_member D k) as [M |]; [| reflexivity ].
    destruct (im_head M); [ reflexivity | |];
      rewrite member_nest_targets_f_ok, (map_ext _ _ IH); reflexivity.
  Qed.

  (** [grp_rank] *)
  Definition grp_rank_f (D : ind_decl) : nat -> nat := grp_rank_iter_f D (List.length (ind_members D)).

  (** [rank_check] *)
  Definition rank_check_f (D : ind_decl) : bool :=
    let rk := grp_rank_f D in
    List.forallb (fun kM =>
      match im_head (snd kM) with
      | mh_decl _ => Nat.eqb (rk (fst kM)) 0
      | mh_view _ _ _ _ | mh_record _ _ _ =>
          List.forallb (fun j => Nat.ltb (rk j) (rk (fst kM))) (member_nest_targets_f D (snd kM))
      end) (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D)).

  Lemma rank_check_f_ok : forall D, rank_check_f D = rank_check Θ Ξ D.
  Proof.
    intros; unfold rank_check_f, rank_check, grp_rank_f, grp_rank.
    apply forallb_pointwise; intros [k M]; cbn [fst snd].
    rewrite !grp_rank_iter_f_ok; destruct (im_head M); [ reflexivity | |];
      rewrite member_nest_targets_f_ok; apply forallb_pointwise; intros j; rewrite !grp_rank_iter_f_ok; reflexivity.
  Qed.

  (** [view_maps_check] *)
  Definition view_maps_check_f (D : ind_decl) : bool :=
    List.forallb (fun Mk =>
      match im_head Mk with
      | mh_decl _ | mh_record _ _ _ => true
      | mh_view qc _ _ vm =>
          match fc_ind F qc with
          | Some D' =>
              List.forallb (fun iM =>
                match List.nth_error vm (fst iM) with
                | Some v =>
                    match ind_member D v with
                    | Some Mv =>
                        match im_head Mv with
                        | mh_decl _ | mh_record _ _ _ => true
                        | mh_view _ _ _ vmv => view_map_at_check vm (snd iM) vmv
                        end
                    | None => true
                    end
                | None => true
                end) (List.combine (List.seq 0 (List.length (ind_members D'))) (ind_members D'))
          | None => true
          end
      end) (ind_members D).

  Lemma view_maps_check_f_ok : forall D, view_maps_check_f D = view_maps_check Θ Ξ D.
  Proof.
    intros; unfold view_maps_check_f, view_maps_check.
    apply forallb_pointwise; intros Mk; destruct (im_head Mk); [ reflexivity | | reflexivity ].
    rewrite fc_ind_ok; reflexivity.
  Qed.

  (** [nat_view] *)
  Definition nat_view_f (B : builtins) : option (qname * string * string) :=
    match builtins_nat B with
    | Some p =>
        match fc_ind F p with
        | Some D =>
            match nat_shape D with
            | Some (z, s) => Some (p, z, s)
            | None => None
            end
        | None => None
        end
    | None => None
    end.

  Lemma nat_view_f_ok : forall B, nat_view_f B = nat_view Θ Ξ B.
  Proof. intros; unfold nat_view_f, nat_view; destruct (builtins_nat B); [ rewrite fc_ind_ok |]; reflexivity. Qed.

  (** [own_target] *)
  Definition own_target_f (pc : qname) (k : nat) (Rs : list nf) (m : nat) (Bks : list eblock) : option (qname * list exp) :=
    match fc_ind F pc with
    | Some D =>
        if Nat.eqb m k && Nat.ltb k (ind_ndecl D) && blocks_fit D Bks
        then Some (pc, List.firstn (ind_nu D) (List.map nf_to_exp Rs))
        else None
    | None => None
    end.

  (** [view_targets] *)
  Fixpoint view_targets_f (pc : qname) (k m : nat) (Bks : list eblock) (seen : list qname)
      (os : list (qname * nat * list exp)) : list (qname * list exp) :=
    match os with
    | nil => nil
    | (pq, d, As) :: os' =>
        if qname_eq_dec pq pc then view_targets_f pc k m Bks seen os' else
        if List.existsb (fun s => if qname_eq_dec s pq then true else false) seen
        then view_targets_f pc k m Bks seen os' else
        let rest := view_targets_f pc k m Bks (pq :: seen) os' in
        match fc_ind F pq with
        | Some D =>
            if view_of D m pc k && blocks_fit D Bks
            then match img_pats (List.repeat true d) (List.firstn (ind_nu D) As) with
                 | Some Us => (pq, Us) :: rest
                 | None => rest
                 end
            else rest
        | None => rest
        end
    end.

  (** [elim_readings] *)
  Definition elim_readings_f (pc : qname) (k : nat) (Rs : list nf) (m : nat) (Bks : list eblock) : list (qname * list exp) :=
    let own := match own_target_f pc k Rs m Bks with Some r => r :: nil | None => nil end in
    match fc_ind F pc with
    | Some Dc => own ++ view_targets_f pc k m Bks nil (List.flat_map (nf_formers 0) (List.firstn (ind_nu Dc) Rs))
    | None => own
    end.

  (** [elim_target] *)
  Definition elim_target_f (pc : qname) (k : nat) (Rs : list nf) (m : nat) (Bks : list eblock) : elim_target_result :=
    match elim_readings_f pc k Rs m Bks with
    | nil => elim_target_none
    | (p, Us) :: nil => elim_target_one p Us
    | rs => elim_target_ambiguous rs
    end.

  (** [member_name] *)
  Definition member_name_f (p : qname) (j : nat) : string :=
    match fc_ind F p with
    | Some D => match ind_mpath D j with Some pm => qname_last pm | None => EmptyString end
    | None => EmptyString
    end.

  Lemma member_name_f_ok : forall p j, member_name_f p j = member_name Θ Ξ p j.
  Proof. intros; unfold member_name_f, member_name; rewrite fc_ind_ok; reflexivity. Qed.

  (** [inst_member_names] *)
  Definition inst_member_names_f (Is : list exp) : string :=
    String.concat EmptyString
      (List.map (fun I => match app_head I with
                          | a_ind p j => ("_" ++ member_name_f p j)%string
                          | _ => EmptyString
                          end) Is).

  Lemma inst_member_names_f_ok : forall Is, inst_member_names_f Is = inst_member_names Θ Ξ Is.
  Proof.
    intros; unfold inst_member_names_f, inst_member_names; f_equal; apply map_ext; intros I.
    destruct (app_head I); try reflexivity; rewrite member_name_f_ok; reflexivity.
  Qed.

  (** [grec_member_name] *)
  Definition grec_member_name_f (Mi : imember) : string :=
    match im_head Mi with
    | mh_decl pm => qname_last pm
    | mh_view qc k Is _ => (member_name_f qc k ++ inst_member_names_f Is)%string
    | mh_record qr Is _ => (qname_last qr ++ inst_member_names_f Is)%string
    end.

  Lemma grec_member_name_f_ok : forall Mi, grec_member_name_f Mi = grec_member_name Θ Ξ Mi.
  Proof.
    intros; unfold grec_member_name_f, grec_member_name; destruct (im_head Mi);
      rewrite ?member_name_f_ok, ?inst_member_names_f_ok; reflexivity.
  Qed.

  (** [grec_names] *)
  Definition grec_names_f (D : ind_decl) : list string :=
    List.map (fun x => ("rec_" ++ x)%string) (grec_fresh_names nil (List.map grec_member_name_f (ind_bmembers D))).

  Lemma grec_names_f_ok : forall D, grec_names_f D = grec_names Θ Ξ D.
  Proof. intros; unfold grec_names_f, grec_names; rewrite (map_ext _ _ grec_member_name_f_ok); reflexivity. Qed.

  (** [grec_mod_cmd] *)
  Definition grec_mod_cmd_f (pq : qname) (D : ind_decl) (Δu : ctx) : core_cmd :=
    core_cmd_gen (core_cmd_mod "Rec" false (grec_tele pq D Δu)
      (List.map (fun jx => let '(j, Mj, x) := jx in core_cmd_gen (core_cmd_def x true false (grec_fn_ty pq D j Mj) (Some (grec_fn pq D j Mj))))
         (List.combine (List.combine (List.seq 0 (ind_nblk D)) (ind_bmembers D)) (grec_names_f D)))).

  Lemma grec_mod_cmd_f_ok : forall pq D Δu, grec_mod_cmd_f pq D Δu = grec_mod_cmd Θ Ξ pq D Δu.
  Proof. intros; unfold grec_mod_cmd_f, grec_mod_cmd; rewrite grec_names_f_ok; reflexivity. Qed.

  (** [rec_cmds] *)
  Definition rec_cmds_f (R : raw_decl) (pq : qname) (D : ind_decl) : list core_cmd :=
    if raw_decl_rec_field R then grec_mod_cmd_f pq D (raw_decl_uparams R) :: nil else nil.

  Lemma rec_cmds_f_ok : forall R pq D, rec_cmds_f R pq D = rec_cmds Θ Ξ R pq D.
  Proof. intros; unfold rec_cmds_f, rec_cmds; rewrite grec_mod_cmd_f_ok; reflexivity. Qed.

  (** [ind_grec_cmds] *)
  Definition ind_grec_cmds_f (R : raw_decl) (pq : qname) (D : ind_decl) (k : nat) : list core_cmd :=
    if Nat.eqb k 0 && negb (raw_decl_rec_field R) then grec_mod_cmd_f pq D nil :: nil else nil.

  (** [ind_mod_cmds] *)
  Definition ind_mod_cmds_f (R : raw_decl) (pq : qname) (D : ind_decl) (k : nat) (M : imember) : list core_cmd :=
    List.map (ind_con_cmd pq D k M) (im_cons M) ++ ind_rec_cmds pq D M ++ ind_grec_cmds_f R pq D k.

  Lemma ind_mod_cmds_f_ok : forall R pq D k M, ind_mod_cmds_f R pq D k M = ind_mod_cmds Θ Ξ R pq D k M.
  Proof. intros; unfold ind_mod_cmds_f, ind_mod_cmds, ind_grec_cmds_f, ind_grec_cmds; rewrite grec_mod_cmd_f_ok; reflexivity. Qed.

  Lemma elim_target_f_ok : forall pc k Rs m Bks, elim_target_f pc k Rs m Bks = elim_target Θ Ξ pc k Rs m Bks.
  Proof.
    intros pc k Rs m Bks.
    assert (Hv : forall seen os, view_targets_f pc k m Bks seen os = view_targets Θ Ξ pc k m Bks seen os).
    { intros seen os; revert seen; induction os as [| [[pq d] As] os IH]; intros seen; cbn; [ reflexivity |].
      rewrite !IH, fc_ind_ok; reflexivity. }
    unfold elim_target_f, elim_target, elim_readings_f, elim_readings, own_target_f, own_target; rewrite !fc_ind_ok.
    destruct (fc_ind F pc); [ rewrite Hv |]; reflexivity.
  Qed.
End Twins.
