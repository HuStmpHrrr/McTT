From Stdlib Require Import Bool Lia List PeanoNat String.

From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Syntax GlobalCtx Command.
From Mctt.Frontend Require Import Resolve Elaborator ElabSpec.

Import Syntax_Notations.
Open Scope list_scope.

(** * The Elaborator Meets Its Specification

    [elaborate_core] computes exactly [elab_spec] ([elaborate_core_sound],
    [elaborate_core_complete]), so the specification is functional
    ([elab_spec_functional]).

    Specification states are mapped to elaborator states by [to_mref],
    [to_os], [to_of] and [to_ls]; a frame's member table, which the
    specification reads off the emitted commands, is [emod_of].  Each layer is
    an [iff] between the elaborator succeeding on the image and the
    specification relating the preimage, by induction on the syntax. *)

(** ** Representation *)

(** The member table that the commands [cs] declare, extending [Φ]. *)
Fixpoint en_cmd (c : ccmd) : option (string * ename) :=
  match c with
  | cc_def x _ pv _ _ => Some (x, en_def pv)
  | cc_mod x Δ cs =>
      Some (x, en_mod (List.length Δ)
                 ((fix go (Φ : emod) (cs : list ccmd) : emod :=
                     match cs with
                     | nil => Φ
                     | c :: cs' => go (match en_cmd c with Some (y, e) => em_ext Φ y e | None => Φ end) cs'
                     end) em_nil cs))
  | _ => None
  end.

Definition em_step (Φ : emod) (c : ccmd) : emod :=
  match en_cmd c with Some (y, e) => em_ext Φ y e | None => Φ end.

Fixpoint emod_ext (Φ : emod) (cs : list ccmd) : emod :=
  match cs with
  | nil => Φ
  | c :: cs' => emod_ext (em_step Φ c) cs'
  end.

Definition emod_of (cs : list ccmd) : emod := emod_ext em_nil cs.

Definition en_of (c : ccmd) : option ename :=
  match c with
  | cc_def _ _ pv _ _ => Some (en_def pv)
  | cc_mod _ Δ cs => Some (en_mod (List.length Δ) (emod_of cs))
  | _ => None
  end.

Definition to_mref (R : sref) : mref :=
  {| mr_unit := sr_unit R; mr_mems := sr_mems R; mr_mod := option_map emod_of (sr_sig R);
     mr_public := true; mr_args := sr_args R |}.

Definition to_target (t : starget) : target :=
  match t with
  | st_mod R => tg_mod (to_mref R)
  | st_def R x => tg_mem (to_mref R) x
  end.

Definition to_alias (yt : (string * starget)%type) : (string * target)%type := (fst yt, to_target (snd yt)).

Definition to_os (sc : sscope) : oscope := os_mk (map to_alias (ss_alias sc)) (ss_units sc).

Definition to_of (F : sframe) : oframe :=
  of_mk (ef_mk (rev (map fst (sf_params F))) (emod_of (sf_cmds F)))
        (ptele (sf_params F)) (rev (sf_cmds F)) (to_os (sf_scope F)) (sf_path F).

Definition to_lent (d : nat) (b : lbind) : lent :=
  match b with
  | lb_var _ => le_term (a_var 0) (S d)
  | lb_let _ M => le_term M d
  | lb_mod _ R => le_mod (to_mref R) d
  end.

Fixpoint to_ls (L : list lbind) : lscope :=
  match L with
  | nil => nil
  | b :: L' => (lb_name b, to_lent (nbinders L') b) :: to_ls L'
  end.

(** A denotation applied to the arguments [args] of the spine it heads, in
    the elaborator's terms. *)
Definition fin (r : sres) (args : list exp) : option res :=
  match r with
  | s_term M => Some (r_exp (sc_apply M args))
  | s_mod R => Some (r_mod (to_mref (sr_app R args)))
  | s_def R x => Some (r_exp (sc_apply (a_glob (p_abs (sr_unit R) (sr_mems R ++ x :: nil))) (sr_args R ++ args)))
  end.

(** ** Generalities *)

Lemma ebind_eok : forall {A B} (m : eres A) (f : A -> eres B) b,
    ebind m f = eok b <-> exists a, m = eok a /\ f a = eok b.
Proof.
  intros; destruct m; cbn; split; intros H.
  - eauto.
  - destruct H as (? & [=<-] & ?); assumption.
  - discriminate.
  - destruct H as (? & ? & _); discriminate.
Qed.

Lemma echeck_eok : forall b e u, echeck b e = eok u <-> b = true.
Proof. intros [] ? []; cbn; split; congruence. Qed.

Lemma ebind_echeck : forall {B} b e (f : unit -> eres B) r,
    ebind (echeck b e) f = eok r <-> b = true /\ f tt = eok r.
Proof.
  intros; rewrite ebind_eok; split.
  - intros ([] & H1 & H2); apply echeck_eok in H1; auto.
  - intros [H1 H2]; exists tt; rewrite echeck_eok; auto.
Qed.

Lemma sr_app_nil : forall R, sr_app R nil = R.
Proof. intros []; unfold sr_app; cbn; rewrite app_nil_r; reflexivity. Qed.

Lemma sc_apply_app : forall M xs ys, sc_apply M (xs ++ ys) = sc_apply (sc_apply M xs) ys.
Proof. intros; unfold sc_apply; apply fold_left_app. Qed.

Lemma length_ptele : forall ps, List.length (ptele ps) = List.length ps.
Proof. intros; unfold ptele; rewrite length_rev, length_map; reflexivity. Qed.

Lemma nbinders_app : forall L1 L2, nbinders (L1 ++ L2) = nbinders L1 + nbinders L2.
Proof. induction L1; intros; cbn in *; [ reflexivity | unfold nbinders in *; rewrite IHL1; lia ]. Qed.

Lemma mr_weaken_to : forall d n R, mr_weaken d n (to_mref R) = to_mref (wk_sref (d - n) R).
Proof. reflexivity. Qed.

Lemma fin_sapp : forall r N args, fin (sapp r N) args = fin r (N :: args).
Proof.
  intros [M | R | R x] N args; cbn; try reflexivity;
    unfold to_mref, sr_app; cbn; rewrite <- app_assoc; reflexivity.
Qed.

Lemma mr_def_fin : forall R x args r,
    mr_def (to_mref R) x args = eok r <-> fin (s_def R x) args = Some r.
Proof.
  intros; unfold mr_def, fin, to_mref; cbn.
  split; intros H; inversion H; subst; reflexivity.
Qed.

(** Term and module positions. *)
Lemma res_term_fin : forall m P M,
    (forall r, m = eok r <-> exists sr, P sr /\ fin sr nil = Some r) ->
    res_term m = eok M <-> exists sr, P sr /\ as_term sr M.
Proof.
  intros m P M Hm; split.
  - intros H. destruct m as [r |]; [| discriminate ].
    destruct (proj1 (Hm r) eq_refl) as (sr & HP & Hf). exists sr; split; [ assumption |].
    destruct sr as [N | R | R x]; cbn in Hf.
    + inversion Hf; subst; cbn in H; inversion H; constructor.
    + inversion Hf; subst; cbn in H.
      destruct (sr_sig R) eqn:Hs; cbn in H; [ discriminate |].
      rewrite app_nil_r in H.
      destruct (sr_mems R) eqn:Hm'; [ discriminate |].
      inversion H; subst. rewrite <- Hm'. constructor; [ assumption | congruence ].
    + rewrite app_nil_r in Hf.
      inversion Hf; subst; cbn in H; inversion H; subst. constructor.
  - intros (sr & HP & Hat).
    inversion Hat; subst.
    + rewrite (proj2 (Hm _) (ex_intro _ _ (conj HP eq_refl))). reflexivity.
    + assert (Hf : fin (s_def R x) nil =
                   Some (r_exp (sc_apply (a_glob (p_abs (sr_unit R) (sr_mems R ++ x :: nil))) (sr_args R)))).
      { cbn; rewrite app_nil_r; reflexivity. }
      rewrite (proj2 (Hm _) (ex_intro _ _ (conj HP Hf))). reflexivity.
    + rewrite (proj2 (Hm _) (ex_intro _ _ (conj HP eq_refl))). cbn.
      rewrite H, app_nil_r. destruct (sr_mems R); [ contradiction | reflexivity ].
Qed.

Lemma res_mod_fin : forall m P mr,
    (forall r, m = eok r <-> exists sr, P sr /\ fin sr nil = Some r) ->
    res_mod m = eok mr <-> exists R, P (s_mod R) /\ mr = to_mref R.
Proof.
  intros m P mr Hm; split.
  - intros H. destruct m as [r |]; [| discriminate ].
    destruct (proj1 (Hm r) eq_refl) as (sr & HP & Hf).
    destruct sr as [N | R | R x]; cbn in Hf.
    + inversion Hf; subst; discriminate.
    + inversion Hf; subst; cbn in H; inversion H; subst.
      rewrite sr_app_nil. eauto.
    + inversion Hf; subst; discriminate.
  - intros (R & HP & ->).
    rewrite (proj2 (Hm (r_mod (to_mref R))) (ex_intro _ _ (conj HP (f_equal (fun R => Some (r_mod (to_mref R))) (sr_app_nil R))))).
    reflexivity.
Qed.

(** ** Members Read Off Commands *)

Lemma emod_ext_app : forall cs1 cs2 Φ, emod_ext Φ (cs1 ++ cs2) = emod_ext (emod_ext Φ cs1) cs2.
Proof. induction cs1; intros; cbn; auto. Qed.

Lemma emod_ext_one : forall c Φ,
    emod_ext Φ (c :: nil) =
      match cc_name c, en_of c with
      | Some x, Some e => em_ext Φ x e
      | _, _ => Φ
      end.
Proof. intros [] ?; reflexivity. Qed.

Lemma em_lookup_ext_neq : forall x y e Φ, x <> y -> em_lookup x (em_ext Φ y e) = em_lookup x Φ.
Proof. intros; cbn; apply String.eqb_neq in H; rewrite H; reflexivity. Qed.

Lemma em_lookup_ext_eq : forall x e Φ, em_lookup x (em_ext Φ x e) = Some e.
Proof. intros; cbn; rewrite String.eqb_refl; reflexivity. Qed.

Lemma emod_ext_nodecl : forall cs x Φ, ~ declares cs x -> em_lookup x (emod_ext Φ cs) = em_lookup x Φ.
Proof.
  induction cs as [| c cs IH]; intros x Φ Hd; [ reflexivity |].
  change (c :: cs) with ((c :: nil) ++ cs). rewrite emod_ext_app, IH.
  - rewrite emod_ext_one. destruct (cc_name c) as [y |] eqn:Hc; [| reflexivity ].
    destruct (en_of c); [| reflexivity ].
    apply em_lookup_ext_neq. intros ->. apply Hd. exists c; cbn; auto.
  - intros (c' & Hin & Hn). apply Hd. exists c'; cbn; auto.
Qed.

Lemma cc_name_en_of : forall c x, cc_name c = Some x -> exists e, en_of c = Some e.
Proof. intros [] ? H; cbn in *; try discriminate; eauto. Qed.

Lemma emod_ext_member : forall cs x c Φ, cs_member cs x c -> em_lookup x (emod_ext Φ cs) = en_of c.
Proof.
  intros * (cs1 & cs2 & -> & Hn & Hd).
  rewrite emod_ext_app. change (c :: cs2) with ((c :: nil) ++ cs2).
  rewrite emod_ext_app, emod_ext_nodecl by assumption.
  rewrite emod_ext_one, Hn. destruct (cc_name_en_of _ _ Hn) as [e He]; rewrite He.
  apply em_lookup_ext_eq.
Qed.

Lemma declares_member : forall cs x, declares cs x -> exists c, cs_member cs x c.
Proof.
  induction cs as [| c cs IH] using rev_ind; intros x (c' & Hin & Hn); [ destruct Hin |].
  destruct (cc_name c) as [y |] eqn:Hc; [ destruct (String.eqb_spec x y) as [-> |] |].
  - exists c, cs, nil; repeat split; auto. intros (? & [] & _).
  - assert (Hd : declares cs x).
    { apply in_app_or in Hin as [| [<- | []] ]; [ exists c'; auto | congruence ]. }
    destruct (IH _ Hd) as (c0 & cs1 & cs2 & -> & Hn0 & Hd0).
    exists c0, cs1, (cs2 ++ c :: nil). rewrite <- app_assoc. repeat split; auto.
    intros (c1 & Hin1 & Hn1). apply in_app_or in Hin1 as [| [<- | []] ]; [ apply Hd0; exists c1; auto | congruence ].
  - assert (Hd : declares cs x).
    { apply in_app_or in Hin as [| [<- | []] ]; [ exists c'; auto | congruence ]. }
    destruct (IH _ Hd) as (c0 & cs1 & cs2 & -> & Hn0 & Hd0).
    exists c0, cs1, (cs2 ++ c :: nil). rewrite <- app_assoc. repeat split; auto.
    intros (c1 & Hin1 & Hn1). apply in_app_or in Hin1 as [| [<- | []] ]; [ apply Hd0; exists c1; auto | congruence ].
Qed.

Lemma em_lookup_of_none : forall cs x, em_lookup x (emod_of cs) = None <-> ~ declares cs x.
Proof.
  intros; split.
  - intros H Hd. destruct (declares_member _ _ Hd) as [c Hc].
    unfold emod_of in H; rewrite (emod_ext_member _ _ _ _ Hc) in H.
    destruct Hc as (? & ? & _ & Hn & _). destruct (cc_name_en_of _ _ Hn); congruence.
  - intros Hd; unfold emod_of; rewrite emod_ext_nodecl; auto.
Qed.

Lemma declares_dec : forall cs x, declares cs x \/ ~ declares cs x.
Proof.
  induction cs as [| c cs IH]; intros x.
  - right; intros (? & [] & _).
  - destruct (IH x) as [(c' & ? & ?) | Hn].
    + left; exists c'; cbn; auto.
    + destruct (cc_name c) as [y |] eqn:Hc; [ destruct (String.eqb_spec y x) as [-> |] |].
      * left; exists c; cbn; auto.
      * right; intros (c' & [<- | Hin] & H'); [ congruence | apply Hn; exists c'; auto ].
      * right; intros (c' & [<- | Hin] & H'); [ congruence | apply Hn; exists c'; auto ].
Qed.

Lemma em_lookup_of_some : forall cs x e,
    em_lookup x (emod_of cs) = Some e <-> exists c, cs_member cs x c /\ en_of c = Some e.
Proof.
  intros; split.
  - intros H. destruct (declares_dec cs x) as [Hd | Hd].
    + destruct (declares_member _ _ Hd) as [c Hc]. exists c; split; [ assumption |].
      unfold emod_of in H; rewrite (emod_ext_member _ _ _ _ Hc) in H; assumption.
    + apply em_lookup_of_none in Hd; congruence.
  - intros (c & Hc & He). unfold emod_of; rewrite (emod_ext_member _ _ _ _ Hc); assumption.
Qed.

(** ** Projections of the Representation *)

Lemma of_alias_to : forall F, of_alias (to_of F) = os_alias (to_os (sf_scope F)).
Proof. reflexivity. Qed.
Lemma of_mod_to : forall F, ef_mod (of_names (to_of F)) = emod_of (sf_cmds F).
Proof. reflexivity. Qed.
Lemma of_pnames_to : forall F, ef_params (of_names (to_of F)) = rev (map fst (sf_params F)).
Proof. reflexivity. Qed.
Lemma of_params_to : forall F, of_params (to_of F) = ptele (sf_params F).
Proof. reflexivity. Qed.
Lemma of_path_to : forall F, of_path (to_of F) = sf_path F.
Proof. reflexivity. Qed.
Lemma of_scope_to : forall F, of_scope (to_of F) = to_os (sf_scope F).
Proof. reflexivity. Qed.
Lemma of_cmds_to : forall F, of_cmds (to_of F) = rev (sf_cmds F).
Proof. reflexivity. Qed.
Lemma os_alias_to : forall sc, os_alias (to_os sc) = map to_alias (ss_alias sc).
Proof. reflexivity. Qed.
Lemma os_units_to : forall sc, os_units (to_os sc) = ss_units sc.
Proof. reflexivity. Qed.
Lemma mr_apply_to : forall R args, mr_apply (to_mref R) args = to_mref (sr_app R args).
Proof. reflexivity. Qed.
Lemma nbinders_cons : forall b L, nbinders (b :: L) = lb_binders b + nbinders L.
Proof. reflexivity. Qed.

Ltac simpl_to :=
  rewrite ?of_alias_to, ?of_mod_to, ?of_pnames_to, ?of_params_to, ?of_path_to,
    ?of_scope_to, ?of_cmds_to, ?mr_apply_to in *.

(** ** Aliases *)

Lemma alias_lookup_none : forall x al, alias_lookup x (map to_alias al) = None <-> ~ In x (map fst al).
Proof.
  induction al as [| [y t] al IH]; cbn; [ tauto |].
  destruct (String.eqb_spec x y) as [-> | Hne].
  - split; [ discriminate | intros H; exfalso; auto ].
  - rewrite IH. split; intros H; [ intros [? | ?]; [ congruence | auto ] | auto ].
Qed.

Lemma alias_lookup_some : forall x al tg,
    alias_lookup x (map to_alias al) = Some tg ->
    exists t al1 al2, tg = to_target t /\ al = al1 ++ (x, t) :: al2 /\ ~ In x (map fst al1).
Proof.
  induction al as [| [y t] al IH]; cbn; intros tg H; [ discriminate |].
  destruct (String.eqb_spec x y) as [-> | Hne].
  - inversion H; subst. exists t, nil, al; cbn; auto.
  - destruct (IH _ H) as (t' & al1 & al2 & -> & -> & Hn).
    exists t', ((y, t) :: al1), al2; cbn; repeat split; auto.
    intros [? | ?]; [ congruence | auto ].
Qed.

Lemma alias_lookup_split : forall x t al1 al2,
    ~ In x (map fst al1) -> alias_lookup x (map to_alias (al1 ++ (x, t) :: al2)) = Some (to_target t).
Proof.
  induction al1 as [| [y t'] al1 IH]; cbn; intros.
  - rewrite String.eqb_refl; reflexivity.
  - destruct (String.eqb_spec x y); [ exfalso; auto |]. auto.
Qed.

Lemma ss_lookup_none : forall sc x, alias_lookup x (os_alias (to_os sc)) = None <-> ss_free sc x.
Proof. intros; rewrite os_alias_to in *; apply alias_lookup_none. Qed.

Lemma ss_lookup_some : forall sc x tg,
    alias_lookup x (os_alias (to_os sc)) = Some tg -> exists t, ss_binds sc x t /\ tg = to_target t.
Proof.
  intros * H; rewrite os_alias_to in *. destruct (alias_lookup_some _ _ _ H) as (t & al1 & al2 & -> & E & Hn).
  exists t; split; [ unfold ss_binds; rewrite E; apply in_or_app; right; left |]; reflexivity.
Qed.

(** With one alias per name, an alias is the one found. *)
Lemma ss_binds_lookup : forall sc x t l,
    NoDup (map fst (ss_alias sc) ++ l) ->
    ss_binds sc x t -> alias_lookup x (os_alias (to_os sc)) = Some (to_target t).
Proof.
  intros * Hnd Hb; rewrite os_alias_to. unfold ss_binds in Hb.
  apply in_split in Hb as (al1 & al2 & E). rewrite E in *. apply alias_lookup_split.
  rewrite map_app, <- app_assoc in Hnd. cbn in Hnd. apply NoDup_remove_2 in Hnd.
  intros Hin; apply Hnd, in_or_app; left; assumption.
Qed.

Lemma tg_use_fin : forall off t args r,
    tg_use (tg_local off (to_target t)) args = eok r <-> fin (st_res (wk_starget off t)) args = Some r.
Proof.
  intros off [R | R x] args r; cbn [to_target tg_local tg_use st_res wk_starget];
    rewrite mr_weaken_to, Nat.sub_0_r.
  - rewrite mr_apply_to; cbn; split; intros H; inversion H; reflexivity.
  - apply mr_def_fin.
Qed.

(** ** Pre-application *)

Definition tele (Fs : list sframe) : nat := fold_right (fun F n => List.length (sf_params F) + n) 0 Fs.

Lemma tele_cons : forall F Fs, tele (F :: Fs) = List.length (sf_params F) + tele Fs.
Proof. reflexivity. Qed.

Lemma fr_tele_len_to : forall Fs, fr_tele_len (map to_of Fs) = tele Fs.
Proof.
  induction Fs; cbn; [ reflexivity |].
  unfold fr_tele_len in *; cbn; simpl_to; rewrite length_ptele, IHFs; reflexivity.
Qed.

Lemma map_seq_add : forall (f : nat -> exp) b a s,
    map f (seq (b + s) a) = map (fun j => f (b + j)) (seq s a).
Proof.
  induction a; intros; cbn; [ reflexivity |].
  f_equal. rewrite <- Nat.add_succ_r. apply IHa.
Qed.

Lemma vars_desc_add : forall off a b, vars_desc off (a + b) = vars_desc (off + a) b ++ vars_desc off a.
Proof.
  intros; unfold vars_desc. rewrite (Nat.add_comm a b), seq_app, map_app. f_equal.
  - apply map_ext_in. intros i Hi. apply in_seq in Hi. f_equal. lia.
  - replace (0 + b) with (b + 0) by lia. rewrite map_seq_add.
    apply map_ext_in. intros i Hi. apply in_seq in Hi. f_equal. lia.
Qed.

(** [preapp] gives the elaborator's [param_vars]. *)
Lemma preapp_iff : forall Fs off vs, preapp off Fs vs <-> vs = vars_desc off (tele Fs).
Proof.
  induction Fs as [| F Fs IH]; intros; split.
  - inversion 1; reflexivity.
  - intros ->; constructor.
  - inversion 1 as [| ? ? ? ? Hp]; subst. apply IH in Hp; subst.
    rewrite tele_cons, vars_desc_add. reflexivity.
  - intros ->. rewrite tele_cons, vars_desc_add. constructor. apply IH. reflexivity.
Qed.

Lemma param_vars_desc : param_vars = vars_desc.
Proof. reflexivity. Qed.

(** ** Parameters *)

Lemma index_of_split : forall x l k,
    index_of x l = Some k -> exists l1 l2, l = l1 ++ x :: l2 /\ ~ In x l1 /\ k = List.length l1.
Proof.
  induction l as [| a l IH]; cbn; [ discriminate |]; intros k.
  destruct (String.eqb_spec x a) as [<- | Hne].
  - intros [=<-]; exists nil, l; cbn; auto.
  - destruct (index_of x l) eqn:E; cbn; [| discriminate ].
    intros [=<-]. destruct (IH _ eq_refl) as (l1 & l2 & -> & Hn & ->).
    exists (a :: l1), l2; cbn; repeat split; auto.
    intros [? | ?]; [ congruence | auto ].
Qed.

Lemma index_of_app : forall x l1 l2, ~ In x l1 -> index_of x (l1 ++ x :: l2) = Some (List.length l1).
Proof.
  induction l1 as [| a l1 IH]; cbn; intros.
  - rewrite String.eqb_refl; reflexivity.
  - destruct (String.eqb_spec x a); [ exfalso; auto |]. rewrite IH; auto.
Qed.

Lemma index_of_none : forall x l, index_of x l = None <-> ~ In x l.
Proof.
  induction l as [| a l IH]; cbn; [ tauto |].
  destruct (String.eqb_spec x a) as [<- | Hne].
  - split; [ discriminate | intros H; exfalso; auto ].
  - destruct (index_of x l) eqn:E; cbn.
    + split; [ discriminate |]. intros H; exfalso; apply H; right.
      destruct (index_of_split _ _ _ E) as (l1 & l2 & -> & _).
      apply in_or_app; right; left; reflexivity.
    + split; intros _; [| reflexivity ].
      intros [? | Hin]; [ congruence | apply (proj1 IH eq_refl Hin) ].
Qed.

Lemma param_index_some : forall x (ps : list (string * typ)) k,
    index_of x (rev (map fst ps)) = Some k ->
    exists ps1 A ps2, ps = ps1 ++ (x, A) :: ps2 /\ ~ In x (map fst ps2) /\ k = List.length ps2.
Proof.
  intros * H. destruct (index_of_split _ _ _ H) as (l1 & l2 & E & Hn & ->).
  apply (f_equal (@rev _)) in E. rewrite rev_involutive, rev_app_distr in E. cbn in E.
  rewrite <- app_assoc in E. cbn in E.
  apply map_eq_app in E as (ps1 & ps' & -> & E1 & E2).
  apply map_eq_cons in E2 as ([y A] & ps2 & -> & Ey & E2). cbn in Ey; subst y.
  exists ps1, A, ps2; repeat split.
  - rewrite E2, <- in_rev; assumption.
  - rewrite <- (length_map fst), E2, length_rev; reflexivity.
Qed.

Lemma param_index_split : forall x (A : typ) (ps1 ps2 : list (string * typ)),
    ~ In x (map fst ps2) ->
    index_of x (rev (map fst (ps1 ++ (x, A) :: ps2))) = Some (List.length ps2).
Proof.
  intros. rewrite map_app, rev_app_distr. cbn. rewrite <- app_assoc. cbn.
  rewrite index_of_app.
  - rewrite length_rev, length_map; reflexivity.
  - rewrite <- in_rev; assumption.
Qed.

Lemma param_index_none : forall x (ps : list (string * typ)), index_of x (rev (map fst ps)) = None <-> ~ In x (map fst ps).
Proof. intros; rewrite index_of_none, <- in_rev; reflexivity. Qed.

(** ** Local Bindings *)

Lemma ls_lookup_some : forall L x e,
    ls_lookup x (to_ls L) = Some e ->
    exists L1 b L2, L = L1 ++ b :: L2 /\ lb_name b = x /\ ~ In x (map lb_name L1) /\
               e = to_lent (nbinders L2) b.
Proof.
  induction L as [| b L IH]; cbn; intros x e H; [ discriminate |].
  destruct (String.eqb_spec x (lb_name b)) as [-> | Hne].
  - inversion H; subst. exists nil, b, L; cbn; auto.
  - destruct (IH _ _ H) as (L1 & b' & L2 & -> & ? & ? & ->).
    exists (b :: L1), b', L2; cbn; repeat split; auto.
    intros [? | ?]; [ congruence | auto ].
Qed.

Lemma ls_lookup_bound : forall L1 b L2 x,
    lb_name b = x -> ~ In x (map lb_name L1) ->
    ls_lookup x (to_ls (L1 ++ b :: L2)) = Some (to_lent (nbinders L2) b).
Proof.
  induction L1 as [| b' L1 IH]; cbn; intros b L2 x Hb Hn.
  - subst; rewrite String.eqb_refl; reflexivity.
  - destruct (String.eqb_spec x (lb_name b')); [ exfalso; auto |]. auto.
Qed.

Lemma ls_lookup_none : forall L x, ls_lookup x (to_ls L) = None <-> ~ In x (map lb_name L).
Proof.
  induction L as [| b L IH]; cbn; intros; [ tauto |].
  destruct (String.eqb_spec x (lb_name b)) as [-> | Hne].
  - split; [ discriminate | intros H; exfalso; auto ].
  - rewrite IH. split; intros H; [ intros [? | ?]; [ congruence | auto ] | auto ].
Qed.

Lemma lent_fin : forall L1 b L2 args r,
    match to_lent (nbinders L2) b with
    | le_term M n => eok (r_exp (sc_apply (sc_shift (nbinders (L1 ++ b :: L2)) n M) args))
    | le_mod mr n => eok (r_mod (mr_apply (mr_weaken (nbinders (L1 ++ b :: L2)) n mr) args))
    end = eok r <-> fin (ldenote (nbinders L1) b) args = Some r.
Proof.
  intros. rewrite nbinders_app, nbinders_cons.
  destruct b as [y | y M | y R]; cbn [lb_binders to_lent ldenote fin].
  - unfold sc_shift. cbn [exp_wk wk_shiftn].
    replace (nbinders L1 + (1 + nbinders L2) - S (nbinders L2)) with (nbinders L1) by lia.
    split; intros H; inversion H; reflexivity.
  - unfold sc_shift, shift_by.
    replace (nbinders L1 + (1 + nbinders L2) - nbinders L2) with (S (nbinders L1)) by lia.
    split; intros H; inversion H; reflexivity.
  - rewrite mr_weaken_to.
    replace (nbinders L1 + (0 + nbinders L2) - nbinders L2) with (nbinders L1) by lia.
    rewrite mr_apply_to. split; intros H; inversion H; reflexivity.
Qed.

(** ** Member Selection *)

Lemma em_lookup_member : forall cs x c, cs_member cs x c -> em_lookup x (emod_of cs) = en_of c.
Proof. intros; apply emod_ext_member; assumption. Qed.

Lemma cs_member_name : forall cs x c, cs_member cs x c -> cc_name c = Some x.
Proof. intros * (? & ? & _ & H & _); exact H. Qed.

Ltac inv_eok := match goal with H : eok _ = eok _ |- _ => inversion H; subst; clear H end.
Ltac inv_some := match goal with H : Some _ = Some _ |- _ => inversion H; subst; clear H end.

(** The member [c] that an [em_lookup] found, with its name. *)
Ltac found_member Em :=
  apply em_lookup_of_some in Em as (c & Hmem & He); destruct c; cbn in He; try discriminate; inversion He; subst;
  match goal with
  | Hm : cs_member _ ?x (cc_def ?s _ _ _ _) |- _ =>
      assert (s = x) by (apply cs_member_name in Hm; cbn in Hm; congruence); subst s
  | Hm : cs_member _ ?x (cc_mod ?s _ _) |- _ =>
      assert (s = x) by (apply cs_member_name in Hm; cbn in Hm; congruence); subst s
  end.

Lemma mr_member_iff : forall R x args r,
    mr_member (to_mref R) x args = eok r <->
    exists t, select R x t /\ fin (st_res t) args = Some r.
Proof.
  intros [u ms sg ag] x args r. split.
  - intros H. unfold mr_member in H; cbn [to_mref mr_mod mr_args mr_mems mr_unit mr_public sr_sig sr_args sr_mems sr_unit] in H.
    destruct sg as [cs |]; cbn [option_map] in H.
    + destruct (em_lookup x (emod_of cs)) as [[pv | n Φ] |] eqn:Em; cbn in H; [| | discriminate ].
      * found_member Em. destruct pv; cbn in H; [ discriminate |].
        exists (st_def (sr_mk u ms (Some cs) ag) x). split.
        -- eapply sl_def; [ reflexivity | eassumption ].
        -- apply (proj1 (mr_def_fin (sr_mk u ms (Some cs) ag) x args r)); exact H.
      * found_member Em. inv_eok.
        eexists; split; [ eapply sl_mod; [ reflexivity | eassumption ] | reflexivity ].
    + inv_eok. eexists; split; [ apply sl_opaque; reflexivity | reflexivity ].
  - intros (t & Hs & Hf). inversion Hs; subst; cbn [sr_sig] in *; subst; unfold mr_member;
      cbn [to_mref mr_mod mr_args mr_mems mr_unit mr_public option_map sr_sig sr_args sr_mems sr_unit].
    + cbn in Hf; inv_some; reflexivity.
    + rewrite (em_lookup_member _ _ _ H0); cbn [en_of negb andb].
      apply (proj2 (mr_def_fin (sr_mk u ms (Some cs) ag) x args r)); exact Hf.
    + rewrite (em_lookup_member _ _ _ H0); cbn [en_of]. cbn in Hf; inv_some; reflexivity.
Qed.

(** ** Names in the Open Frames *)

Lemma fr_tele_len_cons_to : forall F Fs, fr_tele_len (to_of F :: map to_of Fs) = tele (F :: Fs).
Proof. intros; exact (fr_tele_len_to (F :: Fs)). Qed.

Lemma sc_apply_apps : forall M xs ys, sc_apply (apps M xs) ys = sc_apply M (xs ++ ys).
Proof. intros; symmetry; apply sc_apply_app. Qed.

(** ** One Binding per Name *)

Lemma NoDup_app_disj : forall (l1 l2 : list string) x, NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
  induction l1 as [| a l1 IH]; cbn; intros l2 x Hnd H1 H2; [ assumption |].
  inversion Hnd; subst. destruct H1 as [<- | H1]; [| eauto ].
  apply H3, in_or_app; right; assumption.
Qed.

Lemma in_decl_names : forall cs x, In x (decl_names cs) <-> declares cs x.
Proof.
  intros; unfold decl_names, declares; rewrite in_flat_map. split.
  - intros (c & Hin & Hx). exists c; split; [ assumption |].
    destruct (cc_name c); cbn in Hx; [ destruct Hx as [<- | []]; reflexivity | destruct Hx ].
  - intros (c & Hin & Hx). exists c; split; [ assumption |]. rewrite Hx; left; reflexivity.
Qed.

Lemma cs_member_declares : forall cs x c, cs_member cs x c -> declares cs x.
Proof.
  intros * (cs1 & cs2 & -> & Hn & _). exists c; split; [ apply in_or_app; right; left |]; auto.
Qed.

(** In a well-formed frame a member is not also an alias … *)
Lemma wf_member_free : forall F x c, sf_wf F -> cs_member (sf_cmds F) x c -> ss_free (sf_scope F) x.
Proof.
  intros * Hw Hm Hin. apply cs_member_declares, in_decl_names in Hm.
  eapply NoDup_app_disj; [ exact Hw | exact Hin | apply in_or_app; left; exact Hm ].
Qed.

(** … and a parameter is neither an alias, nor a member, nor repeated. *)
Lemma wf_param : forall F x A ps1 ps2,
    sf_wf F -> sf_params F = ps1 ++ (x, A) :: ps2 ->
    ss_free (sf_scope F) x /\ ~ declares (sf_cmds F) x /\ ~ In x (map fst ps2).
Proof.
  intros * Hw Hp. unfold sf_wf, sf_names, sf_taken in Hw. rewrite Hp, map_app in Hw.
  assert (Hx : In x (map fst ps1 ++ map fst ((x, A) :: ps2))) by (apply in_or_app; right; left; reflexivity).
  repeat split.
  - intros Hin. eapply NoDup_app_disj; [ exact Hw | exact Hin | apply in_or_app; right; exact Hx ].
  - intros Hd. apply in_decl_names in Hd.
    apply NoDup_app_remove_l in Hw.
    eapply NoDup_app_disj; [ exact Hw | exact Hd | exact Hx ].
  - intros Hin. do 2 apply NoDup_app_remove_l in Hw. cbn in Hw. apply NoDup_remove_2 in Hw. apply Hw, in_or_app; right; exact Hin.
Qed.

Lemma wf_alias_nodup : forall F, sf_wf F -> NoDup (map fst (ss_alias (sf_scope F)) ++ sf_taken F).
Proof. intros; assumption. Qed.

Lemma not_binds : forall F x,
    ss_free (sf_scope F) x -> ~ declares (sf_cmds F) x -> ~ In x (map fst (sf_params F)) -> ~ sf_binds F x.
Proof.
  unfold sf_binds, sf_names, sf_taken. intros * Ha Hd Hp Hin.
  apply in_app_or in Hin as [Hin | Hin]; [ exact (Ha Hin) |].
  apply in_app_or in Hin as [Hin | Hin]; [ apply Hd, in_decl_names, Hin | exact (Hp Hin) ].
Qed.

Lemma binds_not : forall F x,
    ~ sf_binds F x -> ss_free (sf_scope F) x /\ ~ declares (sf_cmds F) x /\ ~ In x (map fst (sf_params F)).
Proof.
  unfold sf_binds, sf_names, sf_taken. intros * Hn; repeat split; intros Hin; apply Hn.
  - apply in_or_app; left; assumption.
  - apply in_or_app; right; apply in_or_app; left; apply in_decl_names; assumption.
  - apply in_or_app; right; apply in_or_app; right; assumption.
Qed.

Ltac rewrite_free :=
  match goal with Hf : ss_free _ _ |- _ => rewrite (proj2 (ss_lookup_none _ _) Hf) end.
Ltac rewrite_member :=
  match goal with Hm : cs_member _ _ _ |- _ => rewrite (em_lookup_member _ _ _ Hm) end.

Section Lookup.
  Variable (fp : fpath) (O : sscope).
  Hypothesis (HO : ss_wf O).

  Lemma fr_lookup_iff : forall Fs off x args r,
      Forall sf_wf Fs ->
      fr_lookup fp (to_os O) off x (map to_of Fs) args = eok r <->
      exists sr, fbind fp O off Fs x sr /\ fin sr args = Some r.
  Proof.
    induction Fs as [| F Fs IH]; intros off x args r HFs; cbn [map fr_lookup]; split.
    - intros H. destruct (alias_lookup x (os_alias (to_os O))) as [tg |] eqn:E; [| discriminate ].
      destruct (ss_lookup_some _ _ _ E) as (t & Hb & ->). apply tg_use_fin in H.
      eexists; split; [ apply fb_outer; eassumption | exact H ].
    - intros (sr & Hf & H). inversion Hf; subst.
      rewrite (ss_binds_lookup _ _ _ nil ltac:(rewrite app_nil_r; exact HO) ltac:(eassumption)).
      apply tg_use_fin; assumption.
    - inversion HFs as [| ? ? HF HFs']; subst.
      intros H. rewrite fr_tele_len_cons_to in H. simpl_to.
      destruct (alias_lookup x (os_alias (to_os (sf_scope F)))) as [tg |] eqn:Ea.
      + destruct (ss_lookup_some _ _ _ Ea) as (t & Hb & ->). apply tg_use_fin in H.
        eexists; split; [ apply fb_here, fr_alias; eassumption | exact H ].
      + apply ss_lookup_none in Ea.
        destruct (em_lookup x (emod_of (sf_cmds F))) as [[pv | n Φ] |] eqn:Em.
        * found_member Em. inv_eok.
          eexists; split; [ eapply fb_here, fr_def; [ eassumption | apply preapp_iff; reflexivity ] |].
          cbn [fin]. rewrite sc_apply_apps. reflexivity.
        * found_member Em. inv_eok.
          eexists; split; [ eapply fb_here, fr_mod; [ eassumption | apply preapp_iff; reflexivity ] |].
          cbn [fin]. reflexivity.
        * apply em_lookup_of_none in Em.
          destruct (index_of x (rev (map fst (sf_params F)))) as [k |] eqn:Ei.
          -- apply param_index_some in Ei as (ps1 & A & ps2 & Hps & Hn & ->). inv_eok.
             eexists; split; [ eapply fb_here, fr_param; eassumption | reflexivity ].
          -- apply param_index_none in Ei. rewrite length_ptele in H.
             apply IH in H as (sr & Hf & Hfin); [| assumption ]. exists sr; split; [| assumption ].
             apply fb_next; [ apply not_binds; assumption | assumption ].
    - inversion HFs as [| ? ? HF HFs']; subst.
      intros (sr & Hf & H). rewrite fr_tele_len_cons_to. simpl_to.
      inversion Hf as [? ? ? ? ? Hb | ? ? ? ? ? Hn Hnext |]; subst.
      + inversion Hb; subst.
        * rewrite (ss_binds_lookup _ _ _ _ (wf_alias_nodup _ HF) ltac:(eassumption)).
          apply tg_use_fin; assumption.
        * rewrite (proj2 (ss_lookup_none _ _) (wf_member_free _ _ _ HF ltac:(eassumption))).
          rewrite_member. cbn [en_of].
          match goal with Hp : preapp _ _ _ |- _ => apply preapp_iff in Hp; subst end.
          cbn [fin] in H; inv_some. rewrite sc_apply_apps. reflexivity.
        * rewrite (proj2 (ss_lookup_none _ _) (wf_member_free _ _ _ HF ltac:(eassumption))).
          rewrite_member. cbn [en_of].
          match goal with Hp : preapp _ _ _ |- _ => apply preapp_iff in Hp; subst end.
          cbn [fin] in H; inv_some. reflexivity.
        * match goal with Hp : sf_params _ = _ |- _ =>
            destruct (wf_param _ _ _ _ _ HF Hp) as (Ha & Hd & Hn2); rewrite Hp end.
          rewrite (proj2 (ss_lookup_none _ _) Ha).
          match goal with Hp : sf_params _ = _ |- _ => rewrite <- Hp end.
          rewrite (proj2 (em_lookup_of_none _ _) Hd).
          match goal with Hp : sf_params _ = _ |- _ => rewrite Hp end.
          rewrite param_index_split by assumption.
          cbn [fin] in H; inv_some. reflexivity.
      + destruct (binds_not _ _ Hn) as (Ha & Hd & Hp).
        rewrite (proj2 (ss_lookup_none _ _) Ha), (proj2 (em_lookup_of_none _ _) Hd),
          (proj2 (param_index_none _ _) Hp), length_ptele.
        apply IH; eauto.
  Qed.
End Lookup.


(** ** Objects *)

Lemma existsb_path_beq : forall fq l, existsb (path_beq fq) l = true <-> In fq l.
Proof.
  intros; rewrite existsb_exists; split.
  - intros (y & Hin & Hb); apply path_beq_true in Hb; subst; assumption.
  - intros Hin; exists fq; split; [ assumption | apply path_beq_refl ].
Qed.

Lemma unit_reachable_iff : forall fq O Fs,
    unit_reachable (to_os O) (map to_of Fs) fq = true <-> unit_in fq O Fs.
Proof.
  intros; unfold unit_reachable, os_has_unit, unit_in.
  rewrite orb_true_iff, existsb_path_beq, existsb_exists. rewrite ?of_scope_to, ?os_units_to in *.
  split; intros [H | H]; auto; right.
  - destruct H as (f & Hin & Hf). apply in_map_iff in Hin as (F & <- & Hin).
    rewrite ?of_scope_to, ?os_units_to in *. apply existsb_path_beq in Hf. eauto.
  - destruct H as (F & Hin & Hf). exists (to_of F); split; [ apply in_map; assumption |].
    rewrite ?of_scope_to, ?os_units_to in *. apply existsb_path_beq; assumption.
Qed.

Scheme obj_mind := Induction for Cst.obj Sort Prop
  with decl_mind := Induction for Cst.decl Sort Prop.

Section Objects.
  Variable (fp : fpath) (O : sscope) (Fs : list sframe).
  Hypotheses (HO : ss_wf O) (HFs : Forall sf_wf Fs).

  #[local] Abbreviation elab_res := (elab_res fp (to_os O) (map to_of Fs)).

  Definition P_obj (o : Cst.obj) : Prop :=
    forall L args r,
      elab_res (to_ls L) (nbinders L) o args = eok r <->
      exists sr, sel fp O Fs L o sr /\ fin sr args = Some r.

  Definition P_decl (d : Cst.decl) : Prop :=
    match d with
    | Cst.d_def _ _ oA oM => P_obj oA /\ P_obj oM
    | Cst.d_mod _ oE => P_obj oE
    end.

  Lemma sel_term_iff : forall o, P_obj o -> forall L M,
      res_term (elab_res (to_ls L) (nbinders L) o nil) = eok M <-> selt fp O Fs L o M.
  Proof.
    intros o IH L M. rewrite (res_term_fin _ (sel fp O Fs L o) M (fun r => IH L nil r)).
    split; [ intros (sr & ? & ?); econstructor; eauto | inversion 1; eauto ].
  Qed.

  Lemma sel_mod_iff : forall o, P_obj o -> forall L mr,
      res_mod (elab_res (to_ls L) (nbinders L) o nil) = eok mr <->
      exists R, sel fp O Fs L o (s_mod R) /\ mr = to_mref R.
  Proof. intros o IH L mr. apply (res_mod_fin _ (sel fp O Fs L o) mr (fun r => IH L nil r)). Qed.

  Ltac fwd_term IH L H :=
    let M := fresh "M" in let HM := fresh "HM" in let HT := fresh "HT" in
    apply ebind_eok in H as (M & HM & H);
    pose proof (proj1 (sel_term_iff _ IH L M) HM) as HT; clear HM.

  Ltac bwd_term IH L :=
    apply ebind_eok; eexists; split; [ exact (proj2 (sel_term_iff _ IH L _) ltac:(eassumption)) |].

  Lemma elab_res_iff : forall o, P_obj o.
  Proof.
    apply (obj_mind P_obj P_decl); unfold P_obj; intros.
    - (* typ *) cbn [Elaborator.elab_res].
      split; [ intros H; inv_eok; eexists; split; [ constructor | reflexivity ]
             | intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some; reflexivity ].
    - (* nat *) cbn [Elaborator.elab_res].
      split; [ intros H; inv_eok; eexists; split; [ constructor | reflexivity ]
             | intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some; reflexivity ].
    - (* zero *) cbn [Elaborator.elab_res].
      split; [ intros H; inv_eok; eexists; split; [ constructor | reflexivity ]
             | intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some; reflexivity ].
    - (* succ *)
      cbn [Elaborator.elab_res]. split.
      + intros Hr. fwd_term H L Hr. inv_eok.
        eexists; split; [ constructor; eassumption | reflexivity ].
      + intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some.
        bwd_term H L. reflexivity.
    - (* natrec *)
      cbn [Elaborator.elab_res]. split.
      + intros Hr. fwd_term H L Hr. fwd_term H0 (lb_var s :: L) Hr. fwd_term H1 L Hr.
        fwd_term H2 (lb_var s1 :: lb_var s0 :: L) Hr. inv_eok.
        eexists; split; [ constructor; eassumption | reflexivity ].
      + intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some.
        bwd_term H L. bwd_term H0 (lb_var s :: L). bwd_term H1 L.
        bwd_term H2 (lb_var s1 :: lb_var s0 :: L). reflexivity.
    - (* pi *)
      cbn [Elaborator.elab_res]. split.
      + intros Hr. fwd_term H L Hr. fwd_term H0 (lb_var s :: L) Hr. inv_eok.
        eexists; split; [ constructor; eassumption | reflexivity ].
      + intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some.
        bwd_term H L. bwd_term H0 (lb_var s :: L). reflexivity.
    - (* fn *)
      cbn [Elaborator.elab_res]. split.
      + intros Hr. fwd_term H L Hr. fwd_term H0 (lb_var s :: L) Hr. inv_eok.
        eexists; split; [ constructor; eassumption | reflexivity ].
      + intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some.
        bwd_term H L. bwd_term H0 (lb_var s :: L). reflexivity.
    - (* app *)
      cbn [Elaborator.elab_res]. split.
      + intros Hr. fwd_term H0 L Hr. apply H in Hr as (sr & Hs & Hf).
        exists (sapp sr M); split; [ econstructor; eassumption | rewrite fin_sapp; assumption ].
      + intros (sr & Hs & Hf); inversion Hs; subst. rewrite fin_sapp in Hf.
        bwd_term H0 L. apply H. eauto.
    - (* var *)
      cbn [Elaborator.elab_res]. split.
      + intros Hr. destruct (ls_lookup s (to_ls L)) as [e |] eqn:E.
        * apply ls_lookup_some in E as (L1 & b & L2 & -> & Hb & Hn & ->).
          apply lent_fin in Hr. eexists; split; [ apply sel_local; exists L1, L2; eauto | exact Hr ].
        * apply ls_lookup_none in E. apply (fr_lookup_iff fp O HO) in Hr as (sr & Hb & Hf); [| exact HFs ].
          eexists; split; [ apply sel_frame; eassumption | exact Hf ].
      + intros (sr & Hs & Hf); inversion Hs; subst.
        * match goal with Hl : lbound _ _ _ _ |- _ => destruct Hl as (L1 & L2 & -> & Hb & Hn & ->) end.
          rewrite (ls_lookup_bound _ _ _ _ Hb Hn). apply lent_fin; assumption.
        * match goal with Hn : ~ In _ (map lb_name _) |- _ => rewrite (proj2 (ls_lookup_none _ _) Hn) end. apply (fr_lookup_iff fp O HO); eauto.
    - (* glob *)
      cbn [Elaborator.elab_res]. rewrite ebind_echeck, unit_reachable_iff. split.
      + intros [Hu Hr]; inv_eok. eexists; split; [ constructor; assumption | reflexivity ].
      + intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some. split; [ assumption | reflexivity ].
    - (* proj *)
      cbn [Elaborator.elab_res]. rewrite ebind_eok. split.
      + intros (mr & Hm & Hr). apply (sel_mod_iff _ H) in Hm as (R & HR & ->).
        apply mr_member_iff in Hr as (t & Ht & Hf).
        eexists; split; [ econstructor; eassumption | exact Hf ].
      + intros (sr & Hs & Hf); inversion Hs; subst. exists (to_mref R); split.
        * apply (sel_mod_iff _ H); eauto.
        * apply mr_member_iff; eauto.
    - (* letb *)
      destruct d as [m x oA oM | x oE]; cbn [P_decl] in H; cbn [Elaborator.elab_res].
      + destruct H as [HA HM]. split.
        * intros Hr. fwd_term HA L Hr. fwd_term HM L Hr.
          destruct (Cst.md_abstract m) eqn:Ea.
          -- fwd_term H0 (lb_var x :: L) Hr. inv_eok.
             eexists; split; [ eapply sel_let_abs; eassumption | reflexivity ].
          -- fwd_term H0 (lb_let x M0 :: L) Hr. inv_eok.
             eexists; split; [ eapply sel_let; eassumption | reflexivity ].
        * intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some.
          -- bwd_term HA L. bwd_term HM L.
             match goal with Ea : Cst.md_abstract _ = _ |- _ => rewrite Ea end.
             bwd_term H0 (lb_let x M :: L). reflexivity.
          -- bwd_term HA L. bwd_term HM L.
             match goal with Ea : Cst.md_abstract _ = _ |- _ => rewrite Ea end.
             bwd_term H0 (lb_var x :: L). reflexivity.
      + rewrite ebind_eok. split.
        * intros (mr & Hm & Hr). apply (sel_mod_iff _ H) in Hm as (R & HR & ->).
          fwd_term H0 (lb_mod x R :: L) Hr. inv_eok.
          eexists; split; [ econstructor; eassumption | reflexivity ].
        * intros (sr & Hs & Hf); inversion Hs; subst; cbn in Hf; inv_some.
          exists (to_mref R); split; [ apply (sel_mod_iff _ H); eauto |].
          bwd_term H0 (lb_mod x R :: L). reflexivity.
    - (* d_def *) cbn; auto.
    - (* d_mod *) cbn; auto.
  Qed.

  Corollary elab_term_iff : forall L o M,
      res_term (elab_res (to_ls L) (nbinders L) o nil) = eok M <-> selt fp O Fs L o M.
  Proof. intros; apply sel_term_iff, elab_res_iff. Qed.

  Corollary elab_mod_iff : forall L o mr,
      res_mod (elab_res (to_ls L) (nbinders L) o nil) = eok mr <->
      exists R, sel fp O Fs L o (s_mod R) /\ mr = to_mref R.
  Proof. intros; apply sel_mod_iff, elab_res_iff. Qed.

  Lemma sparams_names : forall L ps tys, sparams fp O Fs L ps tys -> map fst tys = map fst ps.
  Proof. induction 1; cbn; congruence. Qed.

  Lemma elab_params_iff : forall ps L Δ0 Δ,
      elab_params fp (to_os O) (map to_of Fs) (to_ls L) (nbinders L) ps Δ0 = eok Δ <->
      exists tys, sparams fp O Fs L ps tys /\ Δ = ptele tys ++ Δ0.
  Proof.
    induction ps as [| [x oA] ps IH]; intros; cbn [elab_params]; split.
    - intros H; inv_eok. exists nil; split; [ constructor | reflexivity ].
    - intros (tys & Hs & ->); inversion Hs; subst; reflexivity.
    - intros H. apply ebind_eok in H as (A & HA & H).
      apply (proj1 (elab_term_iff L oA A)) in HA.
      apply (proj1 (IH (lb_var x :: L) _ _)) in H as (tys & Hs & ->).
      exists ((x, A) :: tys); split; [ constructor; assumption |].
      unfold ptele; cbn. rewrite <- app_assoc; reflexivity.
    - intros (tys & Hs & ->); inversion Hs; subst.
      apply ebind_eok; eexists; split; [ apply (proj2 (elab_term_iff L oA _)); eassumption |].
      apply (proj2 (IH (lb_var x :: L) _ _)). eexists; split; [ eassumption |].
      unfold ptele; cbn. rewrite <- app_assoc; reflexivity.
  Qed.
End Objects.

(** ** Imports *)

Lemma os_fresh_to : forall sc y, os_fresh y (to_os sc) = true <-> ss_free sc y.
Proof.
  intros; unfold os_fresh; rewrite <- ss_lookup_none.
  destruct (alias_lookup y (os_alias (to_os sc))); split; congruence.
Qed.

(** [taken] decides membership in the list [tl]. *)
Definition decides (taken : string -> bool) (tl : list string) : Prop := forall y, taken y = true <-> In y tl.

Lemma alias_fresh_check : forall taken tl sc y,
    decides taken tl ->
    negb (taken y) && os_fresh y (to_os sc) = true <-> alias_fresh tl sc y.
Proof.
  intros * Ht. unfold alias_fresh. rewrite andb_true_iff, negb_true_iff, os_fresh_to.
  specialize (Ht y). destruct (taken y); split; intros [H1 H2]; split; try assumption; try discriminate.
  - exfalso; exact (H1 (proj1 Ht eq_refl)).
  - intros Hy; discriminate (proj2 Ht Hy).
  - reflexivity.
Qed.

Section Imports.
  Variable (taken : string -> bool) (tl : list string).
  Hypothesis (Ht : decides taken tl).

  Lemma use_bind_iff : forall R sc n sc1,
      use_bind taken (to_mref R) (eok (to_os sc)) n = eok sc1 <->
      exists t, alias_fresh tl sc n /\ select R n t /\ sc1 = to_os (ss_add n t sc).
  Proof.
    intros [u ms sg ag] sc n sc1. unfold use_bind. rewrite ebind_eok. split.
    - intros (sc0 & [=<-] & H). apply ebind_echeck in H as [Hf H]. apply (alias_fresh_check _ _ _ _ Ht) in Hf.
      cbn [to_mref mr_mod mr_args mr_mems mr_unit mr_public sr_sig sr_args sr_mems sr_unit option_map] in H.
      destruct sg as [cs |]; cbn [option_map] in H.
      + destruct (em_lookup n (emod_of cs)) as [[pv | k Φ] |] eqn:Em; cbn in H; [| | discriminate ].
        * found_member Em. destruct pv; cbn in H; [ discriminate |]. inv_eok.
          eexists; split; [ eassumption |]; split; [ eapply sl_def; [ reflexivity | eassumption ] | reflexivity ].
        * found_member Em. inv_eok.
          eexists; split; [ eassumption |]; split; [ eapply sl_mod; [ reflexivity | eassumption ] | reflexivity ].
      + inv_eok. eexists; split; [ eassumption |]; split; [ apply sl_opaque; reflexivity | reflexivity ].
    - intros (t & Hf & Hs & ->). exists (to_os sc); split; [ reflexivity |].
      apply ebind_echeck; split; [ apply (alias_fresh_check _ _ _ _ Ht); assumption |].
      inversion Hs; subst; cbn [sr_sig] in *; subst;
        cbn [to_mref mr_mod mr_args mr_mems mr_unit mr_public sr_sig sr_args sr_mems sr_unit option_map].
      + reflexivity.
      + rewrite_member. reflexivity.
      + rewrite_member. reflexivity.
  Qed.

  Lemma fold_use_err : forall mr ns e, exists e', fold_left (use_bind taken mr) ns (eerr e) = eerr e'.
  Proof. induction ns; intros; cbn; eauto. Qed.

  Lemma use_binds_iff : forall ns R sc sc'',
      fold_left (use_bind taken (to_mref R)) ns (eok (to_os sc)) = eok sc'' <->
      exists sc', use_binds R tl ns sc sc' /\ sc'' = to_os sc'.
  Proof.
    induction ns as [| n ns IH]; intros; cbn [fold_left]; split.
    - intros H; inv_eok. eexists; split; [ constructor | reflexivity ].
    - intros (sc' & Hu & ->); inversion Hu; subst; reflexivity.
    - intros H. destruct (use_bind taken (to_mref R) (eok (to_os sc)) n) as [sc1 | e] eqn:E.
      + apply use_bind_iff in E as (t & Hf & Hs & ->). apply IH in H as (sc' & Hu & ->).
        eexists; split; [ econstructor; eassumption | reflexivity ].
      + destruct (fold_use_err (to_mref R) ns e) as [e' He]; congruence.
    - intros (sc' & Hu & ->); inversion Hu; subst.
      match goal with Hf : alias_fresh _ _ _, Hs : select _ _ ?t |- _ =>
        rewrite (proj2 (use_bind_iff R sc n (to_os (ss_add n t sc))) (ex_intro _ t (conj Hf (conj Hs eq_refl)))) end.
      apply IH; eauto.
  Qed.

  Lemma import_binds_unit : forall fq mr spec sc,
      import_binds taken fq mr spec (to_os sc) =
        match spec with
        | Cst.i_open => eok (to_os (ss_add_unit fq sc))
        | Cst.i_as y =>
            let* _ := echeck (negb (taken y) && os_fresh y (to_os (ss_add_unit fq sc)))
                        (y ++ " is already declared")%string in
            eok (os_alias_add y (tg_mod mr) (to_os (ss_add_unit fq sc)))
        | Cst.i_use ns => fold_left (use_bind taken mr) ns (eok (to_os (ss_add_unit fq sc)))
        end.
  Proof. intros; destruct fq; reflexivity. Qed.

  Lemma import_binds_iff : forall fq R spec sc sc'',
      import_binds taken fq (to_mref R) spec (to_os sc) = eok sc'' <->
      exists sc', ibinds R tl spec (ss_add_unit fq sc) sc' /\ sc'' = to_os sc'.
  Proof.
    intros. rewrite import_binds_unit. destruct spec as [| y | ns].
    - split; [ intros H; inv_eok; eexists; split; [ constructor | reflexivity ]
             | intros (sc' & Hb & ->); inversion Hb; subst; reflexivity ].
    - rewrite ebind_echeck, (alias_fresh_check _ _ _ _ Ht). split.
      + intros [Hf H]; inv_eok. eexists; split; [ constructor; assumption | reflexivity ].
      + intros (sc' & Hb & ->); inversion Hb; subst. split; [ assumption | reflexivity ].
    - rewrite use_binds_iff. split.
      + intros (sc' & Hu & ->). eexists; split; [ constructor; eassumption | reflexivity ].
      + intros (sc' & Hb & ->); inversion Hb; subst. eauto.
  Qed.
End Imports.

Section ImportTargets.
  Variable (fp : fpath).

  Lemma import_target_iff : forall O Fs u fq ip mr,
      ss_wf O -> Forall sf_wf Fs ->
      import_target (us_mk fp (to_os O) (map to_of Fs) u) fq ip = eok mr <->
      exists R, itarget fp O Fs fq ip R /\ mr = to_mref R.
  Proof.
    intros * HO HFs. unfold import_target. destruct fq as [| a fq]; [ destruct ip as [| x ip] |]; cbn beta iota.
    - split; [ discriminate | intros (R & HR & _); inversion HR; congruence ].
    - split.
      + intros H. destruct (proj1 (elab_mod_iff fp O Fs HO HFs nil _ mr) H) as (R & HR & ->).
        eexists; split; [ constructor; eassumption | reflexivity ].
      + intros (R & HR & ->). inversion HR; subst; [| congruence ].
        exact (proj2 (elab_mod_iff fp O Fs HO HFs nil _ _) (ex_intro _ R (conj ltac:(eassumption) eq_refl))).
    - split.
      + intros H; inv_eok. eexists; split; [ constructor; discriminate | reflexivity ].
      + intros (R & HR & ->). inversion HR; subst. reflexivity.
  Qed.

  Lemma import_iff : forall taken tl O Fs u fq ip spec sc sc'',
      decides taken tl -> ss_wf O -> Forall sf_wf Fs ->
      (exists mr, import_target (us_mk fp (to_os O) (map to_of Fs) u) fq ip = eok mr /\
             import_binds taken fq mr spec (to_os sc) = eok sc'') <->
      exists sc', simport fp O Fs tl sc (Cst.c_import fq ip spec) sc' (import_cmd fq ip) /\ sc'' = to_os sc'.
  Proof.
    intros * Ht HO HFs; split.
    - intros (mr & Htg & Hb). apply (import_target_iff _ _ _ _ _ _ HO HFs) in Htg as (R & HR & ->).
      apply (import_binds_iff _ _ Ht) in Hb as (sc' & Hb & ->).
      eexists; split; [ econstructor; eassumption | reflexivity ].
    - intros (sc' & Hs & ->). inversion Hs; subst. exists (to_mref R); split.
      + apply (import_target_iff _ _ _ _ _ _ HO HFs); eauto.
      + apply (import_binds_iff _ _ Ht); eauto.
  Qed.
End ImportTargets.

(** What a frame's [of_taken] decides: its members and parameters. *)
Lemma of_taken_decides : forall F, decides (fun y => of_taken y (to_of F)) (sf_taken F).
Proof.
  intros F y. unfold of_taken, sf_taken. simpl_to. rewrite in_app_iff, in_decl_names.
  destruct (em_lookup y (emod_of (sf_cmds F))) eqn:Em.
  - split; [ intros _; left | reflexivity ].
    destruct (declares_dec (sf_cmds F) y) as [| Hd]; [ assumption |].
    apply em_lookup_of_none in Hd; congruence.
  - apply em_lookup_of_none in Em.
    destruct (index_of y (rev (map fst (sf_params F)))) eqn:Ei.
    + split; [ intros _; right | reflexivity ].
      apply param_index_some in Ei as (ps1 & A & ps2 & -> & _).
      rewrite map_app; apply in_or_app; right; left; reflexivity.
    + apply param_index_none in Ei. split; [ discriminate | intros [|]; contradiction ].
Qed.

Lemma nothing_decides : decides (fun _ => false) nil.
Proof. intros y; split; [ discriminate | intros [] ]. Qed.

(** ** Commands *)

Definition cmd_ind' (P : Cst.cmd -> Prop)
  (Hmod : forall p ps body, Forall P body -> P (Cst.c_mod p ps body))
  (Hdef : forall m x oA oM, P (Cst.c_def m x oA oM))
  (Himp : forall fq ip s, P (Cst.c_import fq ip s))
  (Heval : forall oM oA, P (Cst.c_eval oM oA)) : forall c, P c :=
  fix go c :=
    match c with
    | Cst.c_mod p ps body =>
        Hmod p ps body
          ((fix gol (l : list Cst.cmd) : Forall P l :=
              match l with
              | nil => Forall_nil P
              | c' :: l' => @Forall_cons _ P c' l' (go c') (gol l')
              end) body)
    | Cst.c_def m x oA oM => Hdef m x oA oM
    | Cst.c_import fq ip s => Himp fq ip s
    | Cst.c_eval oM oA => Heval oM oA
    end.

Lemma elab_cmd_def : forall st m x oA oM, elab_cmd st (Cst.c_def m x oA oM) = elab_def st m x oA oM.
Proof. reflexivity. Qed.
Lemma elab_cmd_eval : forall st oM oA, elab_cmd st (Cst.c_eval oM oA) = elab_eval st oM oA.
Proof. reflexivity. Qed.
Lemma elab_cmd_import : forall st fq ip s, elab_cmd st (Cst.c_import fq ip s) = elab_import st fq ip s.
Proof. reflexivity. Qed.
Lemma elab_cmds_cons : forall st c cs, elab_cmds st (c :: cs) = ebind (elab_cmd st c) (fun st' => elab_cmds st' cs).
Proof. reflexivity. Qed.

Lemma elab_cmd_mod_one : forall st x ps body,
    elab_cmd st (Cst.c_mod (x :: nil) ps body) =
      let* _ := us_top st (fun f => let* _ := echeck (of_fresh x f) (x ++ " is already declared")%string in eok f) in
      let* f := (let* _ := check_params ps in
                 let* Δ := elab_params (us_unit st) (us_outer st) (us_frames st) nil 0 ps ⋅ in
                 eok (of_new (rev (map fst ps)) Δ (us_path st ++ x :: nil))) in
      let* st1 := elab_cmds (us_open st f) body in
      us_close x st1.
Proof. reflexivity. Qed.

Lemma elab_cmd_mod_path : forall st x y p ps body,
    elab_cmd st (Cst.c_mod (x :: y :: p) ps body) =
      let* _ := us_top st (fun f => let* _ := echeck (of_fresh x f) (x ++ " is already declared")%string in eok f) in
      let* f := eok (of_new nil ⋅ (us_path st ++ x :: nil)) in
      let* st1 := elab_cmd (us_open st f) (Cst.c_mod (y :: p) ps body) in
      us_close x st1.
Proof. reflexivity. Qed.

Lemma us_top_cons : forall u os g gs imps f,
    us_top (us_mk u os (g :: gs) imps) f = ebind (f g) (fun g' => eok (us_mk u os (g' :: gs) imps)).
Proof. reflexivity. Qed.

Lemma us_scope_cons : forall u os g gs imps oc f,
    us_scope (us_mk u os (g :: gs) imps) oc f =
      ebind (f (of_scope g)) (fun sc => eok (us_mk u os
        ({| of_names := of_names g; of_params := of_params g;
            of_cmds := match oc with Some c => c :: of_cmds g | None => of_cmds g end;
            of_scope := sc; of_path := of_path g |} :: gs) imps)).
Proof. reflexivity. Qed.

Lemma us_scope_nil : forall u os imps oc f,
    us_scope (us_mk u os nil imps) oc f =
      ebind (f os) (fun sc => eok (us_mk u sc nil (match oc with Some c => c :: imps | None => imps end))).
Proof. reflexivity. Qed.

Lemma us_close_cons : forall x u os f g gs imps,
    us_close x (us_mk u os (f :: g :: gs) imps) =
      eok (us_mk u os (of_add x (en_mod (List.length (ef_params (of_names f))) (ef_mod (of_names f)))
                              (cc_mod x (of_params f) (rev (of_cmds f))) g :: gs) imps).
Proof. reflexivity. Qed.

Lemma of_fresh_to : forall F x, of_fresh x (to_of F) = true <-> sf_fresh F x.
Proof.
  intros F x. unfold of_fresh, sf_fresh, sf_binds, sf_names. simpl_to.
  pose proof (of_taken_decides F x) as Ht. rewrite in_app_iff.
  destruct (alias_lookup x (os_alias (to_os (sf_scope F)))) eqn:Ea.
  - split; [ discriminate |]. intros Hn; exfalso; apply Hn; left.
    destruct (in_dec string_dec x (map fst (ss_alias (sf_scope F)))) as [| Hi]; [ assumption |].
    apply ss_lookup_none in Hi; congruence.
  - apply ss_lookup_none in Ea. rewrite negb_true_iff.
    destruct (of_taken x (to_of F)); split; intros H.
    + discriminate.
    + exfalso; apply H; right; apply Ht; reflexivity.
    + intros [Hi | Hi]; [ exact (Ea Hi) | apply Ht in Hi; discriminate ].
    + reflexivity.
Qed.

Lemma first_dup_none : forall xs, first_dup xs = None <-> NoDup xs.
Proof.
  induction xs as [| a xs IH]; cbn; split; intros H.
  - constructor.
  - reflexivity.
  - destruct (existsb (String.eqb a) xs) eqn:E; [ discriminate |]. constructor; [| apply IH; assumption ].
    intros Hin.
    assert (existsb (String.eqb a) xs = true)
      by (apply existsb_exists; exists a; split; [ assumption | apply String.eqb_refl ]).
    congruence.
  - inversion H; subst. destruct (existsb (String.eqb a) xs) eqn:E; [| apply IH; assumption ].
    apply existsb_exists in E as (b & Hb & Hab). apply String.eqb_eq in Hab; subst. contradiction.
Qed.

Lemma check_params_ok : forall ps u, check_params ps = eok u <-> NoDup (map fst ps).
Proof.
  intros ps []. unfold check_params. rewrite <- first_dup_none.
  destruct (first_dup (map fst ps)); split; congruence.
Qed.

Lemma to_of_emit : forall F c x e,
    cc_name c = Some x -> en_of c = Some e -> of_add x e c (to_of F) = to_of (sf_emit F c).
Proof.
  intros * Hn He. unfold of_add, to_of, sf_emit.
  cbn [sf_path sf_params sf_cmds sf_scope of_names of_params of_cmds of_scope of_path ef_params ef_mod].
  rewrite rev_unit. unfold emod_of; rewrite emod_ext_app, emod_ext_one, Hn, He. reflexivity.
Qed.

Lemma to_of_eval : forall F M A,
    {| of_names := of_names (to_of F); of_params := of_params (to_of F);
       of_cmds := cc_eval M A :: of_cmds (to_of F); of_scope := of_scope (to_of F);
       of_path := of_path (to_of F) |} = to_of (sf_emit F (cc_eval M A)).
Proof.
  intros; unfold to_of, sf_emit.
  cbn [sf_path sf_params sf_cmds sf_scope of_names of_params of_cmds of_scope of_path].
  rewrite rev_unit. unfold emod_of; rewrite emod_ext_app; reflexivity.
Qed.

Lemma to_of_import : forall F fq ip sc',
    {| of_names := of_names (to_of F); of_params := of_params (to_of F);
       of_cmds := match import_cmd fq ip with Some c => c :: of_cmds (to_of F) | None => of_cmds (to_of F) end;
       of_scope := to_os sc'; of_path := of_path (to_of F) |} =
    to_of (sf_mk (sf_path F) (sf_params F) (sf_cmds F ++ opt_list (import_cmd fq ip)) sc').
Proof.
  intros; destruct fq; unfold to_of;
    cbn [sf_path sf_params sf_cmds sf_scope of_names of_params of_cmds of_scope of_path import_cmd opt_list].
  - rewrite app_nil_r; reflexivity.
  - rewrite rev_unit. unfold emod_of; rewrite emod_ext_app; reflexivity.
Qed.

Lemma of_new_to : forall (ps : list (string * Cst.obj)) tys ip,
    map fst tys = map fst ps -> of_new (rev (map fst ps)) (ptele tys) ip = to_of (sf_new ip tys).
Proof. intros * E; unfold of_new, to_of, sf_new; cbn; rewrite E; reflexivity. Qed.

Lemma to_of_close : forall F N x tys,
    sf_params N = tys ->
    of_add x (en_mod (List.length (ef_params (of_names (to_of N)))) (ef_mod (of_names (to_of N))))
      (cc_mod x (of_params (to_of N)) (rev (of_cmds (to_of N)))) (to_of F) =
    to_of (sf_emit F (cc_mod x (ptele tys) (sf_cmds N))).
Proof.
  intros * E. simpl_to. rewrite rev_involutive, E. apply to_of_emit; [ reflexivity |].
  cbn [en_of]. rewrite length_rev, length_map, length_ptele. reflexivity.
Qed.

Scheme scmd_mind := Induction for scmd Sort Prop
  with scmds_mind := Induction for scmds Sort Prop.

Lemma scmds_shape : forall fp O Fs F cs F', scmds fp O Fs F cs F' -> sf_params F' = sf_params F.
Proof.
  intros fp O.
  apply (scmds_mind fp O (fun Fs F c F' _ => sf_params F' = sf_params F) (fun Fs F cs F' _ => sf_params F' = sf_params F));
    intros; cbn; congruence.
Qed.

Lemma scmd_shape : forall fp O Fs F c F', scmd fp O Fs F c F' -> sf_params F' = sf_params F.
Proof.
  intros fp O.
  apply (scmd_mind fp O (fun Fs F c F' _ => sf_params F' = sf_params F) (fun Fs F cs F' _ => sf_params F' = sf_params F));
    intros; cbn; congruence.
Qed.

Section Commands.
  Variable (fp : fpath).

  #[local] Abbreviation st_of O F Fs imps := (us_mk fp (to_os O) (to_of F :: map to_of Fs) imps).

  (** A command, run in a well-formed state. *)
  Definition P_cmd (c : Cst.cmd) : Prop :=
    forall O Fs F imps st',
      ss_wf O -> Forall sf_wf Fs -> sf_wf F ->
      elab_cmd (st_of O F Fs imps) c = eok st' <->
      exists F', scmd fp O Fs F c F' /\ st' = st_of O F' Fs imps.

  Definition P_cmds (cs : list Cst.cmd) : Prop :=
    forall O Fs F imps st',
      ss_wf O -> Forall sf_wf Fs -> sf_wf F ->
      elab_cmds (st_of O F Fs imps) cs = eok st' <->
      exists F', scmds fp O Fs F cs F' /\ st' = st_of O F' Fs imps.

  Lemma P_cmds_of : forall cs, Forall P_cmd cs -> P_cmds cs.
  Proof.
    induction 1 as [| c cs Hc Hcs IH]; intros O Fs F imps st' HO HFs HF; split.
    - intros H; cbn in H; inv_eok. eexists; split; [ constructor | reflexivity ].
    - intros (F' & Hs & ->). inversion Hs; subst; reflexivity.
    - intros H. rewrite elab_cmds_cons in H. apply ebind_eok in H as (st1 & H1 & H2).
      apply Hc in H1 as (F1 & Hs1 & ->); [| assumption.. ].
      apply IH in H2 as (F2 & Hs2 & ->); [| eauto using scmd_wf .. ].
      eexists; split; [ econstructor; eassumption | reflexivity ].
    - intros (F' & Hs & ->). inversion Hs; subst. rewrite elab_cmds_cons. apply ebind_eok.
      eexists; split; [ apply Hc; eauto | apply IH; eauto using scmd_wf ].
  Qed.

  Lemma us_top_fresh : forall O F Fs imps x u,
      us_top (st_of O F Fs imps)
        (fun f => let* _ := echeck (of_fresh x f) (x ++ " is already declared")%string in eok f) = eok u ->
      sf_fresh F x.
  Proof.
    intros * H. rewrite us_top_cons in H. apply ebind_eok in H as (g & Hg & _).
    apply ebind_echeck in Hg as [Hf _]. apply of_fresh_to; assumption.
  Qed.

  Lemma fresh_us_top : forall O F Fs imps x,
      sf_fresh F x ->
      us_top (st_of O F Fs imps)
        (fun f => let* _ := echeck (of_fresh x f) (x ++ " is already declared")%string in eok f) = eok (st_of O F Fs imps).
  Proof. intros * Hf. rewrite us_top_cons. apply of_fresh_to in Hf. rewrite Hf. reflexivity. Qed.

  Theorem elab_cmd_iff : forall c, P_cmd c.
  Proof.
    apply cmd_ind'.
    - (* module *)
      intros p ps body Hbody. apply P_cmds_of in Hbody.
      destruct p as [| x p]; [ intros O Fs F imps st' _ _ _; split;
                               [ intros H; cbn in H; discriminate | intros (F' & Hs & _); inversion Hs ] |].
      revert x. induction p as [| y p IHp]; intros x O Fs F imps st' HO HFs HF.
      + rewrite elab_cmd_mod_one. split.
        * intros H. apply ebind_eok in H as (u & Hu & H). apply us_top_fresh in Hu.
          apply ebind_eok in H as (f & Hf & H). apply ebind_eok in Hf as ([] & Hc & Hf).
          apply check_params_ok in Hc.
          apply ebind_eok in Hf as (Δ & HΔ & Hf). inv_eok.
          destruct (proj1 (elab_params_iff fp O (F :: Fs) HO (Forall_cons _ HF HFs) ps nil ⋅ Δ) HΔ)
            as (tys & Htys & ->).
          apply ebind_eok in H as (st1 & Hst1 & H).
          pose proof (sparams_names _ _ _ _ _ _ Htys) as Hnames.
          rewrite app_nil_r, (of_new_to _ _ _ Hnames) in Hst1.
          destruct (proj1 (Hbody O (F :: Fs) (sf_new (sf_path F ++ x :: nil) tys) imps st1
                             HO (Forall_cons _ HF HFs) ltac:(apply sf_wf_new; rewrite Hnames; exact Hc)) Hst1)
            as (N & HN & ->).
          cbn [map] in H. rewrite us_close_cons in H. inv_eok.
          eexists; split; [ eapply sc_mod; eassumption |].
          do 2 f_equal. apply to_of_close. apply (scmds_shape _ _ _ _ _ _ HN).
        * intros (F' & Hs & ->). inversion Hs; subst; [| congruence ].
          match goal with
          | Ht : sparams _ _ _ _ _ _, HN : scmds _ _ _ _ _ _, Hc : NoDup _ |- _ =>
              rename Ht into Htys; rename HN into HN'; rename Hc into Hnd
          end.
          pose proof (sparams_names _ _ _ _ _ _ Htys) as Hnames.
          apply ebind_eok; eexists; split; [ apply fresh_us_top; eassumption |].
          apply ebind_eok; eexists; split.
          { apply ebind_eok; exists tt; split; [ apply check_params_ok; exact Hnd |].
            apply ebind_eok; eexists; split;
              [ exact (proj2 (elab_params_iff fp O (F :: Fs) HO (Forall_cons _ HF HFs) ps nil ⋅ _)
                         (ex_intro _ tys (conj Htys eq_refl)))
              | reflexivity ]. }
          apply ebind_eok; eexists; split.
          { rewrite app_nil_r, (of_new_to _ _ _ Hnames).
            exact (proj2 (Hbody O (F :: Fs) _ imps _ HO (Forall_cons _ HF HFs)
                            ltac:(apply sf_wf_new; rewrite Hnames; exact Hnd))
                     (ex_intro _ N (conj HN' eq_refl))). }
          cbn [map]. rewrite us_close_cons. do 3 f_equal.
          apply to_of_close. exact (scmds_shape _ _ _ _ _ _ HN').
      + assert (Hnew : sf_wf (sf_new (sf_path F ++ x :: nil) nil)) by (apply sf_wf_new; constructor).
        rewrite elab_cmd_mod_path. split.
        * intros H. apply ebind_eok in H as (u & Hu & H). apply us_top_fresh in Hu.
          cbn [ebind] in H. apply ebind_eok in H as (st1 & Hst1 & H).
          destruct (proj1 (IHp y O (F :: Fs) (sf_new (sf_path F ++ x :: nil) nil) imps st1
                             HO (Forall_cons _ HF HFs) Hnew) Hst1)
            as (N & HN & ->).
          cbn [map] in H. rewrite us_close_cons in H. inv_eok.
          eexists; split; [ eapply sc_mod_path; [ discriminate | eassumption | eassumption ] |].
          do 2 f_equal. apply (to_of_close _ _ _ nil). exact (scmd_shape _ _ _ _ _ _ HN).
        * intros (F' & Hs & ->). inversion Hs; subst.
          apply ebind_eok; eexists; split; [ apply fresh_us_top; eassumption |].
          cbn [ebind]. apply ebind_eok; eexists; split.
          { exact (proj2 (IHp y O (F :: Fs) (sf_new (sf_path F ++ x :: nil) nil) imps _
                            HO (Forall_cons _ HF HFs) Hnew)
                     (ex_intro _ N (conj ltac:(eassumption) eq_refl))). }
          cbn [map]. rewrite us_close_cons. do 3 f_equal.
          apply (to_of_close _ _ _ nil).
          match goal with HN : scmd _ _ _ _ _ _ |- _ => exact (scmd_shape _ _ _ _ _ _ HN) end.
    - (* definition *)
      intros m x oA oM O Fs F imps st' HO HFs HF.
      pose proof (Forall_cons _ HF HFs) as HFFs.
      rewrite elab_cmd_def. unfold elab_def.
      rewrite us_top_cons, ebind_eok. split.
      + intros (g & Hg & H). inv_eok. apply ebind_echeck in Hg as [Hfr Hg].
        apply ebind_eok in Hg as (A & HA & Hg). apply ebind_eok in Hg as (M & HM & Hg). inv_eok.
        pose proof (proj1 (elab_term_iff fp O (F :: Fs) HO HFFs nil oA A) HA) as HA'.
        pose proof (proj1 (elab_term_iff fp O (F :: Fs) HO HFFs nil oM M) HM) as HM'.
        eexists; split; [ apply sc_def; [ apply of_fresh_to; exact Hfr | exact HA' | exact HM' ] |].
        do 2 f_equal. apply to_of_emit; reflexivity.
      + intros (F' & Hs & ->). inversion Hs; subst. eexists; split.
        * apply ebind_echeck; split; [ apply of_fresh_to; assumption |].
          apply ebind_eok; eexists; split; [ exact (proj2 (elab_term_iff fp O (F :: Fs) HO HFFs nil oA _) ltac:(eassumption)) |].
          apply ebind_eok; eexists; split; [ exact (proj2 (elab_term_iff fp O (F :: Fs) HO HFFs nil oM _) ltac:(eassumption)) |].
          reflexivity.
        * do 3 f_equal. apply to_of_emit; reflexivity.
    - (* import *)
      intros fq ip spec O Fs F imps st' HO HFs HF.
      pose proof (Forall_cons _ HF HFs) as HFFs.
      rewrite elab_cmd_import. unfold elab_import. cbn [us_frames].
      rewrite ebind_eok. split.
      + intros (mr & Hmr & H). rewrite us_scope_cons in H. apply ebind_eok in H as (sc'' & Hb & H). inv_eok.
        destruct (proj1 (import_iff fp _ _ O (F :: Fs) imps fq ip spec (sf_scope F) sc''
                           (of_taken_decides F) HO HFFs) (ex_intro _ mr (conj Hmr Hb)))
          as (sc' & Hs & ->).
        eexists; split; [ apply sc_import; eassumption |].
        do 2 f_equal. exact (to_of_import F fq ip sc').
      + intros (F' & Hs & ->). inversion Hs; subst.
        match goal with Hi : simport _ _ _ _ _ _ _ _ |- _ =>
          rename Hi into Himp; pose proof Himp as Hi'; inversion Hi'; subst; clear Hi' end.
        destruct (proj2 (import_iff fp _ _ O (F :: Fs) imps fq ip spec (sf_scope F) _
                           (of_taken_decides F) HO HFFs)
                    (ex_intro _ sc' (conj Himp eq_refl))) as (mr & Hmr & Hb).
        exists mr; split; [ exact Hmr |]. rewrite us_scope_cons. apply ebind_eok; eexists; split; [ exact Hb |].
        do 3 f_equal. exact (to_of_import F fq ip sc').
    - (* eval *)
      intros oM oA O Fs F imps st' HO HFs HF.
      pose proof (Forall_cons _ HF HFs) as HFFs.
      rewrite elab_cmd_eval. unfold elab_eval.
      rewrite us_top_cons, ebind_eok. destruct oA as [oA |]; split.
      + intros (g & Hg & H). inv_eok. apply ebind_eok in Hg as (M & HM & Hg).
        apply ebind_eok in Hg as (oT & HT & Hg). inv_eok. apply ebind_eok in HT as (A & HA & HT). inv_eok.
        eexists; split.
        * apply sc_eval_typ; [ exact (proj1 (elab_term_iff fp O (F :: Fs) HO HFFs nil oM M) HM)
                             | exact (proj1 (elab_term_iff fp O (F :: Fs) HO HFFs nil oA A) HA) ].
        * do 2 f_equal. exact (to_of_eval F M (Some A)).
      + intros (F' & Hs & ->). inversion Hs; subst. eexists; split.
        * apply ebind_eok; eexists; split; [ exact (proj2 (elab_term_iff fp O (F :: Fs) HO HFFs nil oM _) ltac:(eassumption)) |].
          apply ebind_eok; eexists; split.
          -- apply ebind_eok; eexists; split; [ exact (proj2 (elab_term_iff fp O (F :: Fs) HO HFFs nil oA _) ltac:(eassumption)) |].
             reflexivity.
          -- reflexivity.
        * do 3 f_equal. apply to_of_eval.
      + intros (g & Hg & H). inv_eok. apply ebind_eok in Hg as (M & HM & Hg). cbn [ebind] in Hg. inv_eok.
        eexists; split.
        * apply sc_eval. exact (proj1 (elab_term_iff fp O (F :: Fs) HO HFFs nil oM M) HM).
        * do 2 f_equal. exact (to_of_eval F M None).
      + intros (F' & Hs & ->). inversion Hs; subst. eexists; split.
        * apply ebind_eok; eexists; split; [ exact (proj2 (elab_term_iff fp O (F :: Fs) HO HFFs nil oM _) ltac:(eassumption)) |].
          reflexivity.
        * do 3 f_equal. apply to_of_eval.
  Qed.

  Corollary elab_cmds_iff : forall cs, P_cmds cs.
  Proof. intros; apply P_cmds_of, Forall_forall; intros; apply elab_cmd_iff. Qed.

  Lemma simport_ss_wf : forall O Fs sc c sc' oc, simport fp O Fs nil sc c sc' oc -> ss_wf sc -> ss_wf sc'.
  Proof.
    unfold ss_wf; intros * Hs Hw. pose proof (simport_wf _ _ _ _ _ _ _ _ Hs) as H.
    rewrite !app_nil_r in H. auto.
  Qed.

  (** The imports before the unit's declaration, outside all frames. *)
  Lemma elab_cmds_outer_iff : forall cs O imps st',
      ss_wf O ->
      elab_cmds (us_mk fp (to_os O) nil imps) cs = eok st' <->
      exists O' is, simports fp O cs O' is /\ st' = us_mk fp (to_os O') nil (rev is ++ imps).
  Proof.
    induction cs as [| c cs IH]; intros O imps st' HO; split.
    - intros H; cbn in H; inv_eok. exists O, nil; split; [ constructor | reflexivity ].
    - intros (O' & is & Hs & ->). inversion Hs; subst. reflexivity.
    - intros H. rewrite elab_cmds_cons in H. apply ebind_eok in H as (st1 & H1 & H2).
      destruct c as [p ps body | m x oA oM | fq ip spec | oM oA].
      + exfalso. destruct p as [| x [| y p] ];
          [ cbn in H1 | rewrite elab_cmd_mod_one in H1 | rewrite elab_cmd_mod_path in H1 ]; cbn in H1; discriminate.
      + exfalso. rewrite elab_cmd_def in H1. cbn in H1. discriminate.
      + rewrite elab_cmd_import in H1. unfold elab_import in H1. cbn [us_frames] in H1.
        apply ebind_eok in H1 as (mr & Hmr & H1). rewrite us_scope_nil in H1.
        apply ebind_eok in H1 as (sc'' & Hb & H1). inv_eok.
        destruct (proj1 (import_iff fp _ _ O nil imps fq ip spec O sc'' nothing_decides HO (Forall_nil _))
                    (ex_intro _ mr (conj Hmr Hb)))
          as (O1 & Hs1 & ->).
        apply IH in H2 as (O2 & is & Hs2 & ->); [| eapply simport_ss_wf; eassumption ].
        exists O2, (opt_list (import_cmd fq ip) ++ is); split; [ econstructor; eassumption |].
        f_equal. rewrite rev_app_distr, <- app_assoc. f_equal. destruct fq; reflexivity.
      + exfalso. rewrite elab_cmd_eval in H1. cbn in H1. discriminate.
    - intros (O' & is & Hs & ->). inversion Hs; subst.
      match goal with Hi : simport _ _ _ _ _ _ _ _ |- _ => pose proof Hi as Hi'; inversion Hi'; subst; clear Hi' end.
      rewrite elab_cmds_cons, elab_cmd_import.
      unfold elab_import. cbn [us_frames].
      match goal with Hi : simport _ _ _ _ _ _ ?O1 _, Hr : simports _ ?O1 _ _ ?is0 |- _ =>
        destruct (proj2 (import_iff fp _ _ O nil imps fq ip spec O _ nothing_decides HO (Forall_nil _))
                    (ex_intro _ O1 (conj Hi eq_refl)))
          as (mr & Hmr & Hb);
        apply ebind_eok; eexists; split;
        [ apply ebind_eok; exists mr; split; [ exact Hmr |];
          rewrite us_scope_nil; apply ebind_eok; eexists; split; [ exact Hb | reflexivity ] |];
        apply IH; [ eapply simport_ss_wf; eassumption |]; exists O', is0; split; [ exact Hr |]
      end.
      f_equal. rewrite rev_app_distr, <- app_assoc. f_equal. destruct fq; reflexivity.
  Qed.
End Commands.

(** ** The Theorems *)

Lemma ss_wf_empty : ss_wf ss_empty.
Proof. constructor. Qed.

Theorem elaborate_core_iff : forall prg u, elaborate_core prg = eok u <-> elab_spec prg u.
Proof.
  intros [imports [[fp ps] cs]] u. cbv beta iota zeta delta [elaborate_core]. split.
  - intros H. apply ebind_eok in H as (st0 & H0 & H).
    destruct (proj1 (elab_cmds_outer_iff fp imports ss_empty nil st0 ss_wf_empty) H0) as (O & imps & Hi & ->).
    pose proof (simports_wf _ _ _ _ _ Hi ss_wf_empty) as HO.
    apply ebind_eok in H as ([] & Hc & H). apply check_params_ok in Hc.
    apply ebind_eok in H as (Δ & HΔ & H).
    destruct (proj1 (elab_params_iff fp O nil HO (Forall_nil _) ps nil ⋅ Δ) HΔ) as (tys & Htys & ->).
    apply ebind_eok in H as (st & Hst & H).
    pose proof (sparams_names _ _ _ _ _ _ Htys) as Hnames.
    rewrite (app_nil_r (ptele tys)), (of_new_to _ _ _ Hnames) in Hst.
    destruct (proj1 (elab_cmds_iff fp cs O nil (sf_new nil tys) (rev imps ++ nil) st HO (Forall_nil _)
                       ltac:(apply sf_wf_new; rewrite Hnames; exact Hc)) Hst) as (F & HF & ->).
    cbn [us_frames map] in H. inv_eok.
    simpl_to. rewrite app_nil_r, rev_involutive, rev_involutive, (scmds_shape _ _ _ _ _ _ HF).
    econstructor; eassumption.
  - intros Hs. inversion Hs as [? ? ? ? O imps tys F Hi Hnd Htys HF]; subst.
    pose proof (simports_wf _ _ _ _ _ Hi ss_wf_empty) as HO.
    pose proof (sparams_names _ _ _ _ _ _ Htys) as Hnames.
    apply ebind_eok; eexists; split;
      [ exact (proj2 (elab_cmds_outer_iff fp imports ss_empty nil _ ss_wf_empty)
                 (ex_intro _ O (ex_intro _ imps (conj Hi eq_refl)))) |].
    apply ebind_eok; exists tt; split; [ apply check_params_ok; exact Hnd |].
    apply ebind_eok; eexists; split;
      [ exact (proj2 (elab_params_iff fp O nil HO (Forall_nil _) ps nil ⋅ _) (ex_intro _ tys (conj Htys eq_refl))) |].
    apply ebind_eok; eexists; split.
    { rewrite (app_nil_r (ptele tys)), (of_new_to _ _ _ Hnames).
      exact (proj2 (elab_cmds_iff fp cs O nil (sf_new nil tys) _ _ HO (Forall_nil _)
                      ltac:(apply sf_wf_new; rewrite Hnames; exact Hnd))
               (ex_intro _ F (conj HF eq_refl))). }
    cbn [us_frames us_imps map]. simpl_to.
    rewrite app_nil_r, rev_involutive, rev_involutive, (scmds_shape _ _ _ _ _ _ HF). reflexivity.
Qed.

(** Soundness: what the elaborator produces is what the specification says. *)
Corollary elaborate_core_sound : forall prg u, elaborate_core prg = eok u -> elab_spec prg u.
Proof. intros; apply elaborate_core_iff; assumption. Qed.

(** Completeness: whatever the specification relates, the elaborator produces. *)
Corollary elaborate_core_complete : forall prg u, elab_spec prg u -> elaborate_core prg = eok u.
Proof. intros; apply elaborate_core_iff; assumption. Qed.

(** The specification is functional. *)
Corollary elab_spec_functional : forall prg u1 u2, elab_spec prg u1 -> elab_spec prg u2 -> u1 = u2.
Proof.
  intros * H1 H2. apply elaborate_core_complete in H1, H2. rewrite H1 in H2. inversion H2; reflexivity.
Qed.

(** The elaborator fails exactly on the programs the specification relates
    to nothing. *)
Corollary elaborate_core_fails : forall prg,
    (exists e, elaborate_core prg = eerr e) <-> forall u, ~ elab_spec prg u.
Proof.
  intros; split.
  - intros (e & He) u Hs. apply elaborate_core_complete in Hs. congruence.
  - intros Hn. destruct (elaborate_core prg) as [u | e] eqn:E; [| eauto ].
    exfalso; apply (Hn u), elaborate_core_sound, E.
Qed.
