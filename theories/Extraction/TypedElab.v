(** * Deciding the Typed Fill

    The fill of [Core.TypedElab.Fill], computed.  Every command is filled
    part by part, its contexts computed as the relation reads them,
    inferring a type ([infer_at]) only where the relation does: at an
    access's head, at an unannotated [let], at an eliminator's scrutinee.
    The computed fill is the relation's ([fill_cmd_fn_sound]), and is found
    whenever the relation has one ([fill_cmd_fn_complete]). *)

From Stdlib Require Import List String PeanoNat Bool Lia.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import System Builtin Records.
From Mctt.Core.Syntactic.System Require Import Privacy Translations.
From Mctt.Core Require Import TypedElab.
From Mctt.Core.Syntactic.System.Global Require Import Paths.
From Mctt.Algorithmic.Typing Require Import Definitions Functional.
From Mctt.Extraction Require Import Lookup TypeCheckBase TypeCheck GlobalCheck MemberType MemberOrder Privacy.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Extraction Require Import IndDecl MdefGroup FastDesc LookupTwins.
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

  Lemma equiv_nfs_agree : forall Γ Ms Rs Ts, @nfs_agree (gc_mk Θ Ξ) Γ Ms Rs Ts -> @nfs_agree (gc_mk Θ' Ξ) Γ Ms Rs Ts.
  Proof. induction 1; [ apply (@nfs_agree_nil (gc_mk Θ' Ξ)) | eapply (@nfs_agree_cons (gc_mk Θ' Ξ)); eauto ]. Qed.

  Lemma equiv_alg_subtyping : forall Γ A B, @alg_subtyping (gc_mk Θ Ξ) Γ A B -> @alg_subtyping (gc_mk Θ' Ξ) Γ A B.
  Proof. intros * []; econstructor; eauto. Qed.

  (** Algorithmic typing reads the dependencies through their lookups
      alone. *)
  Lemma equiv_alg_all :
    (forall Γ A M, @alg_type_check (gc_mk Θ Ξ) Γ A M -> @alg_type_check (gc_mk Θ' Ξ) Γ A M) /\
    (forall Γ A M, @alg_type_infer (gc_mk Θ Ξ) Γ A M -> @alg_type_infer (gc_mk Θ' Ξ) Γ A M) /\
    (forall Γ Ψ, @alg_ext (gc_mk Θ Ξ) Γ Ψ -> @alg_ext (gc_mk Θ' Ξ) Γ Ψ) /\
    (forall Γ U, @alg_unit (gc_mk Θ Ξ) Γ U -> @alg_unit (gc_mk Θ' Ξ) Γ U) /\
    (forall Γ Φ Φx, @alg_body (gc_mk Θ Ξ) Γ Φ Φx -> @alg_body (gc_mk Θ' Ξ) Γ Φ Φx) /\
    (forall Γ H, @alg_modexp (gc_mk Θ Ξ) Γ H -> @alg_modexp (gc_mk Θ' Ξ) Γ H).
  Proof.
    destruct Hmd as (Hm1 & Hm2 & Hm3 & Hm4 & Hm5).
    apply (@alg_type_mut_ind (gc_mk Θ Ξ)); intros; cbn [gc_deps gc_stack] in *;
      try solve [ econstructor; eauto 6 using equiv_nfs_agree, equiv_alg_subtyping ].
    (* an eliminator: at the groups it reads *)
    eapply alg_type_infer_elim with (D := D) (Dq := Dq) (Mm := Mm) (Mk := Mk) (bm := bm) (i := i) (p := p) (pc := pc) (k := k);
      try eassumption; eauto using equiv_nfs_agree.
    intros * Hj Hb HZ; destruct (a2 _ _ _ _ Hj Hb HZ) as (W & HW1 & HW2); exists W; split; auto.
  Qed.

  Lemma equiv_glob_ok : forall H y, glob_ok Θ Ξ H y -> glob_ok Θ' Ξ H y.
  Proof. intros * Hok qd Hd; apply Hok; exact (mdecl_dsub _ _ _ (proj2 He) _ _ _ _ Hd). Qed.

  Lemma equiv_sel_ok : forall op y, sel_ok Θ Ξ op y -> sel_ok Θ' Ξ op y.
  Proof. intros [p |] y; cbn; [ apply equiv_glob_ok | auto ]. Qed.

  Let Hmd' := gds_equiv_mdenote_all Θ' Θ Ξ (gds_equiv_sym _ _ He).

  Hypothesis Hg' : ⊢ᵍ Θ' ⍮ Ξ.

  (** The fill reads the dependencies through lookups, inference, the
      eliminator readings, the literals and privacy, all alike. *)
  Lemma equiv_fill_all :
    (forall Γ M M', fill_exp Θ Ξ B Γ M M' -> fill_exp Θ' Ξ B Γ M M') /\
    (forall Γ fs fs', fill_fvals Θ Ξ B Γ fs fs' -> fill_fvals Θ' Ξ B Γ fs fs') /\
    (forall Γ p D Us As j Bks Bks', fill_blocks Θ Ξ B Γ p D Us As j Bks Bks' -> fill_blocks Θ' Ξ B Γ p D Us As j Bks Bks') /\
    (forall Γ p D Mj Us As Bs Bs', fill_brs Θ Ξ B Γ p D Mj Us As Bs Bs' -> fill_brs Θ' Ξ B Γ p D Mj Us As Bs Bs') /\
    (forall Γ oM oM', fill_oexp Θ Ξ B Γ oM oM' -> fill_oexp Θ' Ξ B Γ oM oM') /\
    (forall Γ H r, fill_read Θ Ξ B Γ H r -> fill_read Θ' Ξ B Γ H r) /\
    (forall Γ H H' op, fill_mod Θ Ξ B Γ H H' op -> fill_mod Θ' Ξ B Γ H H' op) /\
    (forall Γ U U', fill_unit Θ Ξ B Γ U U' -> fill_unit Θ' Ξ B Γ U U') /\
    (forall Γ D D', fill_def Θ Ξ B Γ D D' -> fill_def Θ' Ξ B Γ D D') /\
    (forall Γ Δ Δ', fill_tele Θ Ξ B Γ Δ Δ' -> fill_tele Θ' Ξ B Γ Δ Δ') /\
    (forall Γ Φ Φ', fill_body Θ Ξ B Γ Φ Φ' -> fill_body Θ' Ξ B Γ Φ Φ').
  Proof.
    destruct Hmd as (Hm1 & _ & _ & Hm4 & _); destruct Hmd' as (Hm1' & _ & _ & _ & _).
    pose proof (proj1 (proj2 equiv_alg_all)) as Hinf.
    apply fill_mut_ind; intros; try solve [ econstructor; eauto using equiv_sel_ok, equiv_ctx, Forall_impl ].
    (* a member that is no term: no term along the equivalence either *)
    eapply fill_read_mem_module; [ exact H0 | apply equiv_sel_ok; exact s | intros A oM Hm; exact (n A oM (Hm1' _ _ _ Hm)) ].
  Qed.
End AlgEquiv.

(** The fill of a command, and of a unit's parameters, along an
    equivalence of the dependencies. *)
Lemma equiv_fill_cmd : forall Θ Θ' Ξ B c c', gds_equiv Θ Θ' -> ⊢ᵍ Θ' ⍮ Ξ -> fill_cmd Θ Ξ B c c' -> fill_cmd Θ' Ξ B c c'.
Proof.
  intros * He Hg' H.
  pose proof (equiv_fill_all _ _ _ B He Hg') as (Fe & _ & _ & Fb & Fo & _ & Fm & _ & _ & Ft & _).
  destruct H as [ | | | | | | | | | pv R R' [Hu Hr Hm] | b pv Δ Δ' f0 fs fh0 fsh f0' fs' pq m0 Ps D Us ms HΔ Hh Hgp Hb | |].
  11:{ (* a mutual definition: its heads, its group, its bodies *)
      eapply fill_cmd_mdef; [ exact (Ft _ _ _ HΔ) | | exact (equiv_mdef_group _ _ _ _ _ _ _ _ _ _ _ _ He Hg' Hgp) | ].
      - eapply Forall2_impl; [| exact Hh ]; intros f f' [En Ep Es Er Ec]; constructor; eauto.
      - eapply Forall2_impl; [| exact Hb ]; intros fm f' [En Ep Es Hm' Hr' Hc]; constructor; eauto. }
  10:{ (* a group: each part *)
      apply fill_cmd_ind_decl; constructor; [ exact (Ft _ _ _ Hu) | exact Hr |].
      eapply Forall2_impl; [| exact Hm ]; intros Mr Mr' [En Hn Hs Hc]; constructor; eauto.
      eapply Forall2_impl; [| exact Hc ]; intros rc rc' [Ef [Hna Ht]]; split; [ exact Ef | constructor; eauto ]. }
  all: try (econstructor; eauto using Forall_impl, equiv_sel_ok; fail).
  (* a record declaration: its fields *)
  econstructor; eauto.
  match goal with H1 : fill_fields _ _ _ _ _ _ |- _ => clear - Fe H1; induction H1; constructor; auto end.
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
| fill_failure_literal : lerr -> fill_failure
(** An eliminator's scrutinee, filled, in its context: its type, if
    inferred, is not an inductive type *)
| fill_failure_elim_scrutinee : ctx -> exp -> option nf -> fill_failure
(** An eliminator, in its context, whose scrutinee's type is the member
    [k] of the group [pc] at the arguments [Rs], and no reading of which
    fits its blocks: [pc], [k], [Rs], the block marked [at], the blocks
    and the filled scrutinee *)
| fill_failure_elim_none : ctx -> qname -> nat -> list nf -> nat -> list eblock -> exp -> fill_failure
(** An eliminator, in its context, several readings of which fit its
    blocks: the eliminator, its scrutinee filled, and the readings, each
    its group and its uniform parameters *)
| fill_failure_elim_ambiguous : ctx -> exp -> list (qname * list exp) -> fill_failure
(** A local body, in its context, whose entries filled so far have no
    expansion: an open among them generates nothing *)
| fill_failure_body : ctx -> gmod -> fill_failure
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

(** ** A Module's and a Record's Fills

    The fill of a module declaration is its telescope's, that of a record
    declaration its telescope's, sort's and fields'.  At any context. *)

Lemma fill_cmd_mod_params : forall Θ Ξ B x pv Δ Δ' cs,
    fill_params Θ Ξ B Δ Δ' -> fill_cmd Θ Ξ B (core_cmd_mod x pv Δ cs) (core_cmd_mod x pv Δ' cs).
Proof. intros * Ht; apply fill_cmd_mod; exact Ht. Qed.

Lemma fill_cmd_mod_inv : forall Θ Ξ B x pv Δ cs c',
    fill_cmd Θ Ξ B (core_cmd_mod x pv Δ cs) c' -> exists Δ', c' = core_cmd_mod x pv Δ' cs /\ fill_params Θ Ξ B Δ Δ'.
Proof. intros * H; inversion H; subst; eexists; split; [ reflexivity | assumption ]. Qed.

(** What fills to a module is a module with the same name and body, its
    parameters filled. *)
Lemma fill_cmd_to_mod : forall Θ Ξ B c x pv Δ' cs,
    fill_cmd Θ Ξ B c (core_cmd_mod x pv Δ' cs) -> exists Δ, c = core_cmd_mod x pv Δ cs /\ fill_params Θ Ξ B Δ Δ'.
Proof. intros * H; inversion H; subst; eexists; split; [ reflexivity | assumption ]. Qed.

(** What fills to a record declaration is one with the same name and
    with-area. *)
Lemma fill_cmd_to_record : forall Θ Ξ B c x pv Δ' Srt' fs' cs,
    fill_cmd Θ Ξ B c (core_cmd_record x pv Δ' Srt' fs' cs) -> exists Δ Srt fs, c = core_cmd_record x pv Δ Srt fs cs.
Proof. intros * H; inversion H; subst; eauto. Qed.

Section Decide.
  (** The fast context the typed checks look names up in
      ([Extraction.Lookup]); the fill decided is at the Core context it
      stands for. *)
  Variable F : FCtx.
  #[local] Hint Extern 0 GCtx => exact (fc_gctx F) : typeclass_instances.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  Variable B : builtins.
  Hypothesis Hg : ⊢ᵍ Θ ⍮ Ξ.

  (** ** What the Fill Reads *)

  (** The type a term infers in a well-formed context. *)
  Definition infer_at (Γ : ctx) (M : exp) : option nf :=
    match check_ctx F Hg Γ with
    | left HΓ =>
        match type_infer F Γ HΓ M (type_infer_order_all M) with
        | inleft (exist _ W _) => Some W
        | inright _ => None
        end
    | right _ => None
    end.

  (** Whether the binder [k] of [Γ] holds a term. *)
  Definition term_binder_b (Γ : ctx) (k : nat) : bool :=
    match List.nth_error Γ k with
    | Some (ce_ass _) | Some (ce_def _ _) => true
    | _ => false
    end.

  (** Whether the member [y] of [H] is a term. *)
  Definition member_term_b (Γ : ctx) (H : modexp) (y : string) : bool :=
    match mdenote_dec F Hg Γ (me_mem H y) with
    | inleft (exist _ (fds_term _ _) _) => true
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

  (** A module expression, in module position, read as [r]: the module it
      is, with the record it is the module of a value of, if it has a term
      at its head.  [y] names what is selected from it, for the error. *)
  Definition fill_mod_of (Γ : ctx) (y : string) (r : fill_result module_read) : fill_result (modexp * option qname)%type :=
    match r with
    | fill_error e => fill_error e
    | fill_ok (read_module H') => fill_ok (H', None)
    | fill_ok (read_term M) =>
        match infer_at Γ M with
        | Some (nf_record p Rs) => fill_ok (record_value_module p Rs M, Some p)
        | Some W => fill_error (fill_failure_not_record y Γ M W)
        | None => fill_error (fill_failure_no_type y Γ M)
        end
    end.

  (** ** The Fill, Computed *)

  Fixpoint fill_exp_fn (Γ : ctx) (M : exp) {struct M} : fill_result exp :=
    match M with
    | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False
    | a_ind _ _ | a_con _ _ _ | a_var _ | a_record _ => fill_ok M
    | a_nlit n =>
        match nat_view_f F B with
        | Some (p, z, s) => fill_ok (nat_chain p z s n)
        | None => fill_error (fill_failure_literal (le_num n))
        end
    | a_ntok =>
        match nat_view_f F B with
        | Some (p, _, _) => fill_ok (a_ind p 0)
        | None => fill_error (fill_failure_literal le_tok)
        end
    | a_univ M0 => let%a M' := fill_exp_fn Γ M0 in fill_ok (a_univ M')
    | a_succl M0 => let%a M' := fill_exp_fn Γ M0 in fill_ok (a_succl M')
    | a_maxl M0 N0 =>
        let%a M' := fill_exp_fn Γ M0 in
        let%a N' := fill_exp_fn Γ N0 in
        fill_ok (a_maxl M' N')
    | a_exfalso A M0 =>
        let%a A' := fill_exp_fn (ce_ass a_False :: Γ) A in
        let%a M' := fill_exp_fn Γ M0 in
        fill_ok (a_exfalso A' M')
    | a_pi A B0 =>
        let%a A' := fill_exp_fn Γ A in
        let%a B' := fill_exp_fn (ce_ass A' :: Γ) B0 in
        fill_ok (a_pi A' B')
    | a_fn A M0 =>
        let%a A' := fill_exp_fn Γ A in
        let%a M' := fill_exp_fn (ce_ass A' :: Γ) M0 in
        fill_ok (a_fn A' M')
    | a_app M0 N0 =>
        let%a M' := fill_exp_fn Γ M0 in
        let%a N' := fill_exp_fn Γ N0 in
        fill_ok (a_app M' N')
    | a_let (b_def (Some A) M0) B0 =>
        let%a A' := fill_exp_fn Γ A in
        let%a M' := fill_exp_fn Γ M0 in
        let%a B' := fill_exp_fn (ce_def A' M' :: Γ) B0 in
        fill_ok (a_let (b_def (Some A') M') B')
    | a_let (b_def None M0) B0 =>
        let%a M' := fill_exp_fn Γ M0 in
        match infer_at Γ M' with
        | Some W =>
            let%a B' := fill_exp_fn (ce_def (nf_to_exp W) M' :: Γ) B0 in
            fill_ok (a_let (b_def None M') B')
        | None => fill_error (fill_failure_message "the definition of an unannotated let infers no type")
        end
    | a_let (b_mod U) B0 =>
        let%a U' := fill_unit_fn Γ U in
        let%a B' := fill_exp_fn (ce_mod U' :: Γ) B0 in
        fill_ok (a_let (b_mod U') B')
    | a_mem H x =>
        let%a r := fill_mod_of Γ x (fill_read_fn Γ H) in
        match sel_check (snd r) x with
        | Some (qd, y) => fill_error (fill_failure_private qd y)
        | None => fill_ok (a_mem (fst r) x)
        end
    | a_tuple T fs =>
        let%a T' := fill_exp_fn Γ T in
        let%a fs' :=
          (fix fields (fs : list (string * exp)) : fill_result (list (string * exp)) :=
             match fs with
             | nil => fill_ok nil
             | (f, N) :: fs0 =>
                 let%a N' := fill_exp_fn Γ N in
                 let%a fs0' := fields fs0 in
                 fill_ok ((f, N') :: fs0')
             end) fs in
        fill_ok (a_tuple T' fs')
    | a_proj f M0 => let%a M' := fill_exp_fn Γ M0 in fill_ok (a_proj f M')
    | a_elim None nil m Bks M0 =>
        let%a M' := fill_exp_fn Γ M0 in
        match infer_at Γ M' with
        | Some (nf_indty pc k Rs) =>
            match elim_target_f F pc k Rs m Bks with
            | elim_target_one p Us =>
                match fc_ind F p with
                | None => fill_error (fill_failure_message "internal error: an eliminator of no group")
                | Some D =>
                    (** first each block's annotation and motive, at the
                        uniform parameters *)
                    let%a hs :=
                      (fix heads (j : nat) (Bks : list eblock) : fill_result (list (option exp * exp)) :=
                         match Bks with
                         | nil => fill_ok nil
                         | eb_mk nm oZ A Bs :: Bks0 =>
                             match ind_member D j with
                             | None => fill_error (fill_failure_message "an eliminator with more blocks than its group has members")
                             | Some Mj =>
                                 if Nat.eqb nm (S (im_nn Mj)) then
                                   let%a oZ' :=
                                     match oZ with
                                     | None => fill_ok None
                                     | Some Z =>
                                         let%a Z' := fill_exp_fn (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z in
                                         fill_ok (Some Z')
                                     end in
                                   let%a A' := fill_exp_fn (elim_mctx p D j Mj Us ++ Γ) A in
                                   let%a hs0 := heads (S j) Bks0 in
                                   fill_ok ((oZ', A') :: hs0)
                                 else fill_error (fill_failure_message "a block of an eliminator binds the wrong number of variables")
                             end
                         end) 0 Bks in
                    (** then the branches, at the filled motives of all
                        the blocks *)
                    let As := List.map snd hs in
                    let%a Bks' :=
                      (fix blocks (j : nat) (Bks : list eblock) (rest : list (option exp * exp)) : fill_result (list eblock) :=
                         match Bks, rest with
                         | nil, _ => fill_ok nil
                         | eb_mk nm _ _ Bs :: Bks0, (oZ', A') :: rest0 =>
                             match ind_member D j with
                             | None => fill_error (fill_failure_message "an eliminator with more blocks than its group has members")
                             | Some Mj =>
                                 let%a Bs' :=
                                   (fix brs (Bs : list (string * nat * exp)) : fill_result (list (string * nat * exp)) :=
                                      match Bs with
                                      | nil => fill_ok nil
                                      | (c, n, B0) :: Bs0 =>
                                          match ind_con Mj c with
                                          | None => fill_error (fill_failure_message ("a branch of no constructor " ++ c))
                                          | Some gs =>
                                              if Nat.eqb n (im_nn Mj + List.length gs + cargs_nrec D gs) then
                                                let%a B' := fill_exp_fn (elim_bctx p D Mj gs As Us ++ Γ) B0 in
                                                let%a Bs0' := brs Bs0 in
                                                fill_ok ((c, n, B') :: Bs0')
                                              else fill_error (fill_failure_message ("the branch of " ++ c ++ " binds the wrong number of variables"))
                                          end
                                      end) Bs in
                                 let%a Bks0' := blocks (S j) Bks0 rest0 in
                                 fill_ok (eb_mk nm oZ' A' Bs' :: Bks0')
                             end
                         | _ :: _, nil => fill_error (fill_failure_message "internal error: a block without its motive")
                         end) 0 Bks hs in
                    fill_ok (a_elim (Some p) Us m Bks' M')
                end
            | elim_target_ambiguous rs => fill_error (fill_failure_elim_ambiguous Γ (a_elim None nil m Bks M') rs)
            | elim_target_none => fill_error (fill_failure_elim_none Γ pc k Rs m Bks M')
            end
        | W => fill_error (fill_failure_elim_scrutinee Γ M' W)
        end
    | a_elim _ _ _ _ _ => fill_error (fill_failure_message "an eliminator written with its group")
    end

  with fill_read_fn (Γ : ctx) (H : modexp) {struct H} : fill_result module_read :=
    match H with
    | me_unit fp => fill_ok (read_module (me_unit fp))
    | me_var k => if term_binder_b Γ k then fill_ok (read_term (a_var k)) else fill_ok (read_module (me_var k))
    | me_lit U => let%a U' := fill_unit_fn Γ U in fill_ok (read_module (me_lit U'))
    | me_mem H0 y =>
        let%a r := fill_mod_of Γ y (fill_read_fn Γ H0) in
        match sel_check (snd r) y with
        | Some (qd, x) => fill_error (fill_failure_private qd x)
        | None =>
            if member_term_b Γ (fst r) y then fill_ok (read_term (a_mem (fst r) y))
            else fill_ok (read_module (me_mem (fst r) y))
        end
    | me_app H0 N =>
        let%a r := fill_read_fn Γ H0 in
        let%a N' := fill_exp_fn Γ N in
        match r with
        | read_module H' => fill_ok (read_module (me_app H' N'))
        | read_term M => fill_ok (read_term (a_app M N'))
        end
    end

  with fill_unit_fn (Γ : ctx) (U : gunit) {struct U} : fill_result gunit :=
    match U with
    | gu_mk Δ D =>
        let%a Δ' :=
          (fix tele (Δ : list centry) : fill_result ctx :=
             match Δ with
             | nil => fill_ok nil
             | e :: Δ0 =>
                 let%a Δ0' := tele Δ0 in
                 let%a e' := fill_centry_fn (Δ0' ++ Γ) e in
                 fill_ok (e' :: Δ0')
             end) Δ in
        let%a D' := fill_def_fn (Δ' ++ Γ) D in
        fill_ok (gu_mk Δ' D')
    end

  with fill_def_fn (Γ : ctx) (D : moddef) {struct D} : fill_result moddef :=
    match D with
    | md_alias E => let%a r := fill_mod_of Γ "" (fill_read_fn Γ E) in fill_ok (md_alias (fst r))
    | md_body sm Φ => let%a Φ' := fill_body_fn Γ Φ in fill_ok (md_body sm Φ')
    end

  with fill_body_fn (Γ : ctx) (Φ : gmod) {struct Φ} : fill_result gmod :=
    match Φ with
    | gm_nil => fill_ok gm_nil
    | gm_ext Φ0 x E =>
        let%a Φ0' := fill_body_fn Γ Φ0 in
        let%a Φx := body_xp_fn Γ Φ0' in
        match E with
        | ge_def b pv A oM =>
            let%a A' := fill_exp_fn (body_ctx Φx ++ Γ) A in
            let%a oM' :=
              match oM with
              | None => fill_ok None
              | Some M => let%a M' := fill_exp_fn (body_ctx Φx ++ Γ) M in fill_ok (Some M')
              end in
            fill_ok (gm_ext Φ0' x (ge_def b pv A' oM'))
        | ge_mod pv U =>
            let%a U' := fill_unit_fn (body_ctx Φx ++ Γ) U in
            fill_ok (gm_ext Φ0' x (ge_mod pv U'))
        | ge_def_mod pv A M U =>
            let%a A' := fill_exp_fn (body_ctx Φx ++ Γ) A in
            let%a M' := fill_exp_fn (body_ctx Φx ++ Γ) M in
            let%a U' := fill_unit_fn (body_ctx Φx ++ Γ) U in
            fill_ok (gm_ext Φ0' x (ge_def_mod pv A' M' U'))
        | _ => fill_error (fill_failure_message "an entry no local body is written with")
        end
    | gm_open Φ0 H its =>
        let%a Φ0' := fill_body_fn Γ Φ0 in
        let%a Φx := body_xp_fn Γ Φ0' in
        let%a r := fill_mod_of (body_ctx Φx ++ Γ) "" (fill_read_fn (body_ctx Φx ++ Γ) H) in
        let%a _ := sels_check (snd r) (items_members its) in
        fill_ok (gm_open Φ0' (fst r) its)
    end

  with fill_centry_fn (Γ : ctx) (e : centry) {struct e} : fill_result centry :=
    match e with
    | ce_ass A => let%a A' := fill_exp_fn Γ A in fill_ok (ce_ass A')
    | ce_def A M =>
        let%a A' := fill_exp_fn Γ A in
        let%a M' := fill_exp_fn Γ M in
        fill_ok (ce_def A' M')
    | ce_mod U => let%a U' := fill_unit_fn Γ U in fill_ok (ce_mod U')
    | ce_dm A M U =>
        let%a A' := fill_exp_fn Γ A in
        let%a M' := fill_exp_fn Γ M in
        let%a U' := fill_unit_fn Γ U in
        fill_ok (ce_dm A' M' U')
    end.

  (** A module expression in module position. *)
  Definition fill_mod_fn (Γ : ctx) (y : string) (H : modexp) : fill_result (modexp * option qname)%type :=
    fill_mod_of Γ y (fill_read_fn Γ H).

  (** A telescope, innermost first, each entry over the filled ones after
      it. *)
  Fixpoint fill_tele_fn (Γ : ctx) (Δ : ctx) : fill_result ctx :=
    match Δ with
    | nil => fill_ok nil
    | e :: Δ0 =>
        let%a Δ0' := fill_tele_fn Γ Δ0 in
        let%a e' := fill_centry_fn (Δ0' ++ Γ) e in
        fill_ok (e' :: Δ0')
    end.

  (** A record's fields, each over the filled ones before it. *)
  Fixpoint fill_fields_fn (Γ : ctx) (fs : list (string * typ)) : fill_result (list (string * typ)) :=
    match fs with
    | nil => fill_ok nil
    | (f, T) :: fs0 =>
        let%a T' := fill_exp_fn Γ T in
        let%a fs0' := fill_fields_fn (ce_ass T' :: Γ) fs0 in
        fill_ok ((f, T') :: fs0')
    end.

  (** A term that may be absent. *)
  Definition fill_oexp_fn (Γ : ctx) (oM : option exp) : fill_result (option exp) :=
    match oM with
    | None => fill_ok None
    | Some M => let%a M' := fill_exp_fn Γ M in fill_ok (Some M')
    end.

  (** ** The Loops of the Fill

      The loops [fill_exp_fn] runs over the lists inside a term, named, so
      that what they compute can be stated. *)

  (** The fields of a record value. *)
  Definition fvals_fn (Γ : ctx) :=
    fix fields (fs : list (string * exp)) : fill_result (list (string * exp)) :=
      match fs with
      | nil => fill_ok nil
      | (f, N) :: fs0 =>
          let%a N' := fill_exp_fn Γ N in
          let%a fs0' := fields fs0 in
          fill_ok ((f, N') :: fs0')
      end.

  (** Each block's annotation and motive. *)
  Definition heads_fn (Γ : ctx) (p : qname) (D : ind_decl) (Us : list exp) :=
    fix heads (j : nat) (Bks : list eblock) : fill_result (list (option exp * exp)) :=
      match Bks with
      | nil => fill_ok nil
      | eb_mk nm oZ A Bs :: Bks0 =>
          match ind_member D j with
          | None => fill_error (fill_failure_message "an eliminator with more blocks than its group has members")
          | Some Mj =>
              if Nat.eqb nm (S (im_nn Mj)) then
                let%a oZ' :=
                  match oZ with
                  | None => fill_ok None
                  | Some Z =>
                      let%a Z' := fill_exp_fn (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) Z in
                      fill_ok (Some Z')
                  end in
                let%a A' := fill_exp_fn (elim_mctx p D j Mj Us ++ Γ) A in
                let%a hs0 := heads (S j) Bks0 in
                fill_ok ((oZ', A') :: hs0)
              else fill_error (fill_failure_message "a block of an eliminator binds the wrong number of variables")
          end
      end.

  (** A block's branches, at the motives [As]. *)
  Definition brs_fn (Γ : ctx) (p : qname) (D : ind_decl) (Mj : imember) (As Us : list exp) :=
    fix brs (Bs : list (string * nat * exp)) : fill_result (list (string * nat * exp)) :=
      match Bs with
      | nil => fill_ok nil
      | (c, n, B0) :: Bs0 =>
          match ind_con Mj c with
          | None => fill_error (fill_failure_message ("a branch of no constructor " ++ c))
          | Some gs =>
              if Nat.eqb n (im_nn Mj + List.length gs + cargs_nrec D gs) then
                let%a B' := fill_exp_fn (elim_bctx p D Mj gs As Us ++ Γ) B0 in
                let%a Bs0' := brs Bs0 in
                fill_ok ((c, n, B') :: Bs0')
              else fill_error (fill_failure_message ("the branch of " ++ c ++ " binds the wrong number of variables"))
          end
      end.

  (** The blocks, their annotations and motives filled as [hs], and the
      motives of all of them [As]. *)
  Definition blocks_fn (Γ : ctx) (p : qname) (D : ind_decl) (As Us : list exp) :=
    fix blocks (j : nat) (Bks : list eblock) (rest : list (option exp * exp)) : fill_result (list eblock) :=
      match Bks, rest with
      | nil, _ => fill_ok nil
      | eb_mk nm _ _ Bs :: Bks0, (oZ', A') :: rest0 =>
          match ind_member D j with
          | None => fill_error (fill_failure_message "an eliminator with more blocks than its group has members")
          | Some Mj =>
              let%a Bs' := brs_fn Γ p D Mj As Us Bs in
              let%a Bks0' := blocks (S j) Bks0 rest0 in
              fill_ok (eb_mk nm oZ' A' Bs' :: Bks0')
          end
      | _ :: _, nil => fill_error (fill_failure_message "internal error: a block without its motive")
      end.

  (** An eliminator as written, its scrutinee filled to [M'] in [Γ]: the
      one reading that fits its blocks, then its blocks at it, their
      annotations and motives first, then their branches at the filled
      motives. *)
  Definition elim_fill_fn (Γ : ctx) (m : nat) (Bks : list eblock) (M' : exp) : fill_result exp :=
    match infer_at Γ M' with
    | Some (nf_indty pc k Rs) =>
        match elim_target_f F pc k Rs m Bks with
        | elim_target_one p Us =>
            match fc_ind F p with
            | None => fill_error (fill_failure_message "internal error: an eliminator of no group")
            | Some D =>
                let%a hs := heads_fn Γ p D Us 0 Bks in
                let As := List.map snd hs in
                let%a Bks' := blocks_fn Γ p D As Us 0 Bks hs in
                fill_ok (a_elim (Some p) Us m Bks' M')
            end
        | elim_target_ambiguous rs => fill_error (fill_failure_elim_ambiguous Γ (a_elim None nil m Bks M') rs)
        | elim_target_none => fill_error (fill_failure_elim_none Γ pc k Rs m Bks M')
        end
    | W => fill_error (fill_failure_elim_scrutinee Γ M' W)
    end.

  (** ** Commands, Filled *)

  (** The heads of a mutual definition's functions over [Γ]: each one's
      parameters, then its scrutinee over them. *)
  Fixpoint fill_rfun_heads_fn (Γ : ctx) (fs : list raw_fun) : fill_result (list raw_fun) :=
    match fs with
    | nil => fill_ok nil
    | f :: fs0 =>
        let%a ys' := fill_tele_fn Γ (raw_fun_nparams f) in
        let%a Z' := fill_exp_fn (ys' ++ Γ) (raw_fun_scrut f) in
        let%a fs0' := fill_rfun_heads_fn Γ fs0 in
        fill_ok (mk_rfun (raw_fun_name f) ys' Z' (raw_fun_res f) (raw_fun_clauses f) :: fs0')
    end.

  (** The results of functions, each of its member, in the motive's
      context. *)
  Fixpoint fill_rfun_results_fn (Γ : ctx) (pq : qname) (D : ind_decl) (Us : list exp) (fms : list (raw_fun * nat)) :
      fill_result (list raw_fun) :=
    match fms with
    | nil => fill_ok nil
    | (f, m) :: fms0 =>
        match ind_member D m with
        | None => fill_error (fill_failure_message "internal error: a function of no member")
        | Some Mm =>
            let%a A' := fill_exp_fn (elim_mctx pq D m Mm Us ++ Γ) (raw_fun_res f) in
            let%a fs0' := fill_rfun_results_fn Γ pq D Us fms0 in
            fill_ok (mk_rfun (raw_fun_name f) (raw_fun_nparams f) (raw_fun_scrut f) A' (raw_fun_clauses f) :: fs0')
        end
    end.

  (** The clauses of functions, each of its member, in their branches'
      contexts at the motives [As]. *)
  Fixpoint fill_rfun_clauses_fn (Γ : ctx) (pq : qname) (D : ind_decl) (Us As : list exp) (fms : list (raw_fun * nat)) :
      fill_result (list raw_fun) :=
    match fms with
    | nil => fill_ok nil
    | (f, m) :: fms0 =>
        match ind_member D m with
        | None => fill_error (fill_failure_message "internal error: a function of no member")
        | Some Mm =>
            let%a Bs' := brs_fn Γ pq D Mm As Us (raw_fun_clauses f) in
            let%a fs0' := fill_rfun_clauses_fn Γ pq D Us As fms0 in
            fill_ok (mk_rfun (raw_fun_name f) (raw_fun_nparams f) (raw_fun_scrut f) (raw_fun_res f) Bs' :: fs0')
        end
    end.

  (** A mutual definition's functions over [Γ], their heads filled as
      [hs]: their group, then their results, then their clauses at the
      motives of the blocks of the functions with their results filled. *)
  Definition fill_rfun_bodies_fn (Γ : ctx) (Δ' : ctx) (hs : list raw_fun) : fill_result (list raw_fun) :=
    match hs with
    | nil => fill_error (fill_failure_message "a mutual definition with no function")
    | h0 :: hs0 =>
        match mdef_group_dec F Hg Δ' h0 hs0 with
        | inr e => fill_error (fill_failure_mdef_group e)
        | inl (exist _ (pq, m0, Ps, D, Us, ms) _) =>
            let%a rs := fill_rfun_results_fn Γ pq D Us (List.combine hs ms) in
            fill_rfun_clauses_fn Γ pq D Us (blocks_motives (mdef_blocks 0 (ind_nblk D) rs ms))
              (List.combine rs ms)
        end
    end.

  (** Arguments named [ys], outermost first, from a telescope of
      assumptions [es], outermost first. *)
  Fixpoint zip_ass (ys : list string) (es : list centry) : option (list (string * exp)) :=
    match ys, es with
    | nil, nil => Some nil
    | y :: ys0, ce_ass A :: es0 => option_map (cons (y, A)) (zip_ass ys0 es0)
    | _, _ => None
    end.

  (** A constructor's arguments over [Γ], filled as a telescope, their
      names kept. *)
  Definition fill_raw_args_fn (Γ : ctx) (args : list (string * exp)) : fill_result (list (string * exp)) :=
    let%a Δ' := fill_tele_fn Γ (rtele args) in
    match zip_ass (List.map fst args) (List.rev Δ') with
    | Some args' => fill_ok args'
    | None => fill_error (fill_failure_message "internal error: a constructor's arguments filled to no arguments")
    end.

  (** Constructors' arguments over [Γ], their names kept. *)
  Fixpoint fill_raw_cons_fn (Γ : ctx) (cs : list (string * list (string * exp))) :
      fill_result (list (string * list (string * exp))) :=
    match cs with
    | nil => fill_ok nil
    | (c, args) :: cs0 =>
        let%a args' := fill_raw_args_fn Γ args in
        let%a cs0' := fill_raw_cons_fn Γ cs0 in
        fill_ok ((c, args') :: cs0')
    end.

  (** Declared members' parameters and sorts over [Γ], the uniform
      parameters and the frames'. *)
  Fixpoint fill_raw_heads_fn (Γ : ctx) (ms : list raw_member) : fill_result (list raw_member) :=
    match ms with
    | nil => fill_ok nil
    | Mr :: ms0 =>
        let%a ys' := fill_tele_fn Γ (raw_member_nparams Mr) in
        let%a S' := fill_exp_fn Γ (raw_member_sort Mr) in
        let%a ms0' := fill_raw_heads_fn Γ ms0 in
        fill_ok (mk_rmem (raw_member_name Mr) ys' S' (raw_member_cons Mr) :: ms0')
    end.

  (** Declared members' constructors, each over the member's context in
      the group [Rh], whose parameters and sorts are filled. *)
  (** The context of a member's constructors ([rm_pctx]), over the frames'
      parameters [Γt] *)
  Definition rm_pctx_at (Γt : ctx) (R : raw_decl) (Mr : raw_member) : ctx :=
    tele_wk (raw_member_nparams Mr ++ raw_decl_uparams R) (wk_shiftn (rd_n R)) ++ rd_selfs R ++ Γt.

  (** The fills below of a command and of what it is made of, over the
      frames' parameters [Γt]: the extracted checker computes them over
      the fast telescope of the frames ([fc_tele]), the lemmas read them
      over the Core one ([gs_tele]), which it is ([fc_tele_ok]). *)
  Fixpoint fill_raw_bodies_at (Γt : ctx) (Rh : raw_decl) (ms : list raw_member) : fill_result (list raw_member) :=
    match ms with
    | nil => fill_ok nil
    | Mr :: ms0 =>
        let%a cs' := fill_raw_cons_fn (rm_pctx_at Γt Rh Mr) (raw_member_cons Mr) in
        let%a ms0' := fill_raw_bodies_at Γt Rh ms0 in
        fill_ok (mk_rmem (raw_member_name Mr) (raw_member_nparams Mr) (raw_member_sort Mr) cs' :: ms0')
    end.

  (** A group as written, filled: its uniform parameters, its members'
      parameters and sorts, then their constructors' arguments in the
      group with those filled. *)
  Definition fill_raw_decl_at (Γt : ctx) (R : raw_decl) : fill_result raw_decl :=
    let%a ups' := fill_tele_fn Γt (raw_decl_uparams R) in
    let%a hs := fill_raw_heads_fn (ups' ++ Γt) (raw_decl_members R) in
    let%a ms' := fill_raw_bodies_at Γt (mk_raw ups' hs (raw_decl_rec_field R)) hs in
    fill_ok (mk_raw ups' ms' (raw_decl_rec_field R)).

  (** A command filled, part by part. *)
  Definition fill_cmd_at (Γt : ctx) (c : core_cmd) : fill_result core_cmd :=
    match c with
    | core_cmd_def x b pv A oM =>
        let%a A' := fill_exp_fn Γt A in
        let%a oM' := fill_oexp_fn Γt oM in
        fill_ok (core_cmd_def x b pv A' oM')
    | core_cmd_mod x pv Δ cs => let%a Δ' := fill_tele_fn Γt Δ in fill_ok (core_cmd_mod x pv Δ' cs)
    | core_cmd_alias x pv Δ E =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a r := fill_mod_fn (Δ' ++ Γt) "" E in
        fill_ok (core_cmd_alias x pv Δ' (fst r))
    | core_cmd_inductive_alias x pv Δ E =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a r := fill_mod_fn (Δ' ++ Γt) "" E in
        match snd r with
        | None => fill_ok (core_cmd_inductive_alias x pv Δ' (fst r))
        | Some _ => fill_error (fill_failure_message ("the inductive alias " ++ x ++ " names a record value, not an inductive type"))
        end
    | core_cmd_record_alias x pv Δ E =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a r := fill_mod_fn (Δ' ++ Γt) "" E in
        match snd r with
        | None => fill_ok (core_cmd_record_alias x pv Δ' (fst r))
        | Some _ => fill_error (fill_failure_message ("the record alias " ++ x ++ " names a record value, not a record type"))
        end
    | core_cmd_open E its =>
        let%a r := fill_mod_fn Γt "" E in
        let%a _ := sels_check (snd r) (items_members its) in
        fill_ok (core_cmd_open (fst r) its)
    | core_cmd_builtin k E =>
        let%a r := fill_mod_fn Γt "" E in
        match snd r with
        | None => fill_ok (core_cmd_builtin k (fst r))
        | Some _ => fill_error (fill_failure_message "a builtin binding names a record value, not an inductive type")
        end
    | core_cmd_eval M oA =>
        let%a M' := fill_exp_fn Γt M in
        let%a oA' := fill_oexp_fn Γt oA in
        fill_ok (core_cmd_eval M' oA')
    | core_cmd_record x pv Δ Srt fs cs =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a Srt' := fill_exp_fn (Δ' ++ Γt) Srt in
        let%a fs' := fill_fields_fn (Δ' ++ Γt) fs in
        fill_ok (core_cmd_record x pv Δ' Srt' fs' cs)
    | core_cmd_mdef b pv Δ fs =>
        let%a Δ' := fill_tele_fn Γt Δ in
        let%a hs := fill_rfun_heads_fn (Δ' ++ Γt) fs in
        let%a fs' := fill_rfun_bodies_fn (Δ' ++ Γt) Δ' hs in
        fill_ok (core_cmd_mdef b pv Δ' fs')
    | core_cmd_inductive pv R => let%a R' := fill_raw_decl_at Γt R in fill_ok (core_cmd_inductive pv R')
    | core_cmd_load _ | core_cmd_gen _ => fill_ok c
    end.

  (** A command filled, over the fast telescope of the frames *)
  Definition fill_cmd_fn (c : core_cmd) : fill_result core_cmd := fill_cmd_at (fc_tele F) c.

  (** It is the fill over the Core telescope. *)
  Lemma fill_cmd_fn_core : forall c, fill_cmd_fn c = fill_cmd_at (gs_tele Ξ) c.
  Proof. intros; unfold fill_cmd_fn; rewrite fc_tele_ok; reflexivity. Qed.

  (** A unit's parameter telescope filled. *)
  Definition fill_params_fn (Δ : ctx) : fill_result ctx := fill_tele_fn (fc_tele F) Δ.

  (** It is the fill over the Core telescope. *)
  Lemma fill_params_fn_core : forall Δ, fill_params_fn Δ = fill_tele_fn (gs_tele Ξ) Δ.
  Proof. intros; unfold fill_params_fn; rewrite fc_tele_ok; reflexivity. Qed.

  (** An eliminator as written, through the named loops. *)
  Lemma fill_exp_fn_elim : forall Γ m Bks M0,
      fill_exp_fn Γ (a_elim None nil m Bks M0) = let%a M' := fill_exp_fn Γ M0 in elim_fill_fn Γ m Bks M'.
  Proof. reflexivity. Qed.

  (** A record value, through the named loop. *)
  Lemma fill_exp_fn_tuple : forall Γ T fs,
      fill_exp_fn Γ (a_tuple T fs) = let%a T' := fill_exp_fn Γ T in let%a fs' := fvals_fn Γ fs in fill_ok (a_tuple T' fs').
  Proof. reflexivity. Qed.

  (** A unit, through [fill_tele_fn]. *)
  Lemma fill_unit_fn_mk : forall Γ Δ D,
      fill_unit_fn Γ (gu_mk Δ D) =
        let%a Δ' := fill_tele_fn Γ Δ in let%a D' := fill_def_fn (Δ' ++ Γ) D in fill_ok (gu_mk Δ' D').
  Proof.
    intros; cbn [fill_unit_fn]; f_equal.
    induction Δ as [| e Δ IH]; cbn; [ reflexivity | rewrite IH; reflexivity ].
  Qed.

  (** ** What the Fill Reads, Specified *)

  (** The inference found, at the global context the fill relation reads
      it at ([gc_mk Θ Ξ], [fc_gctx_eta]) *)
  Lemma infer_at_sound : forall Γ M W, infer_at Γ M = Some W -> ⊢ Θ ⍮ Ξ ⍮ Γ /\ @alg_type_infer (gc_mk Θ Ξ) Γ W M.
  Proof.
    intros * E; unfold infer_at in E.
    destruct (check_ctx F Hg Γ) as [HΓ |]; [| discriminate ].
    destruct (type_infer F Γ HΓ M (type_infer_order_all M)) as [[W0 [HW _]] |]; [| discriminate ].
    injection E as <-; rewrite (fc_gctx_eta F) in HW; split; assumption.
  Qed.

  Lemma infer_at_complete : forall Γ M W, ⊢ Θ ⍮ Ξ ⍮ Γ -> @alg_type_infer (gc_mk Θ Ξ) Γ W M -> infer_at Γ M = Some W.
  Proof.
    intros * HΓ HW; rewrite <- (fc_gctx_eta F) in HW; unfold infer_at.
    destruct (check_ctx F Hg Γ) as [HΓ' | Hn]; [| contradiction ].
    destruct (type_infer F Γ HΓ' M (type_infer_order_all M)) as [[W0 [HW0 _]] | Hn];
      [| exfalso; exact (Hn _ HW) ].
    rewrite (@functional_alg_type_infer (fc_gctx F) _ _ _ _ Hg HW0 HW); reflexivity.
  Qed.

  Lemma term_binder_b_spec : forall Γ k, term_binder_b Γ k = true <-> term_binder Γ k.
  Proof.
    intros; unfold term_binder_b, term_binder.
    destruct (List.nth_error Γ k) as [[] |]; split; intros H; first [ exact I | reflexivity | discriminate | destruct H ].
  Qed.

  Lemma member_term_b_spec : forall Γ H y,
      member_term_b Γ H y = true <-> exists A oM, mdenote Θ Ξ Γ (me_mem H y) (ds_term A oM).
  Proof.
    intros; unfold member_term_b.
    destruct (mdenote_dec F Hg Γ (me_mem H y)) as [[R HR] | Hn].
    - destruct R; split; intros E; try discriminate; eauto;
        destruct E as (A & oM & HA); pose proof (proj1 (mdenote_functional_all _ _ Hg) _ _ _ HR _ HA); discriminate.
    - split; [ discriminate | intros (A & oM & HA); exfalso; exact (Hn _ HA) ].
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

  Definition exp_fill_sound (M : exp) : Prop :=
    forall Γ M', fill_exp_fn Γ M = fill_ok M' -> fill_exp Θ Ξ B Γ M M'.
  Definition read_fill_sound (H : modexp) : Prop :=
    forall Γ r, fill_read_fn Γ H = fill_ok r -> fill_read Θ Ξ B Γ H r.
  Definition unit_fill_sound (U : gunit) : Prop :=
    forall Γ U', fill_unit_fn Γ U = fill_ok U' -> fill_unit Θ Ξ B Γ U U'.
  Definition def_fill_sound (D : moddef) : Prop :=
    forall Γ D', fill_def_fn Γ D = fill_ok D' -> fill_def Θ Ξ B Γ D D'.
  Definition body_fill_sound (Φ : gmod) : Prop :=
    forall Γ Φ', fill_body_fn Γ Φ = fill_ok Φ' -> fill_body Θ Ξ B Γ Φ Φ'.
  Definition centry_fill_sound (e : centry) : Prop :=
    match e with
    | ce_ass A => exp_fill_sound A
    | ce_def A M => exp_fill_sound A /\ exp_fill_sound M
    | ce_mod U => unit_fill_sound U
    | ce_dm A M U => exp_fill_sound A /\ exp_fill_sound M /\ unit_fill_sound U
    end.
  Definition bnd_fill_sound (b : bnd) : Prop :=
    match b with
    | b_def oA M => (forall A, oA = Some A -> exp_fill_sound A) /\ exp_fill_sound M
    | b_mod U => unit_fill_sound U
    end.
  Definition gentry_fill_sound (E : gentry) : Prop :=
    match E with
    | ge_def _ _ A oM => exp_fill_sound A /\ (forall M, oM = Some M -> exp_fill_sound M)
    | ge_mod _ U => unit_fill_sound U
    | ge_def_mod _ A M U => exp_fill_sound A /\ exp_fill_sound M /\ unit_fill_sound U
    | _ => True
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

  Lemma oexp_fill_sound : forall Γ oM oM', (forall M, oM = Some M -> exp_fill_sound M) ->
      fill_oexp_fn Γ oM = fill_ok oM' -> fill_oexp Θ Ξ B Γ oM oM'.
  Proof.
    intros Γ [M |] oM' IH E; cbn in E; bind_inv; constructor; [ exact (IH _ eq_refl _ _ H) ].
  Qed.

  Lemma tele_fill_sound : forall Γ Δ Δ', Forall centry_fill_sound Δ -> fill_tele_fn Γ Δ = fill_ok Δ' ->
      fill_tele Θ Ξ B Γ Δ Δ'.
  Proof.
    intros Γ; induction Δ as [| e Δ IH]; intros Δ' HΔ E; cbn in E; bind_inv; [ constructor |].
    inversion HΔ as [| ? ? He HΔ0]; subst.
    specialize (IH _ HΔ0 H).
    destruct e as [A | A M | U | A M U]; cbn in *; bind_inv; constructor; auto; apply He; assumption.
  Qed.

  Lemma fvals_fill_sound : forall Γ fs fs', Forall (fun f => exp_fill_sound (snd f)) fs ->
      fvals_fn Γ fs = fill_ok fs' -> fill_fvals Θ Ξ B Γ fs fs'.
  Proof.
    intros Γ; induction fs as [| [f N] fs IH]; intros fs' Hf E; cbn in E; bind_inv; constructor;
      inversion Hf; subst; auto.
  Qed.

  Lemma brs_fill_sound : forall Γ p D Mj As Us Bs Bs', Forall (fun br => exp_fill_sound (snd br)) Bs ->
      brs_fn Γ p D Mj As Us Bs = fill_ok Bs' -> fill_brs Θ Ξ B Γ p D Mj Us As Bs Bs'.
  Proof.
    intros Γ p D Mj As Us; induction Bs as [| [[c n] B0] Bs IH]; intros Bs' HB E; cbn in E; bind_inv; [ constructor |].
    inversion HB; subst.
    destruct (ind_con Mj c) as [gs |] eqn:Ec; [| discriminate ].
    destruct (Nat.eqb_spec n (im_nn Mj + List.length gs + cargs_nrec D gs)); [| discriminate ].
    bind_inv; econstructor; eauto.
  Qed.

  (** The blocks of an eliminator: the motives they end with are the
      ones the branches were read at. *)
  Lemma blocks_fill_sound : forall Γ p D Us As j Bks hs Bks',
      Forall (fun b => (forall Z, eb_ann b = Some Z -> exp_fill_sound Z) /\ exp_fill_sound (eb_motive b) /\
                       Forall (fun br => exp_fill_sound (snd br)) (eb_brs b)) Bks ->
      heads_fn Γ p D Us j Bks = fill_ok hs -> blocks_fn Γ p D As Us j Bks hs = fill_ok Bks' ->
      fill_blocks Θ Ξ B Γ p D Us As j Bks Bks' /\ blocks_motives Bks' = List.map snd hs.
  Proof.
    intros Γ p D Us As j Bks; revert j; induction Bks as [| [nm oZ A Bs] Bks IH]; intros j hs Bks' HB Eh Eb;
      cbn in Eh; bind_inv; [ cbn in Eb; bind_inv; split; [ constructor | reflexivity ] |].
    inversion HB as [| ? ? (HZ & HA & HBs) HB0]; subst; cbn in HZ, HA, HBs.
    destruct (ind_member D j) as [Mj |] eqn:Ej; [| discriminate ].
    destruct (Nat.eqb_spec nm (S (im_nn Mj))) as [-> |]; [| discriminate ].
    bind_inv; cbn in Eb; rewrite Ej in Eb; bind_inv.
    destruct (IH _ _ _ HB0 H1 H3) as [Hb Hm].
    split; [| cbn; f_equal; exact Hm ].
    econstructor; [ exact Ej | reflexivity | | exact (HA _ _ H0) | eapply brs_fill_sound; eassumption | exact Hb ].
    destruct oZ as [Z |]; bind_inv; [ apply fill_oexp_some; eapply HZ; [ reflexivity | eassumption ] | apply fill_oexp_none ].
  Qed.

  (** An eliminator as written, its scrutinee filled. *)
  Lemma elim_fill_fn_sound : forall Γ m Bks M M',
      Forall (fun b => (forall Z, eb_ann b = Some Z -> exp_fill_sound Z) /\ exp_fill_sound (eb_motive b) /\
                       Forall (fun br => exp_fill_sound (snd br)) (eb_brs b)) Bks ->
      fill_exp Θ Ξ B Γ M M' -> forall E, elim_fill_fn Γ m Bks M' = fill_ok E ->
      fill_exp Θ Ξ B Γ (a_elim None nil m Bks M) E.
  Proof.
    intros * HB HM E Ee; unfold elim_fill_fn in Ee.
    destruct (infer_at Γ M') as [W |] eqn:Ei; [| discriminate ].
    destruct W as [| | | | | | | | | pc k Rs | | | | ]; try discriminate.
    apply infer_at_sound in Ei as [HΓ HW].
    destruct (elim_target_f F pc k Rs m Bks) as [p Us | rs |] eqn:Et; rewrite elim_target_f_ok in Et; try discriminate.
    destruct (fc_ind F p) as [D |] eqn:El; rewrite <- fc_ind_ok in El; [| discriminate ].
    bind_inv.
    destruct (blocks_fill_sound _ _ _ _ _ _ _ _ _ HB H H0) as [Hbk Hm].
    eapply fill_exp_elim; [ exact HM | exact HΓ | exact HW | exact Et | exact El | rewrite Hm; exact Hbk ].
  Qed.

  Lemma fill_fn_sound_all :
    (forall M, exp_fill_sound M) /\ (forall H, read_fill_sound H) /\ (forall b, bnd_fill_sound b) /\
    (forall U, unit_fill_sound U) /\ (forall D, def_fill_sound D) /\ (forall Φ, body_fill_sound Φ) /\
    (forall E, gentry_fill_sound E) /\ (forall e, centry_fill_sound e).
  Proof.
    apply syn_mut_ind; unfold exp_fill_sound, read_fill_sound, unit_fill_sound, def_fill_sound, body_fill_sound,
      centry_fill_sound, bnd_fill_sound, gentry_fill_sound; intros; try exact I; try (split; assumption);
      try match goal with
        |- forall _ _, _ = fill_ok _ -> _ => let G := fresh "Γ" in let X := fresh "X" in let E := fresh "E" in intros G X E
        end.
    all: try match goal with E : fill_exp_fn _ (a_tuple _ _) = _ |- _ => rewrite fill_exp_fn_tuple in E end;
      try match goal with E : fill_unit_fn _ (gu_mk _ _) = _ |- _ => rewrite fill_unit_fn_mk in E end.
    all: try match goal with
      | E : fill_exp_fn _ (a_elim _ _ _ _ _) = fill_ok _ |- _ => idtac
      | E : fill_exp_fn _ ?X = fill_ok _ |- _ => tryif is_var X then fail else cbn [fill_exp_fn] in E
      | E : fill_read_fn _ ?X = fill_ok _ |- _ => tryif is_var X then fail else cbn [fill_read_fn] in E
      | E : fill_def_fn _ ?X = fill_ok _ |- _ => tryif is_var X then fail else cbn [fill_def_fn] in E
      | E : fill_body_fn _ ?X = fill_ok _ |- _ => tryif is_var X then fail else cbn [fill_body_fn] in E
      end; bind_inv.
    all: try solve [ apply fill_exp_leaf; reflexivity | econstructor; eauto ].
    - (* a numeral *)
      destruct (nat_view_f F B) as [[[p z] s] |] eqn:Ev; rewrite nat_view_f_ok in Ev; [| discriminate ]; bind_inv; econstructor; exact Ev.
    - (* the token [ℕ] *)
      destruct (nat_view_f F B) as [[[p z] s] |] eqn:Ev; rewrite nat_view_f_ok in Ev; [| discriminate ]; bind_inv; econstructor; exact Ev.
    - (* an eliminator: written without its group, its scrutinee, then the
         reading and its blocks *)
      match goal with Ee : fill_exp_fn _ (a_elim _ _ _ _ _) = fill_ok _ |- _ => rename Ee into E end.
      destruct oq as [p |]; [ cbn in E; discriminate |]; destruct Us as [| U Us]; [| cbn in E; discriminate ].
      rewrite fill_exp_fn_elim in E; bind_inv.
      eapply elim_fill_fn_sound; [ eassumption | eauto | exact E ].
    - (* a let *)
      destruct b as [[A |] M0 | U].
      + destruct H as [HA HM]; bind_inv.
        apply fill_exp_let_ann; [ eapply HA; [ reflexivity | eassumption ] | apply HM; assumption | apply H0; assumption ].
      + destruct H as [_ HM]; bind_inv.
        destruct (infer_at Γ x) as [W |] eqn:Ei; [| discriminate ]; bind_inv.
        apply infer_at_sound in Ei as [? ?].
        eapply fill_exp_let_infer; [ apply HM; eassumption | eassumption | eassumption | apply H0; assumption ].
      + bind_inv; apply fill_exp_let_mod; [ apply H; assumption | apply H0; assumption ].
    - (* a member *)
      destruct (sel_check (snd x0) x) as [[qd y] |] eqn:Es; [ discriminate |]; bind_inv.
      destruct x0 as [H' op]; econstructor; [ eapply fill_mod_of_read_sound; eassumption | apply sel_check_spec; exact Es ].
    - (* a record value *)
      constructor; [ apply H; assumption | eapply fvals_fill_sound; eassumption ].
    - (* a binder in module position *)
      destruct (term_binder_b Γ k) eqn:Et; bind_inv.
      + apply term_binder_b_spec in Et; econstructor; exact Et.
      + apply fill_read_slot; intros HA.
        assert (term_binder_b Γ k = true) by (apply term_binder_b_spec; exact HA); congruence.
    - (* a member in module position *)
      destruct (sel_check (snd x) y) as [[qd x0] |] eqn:Es; [ discriminate |].
      destruct x as [H' op]; cbn [fst snd] in *.
      destruct (member_term_b Γ H' y) eqn:Em; bind_inv.
      + apply member_term_b_spec in Em as (A & oM & HA).
        eapply fill_read_mem_term; [ eapply fill_mod_of_read_sound; eassumption | apply sel_check_spec; exact Es | exact HA ].
      + eapply fill_read_mem_module; [ eapply fill_mod_of_read_sound; eassumption | apply sel_check_spec; exact Es |].
        intros A oM HA; assert (member_term_b Γ H' y = true) by (apply member_term_b_spec; eauto); congruence.
    - (* an application in module position *)
      destruct x; bind_inv; constructor; first [ apply H0; assumption | apply H1; assumption ].
    - exact H.
    - constructor; [ eapply tele_fill_sound; eassumption | apply H0; assumption ].
    - destruct x as [E' op]; econstructor; eapply fill_mod_of_read_sound; eassumption.
    - (* an entry of a body, in the expansion of the body before it *)
      apply body_xp_fn_spec in H3.
      destruct E as [b pv A oM | pv U | | |]; try discriminate; bind_inv.
      + destruct H0 as [HA HoM].
        eapply fill_body_def; [ apply H; eassumption | eassumption | apply HA; assumption |].
        destruct oM as [M |]; bind_inv;
          [ apply fill_oexp_some; eapply HoM; [ reflexivity | eassumption ] | apply fill_oexp_none ].
      + eapply fill_body_mod; [ apply H; eassumption | eassumption | apply H0; assumption ].
      + destruct H0 as (HA & HM & HU).
        eapply fill_body_dm; [ apply H; eassumption | eassumption | apply HA; assumption | apply HM; assumption
                             | apply HU; assumption ].
    - (* a local open *)
      apply body_xp_fn_spec in H4; destruct x2; apply sels_check_spec in H6; destruct x1 as [H' op].
      eapply fill_body_open; [ apply H0; eassumption | eassumption | eapply fill_mod_of_read_sound; eassumption | exact H6 ].
    - exact H.
    - exact H.
    - exact H.
  Qed.

  (** ** The Relation's Fill Is Computed *)

  (** The annotation and motive of each block. *)
  Definition block_heads (Bks : list eblock) : list (option exp * exp) :=
    List.map (fun b => (eb_ann b, eb_motive b)) Bks.

  Lemma fill_fn_complete_all :
    (forall Γ M M', fill_exp Θ Ξ B Γ M M' -> fill_exp_fn Γ M = fill_ok M') /\
    (forall Γ fs fs', fill_fvals Θ Ξ B Γ fs fs' -> fvals_fn Γ fs = fill_ok fs') /\
    (forall Γ p D Us As j Bks Bks', fill_blocks Θ Ξ B Γ p D Us As j Bks Bks' ->
       heads_fn Γ p D Us j Bks = fill_ok (block_heads Bks') /\
       blocks_fn Γ p D As Us j Bks (block_heads Bks') = fill_ok Bks') /\
    (forall Γ p D Mj Us As Bs Bs', fill_brs Θ Ξ B Γ p D Mj Us As Bs Bs' -> brs_fn Γ p D Mj As Us Bs = fill_ok Bs') /\
    (forall Γ oM oM', fill_oexp Θ Ξ B Γ oM oM' -> fill_oexp_fn Γ oM = fill_ok oM') /\
    (forall Γ H r, fill_read Θ Ξ B Γ H r -> fill_read_fn Γ H = fill_ok r) /\
    (forall Γ H H' op, fill_mod Θ Ξ B Γ H H' op -> forall y, fill_mod_fn Γ y H = fill_ok (H', op)) /\
    (forall Γ U U', fill_unit Θ Ξ B Γ U U' -> fill_unit_fn Γ U = fill_ok U') /\
    (forall Γ D D', fill_def Θ Ξ B Γ D D' -> fill_def_fn Γ D = fill_ok D') /\
    (forall Γ Δ Δ', fill_tele Θ Ξ B Γ Δ Δ' -> fill_tele_fn Γ Δ = fill_ok Δ') /\
    (forall Γ Φ Φ', fill_body Θ Ξ B Γ Φ Φ' -> fill_body_fn Γ Φ = fill_ok Φ').
  Proof.
    apply fill_mut_ind; intros;
      try match goal with |- fill_exp_fn _ (a_elim _ _ _ _ _) = _ => rewrite fill_exp_fn_elim end;
      try match goal with |- fill_exp_fn _ (a_tuple _ _) = _ => rewrite fill_exp_fn_tuple end;
      try match goal with |- fill_unit_fn _ (gu_mk _ _) = _ => rewrite fill_unit_fn_mk end;
      try match goal with |- fill_mod_fn _ _ _ = _ => unfold fill_mod_fn end;
      cbn [fill_exp_fn fill_read_fn fill_def_fn fill_body_fn fill_tele_fn fvals_fn brs_fn heads_fn blocks_fn
           fill_oexp_fn];
      repeat match goal with E : ?a = fill_ok _ |- context [?a] => rewrite E; cbn [fill_result_bind] end;
      try reflexivity.
    - (* a term with no subterm *)
      destruct M; try discriminate; reflexivity.
    - (* a numeral *)
      rewrite nat_view_f_ok, e; reflexivity.
    - (* the token [ℕ] *)
      rewrite nat_view_f_ok, e; reflexivity.
    - (* an unannotated let: its definition infers the type *)
      rewrite (infer_at_complete _ _ _ w a); cbn; rewrite H0; reflexivity.
    - (* a member *)
      unfold fill_mod_fn in H0; rewrite (H0 x); cbn; rewrite (proj2 (sel_check_spec _ _) s); reflexivity.
    - (* an eliminator: the reading, then its blocks, whose motives are
         those its branches are read at *)
      unfold elim_fill_fn; rewrite (infer_at_complete _ _ _ w a), elim_target_f_ok, e, <- fc_ind_ok, e0.
      destruct H0 as [Hh Hb]; rewrite Hh; cbn.
      replace (List.map snd (block_heads Bks')) with (blocks_motives Bks')
        by (clear; induction Bks' as [| [] ? IH]; cbn; [ reflexivity | f_equal; exact IH ]).
      rewrite Hb; reflexivity.
    - split; reflexivity.
    - (* a block *)
      rewrite e; subst nm; rewrite Nat.eqb_refl.
      change (match oZ with Some Z => _ | None => fill_ok None end)
        with (fill_oexp_fn (tele_sub (im_nparams Mj) (sb_of_list Id Us) ++ Γ) oZ).
      rewrite H, H0; destruct H2 as [Hh Hb]; rewrite Hh; split; cbn; [ reflexivity |].
      rewrite H1; cbn; unfold block_heads in Hb; rewrite Hb; reflexivity.
    - (* a branch *)
      rewrite e; subst n; rewrite Nat.eqb_refl, H; reflexivity.
    - (* a binder that holds no term *)
      destruct (term_binder_b Γ k) eqn:E; [ apply term_binder_b_spec in E; exfalso; exact (n E) | reflexivity ].
    - (* a term binder *)
      rewrite (proj2 (term_binder_b_spec Γ k) t); reflexivity.
    - (* a member that is no term *)
      unfold fill_mod_fn in H0; rewrite (H0 y); cbn; rewrite (proj2 (sel_check_spec _ _) s).
      destruct (member_term_b Γ H' y) eqn:Em;
        [ apply member_term_b_spec in Em as (A & oM & HA); exfalso; exact (n _ _ HA) | reflexivity ].
    - (* a member that is a term *)
      unfold fill_mod_fn in H0; rewrite (H0 y); cbn; rewrite (proj2 (sel_check_spec _ _) s).
      rewrite (proj2 (member_term_b_spec Γ H' y) (ex_intro _ A (ex_intro _ oM m))); reflexivity.
    - (* a term of a record type *)
      cbn; rewrite (infer_at_complete _ _ _ w a); reflexivity.
    - unfold fill_mod_fn in H; rewrite (H ""); reflexivity.
    - cbn; rewrite H0; reflexivity.
    - cbn; repeat match goal with E : ?a = fill_ok _ |- context [?a] => rewrite E; cbn [fill_result_bind] end; reflexivity.
    - cbn; repeat match goal with E : ?a = fill_ok _ |- context [?a] => rewrite E; cbn [fill_result_bind] end; reflexivity.
    - (* a definition with a module part of a telescope *)
      cbn; repeat match goal with E : ?a = fill_ok _ |- context [?a] => rewrite E; cbn [fill_result_bind] end; reflexivity.
    - (* an entry of a body, in the expansion of the body before it *)
      rewrite (proj2 (body_xp_fn_spec _ _ _) b0); cbn; rewrite H0; cbn.
      change (match oM with Some M => _ | None => fill_ok None end) with (fill_oexp_fn (body_ctx Φx ++ Γ) oM).
      rewrite H1; reflexivity.
    - rewrite (proj2 (body_xp_fn_spec _ _ _) b); cbn; rewrite H0; reflexivity.
    - (* a definition with a module part of a body *)
      rewrite (proj2 (body_xp_fn_spec _ _ _) b); cbn;
        repeat match goal with E : ?a = fill_ok _ |- context [?a] => rewrite E; cbn [fill_result_bind] end; reflexivity.
    - (* a local open *)
      rewrite (proj2 (body_xp_fn_spec _ _ _) b); cbn; unfold fill_mod_fn in H1; rewrite (H1 ""); cbn.
      rewrite (proj2 (sels_check_spec _ _) f1); reflexivity.
  Qed.

  (** ** Commands *)

  Lemma fill_exp_fn_sound : forall Γ M M', fill_exp_fn Γ M = fill_ok M' -> fill_exp Θ Ξ B Γ M M'.
  Proof. intros; apply (proj1 fill_fn_sound_all); assumption. Qed.

  Lemma fill_oexp_fn_sound : forall Γ oM oM', fill_oexp_fn Γ oM = fill_ok oM' -> fill_oexp Θ Ξ B Γ oM oM'.
  Proof. intros; eapply oexp_fill_sound; [ intros; apply (proj1 fill_fn_sound_all) | eassumption ]. Qed.

  Lemma fill_tele_fn_sound : forall Γ Δ Δ', fill_tele_fn Γ Δ = fill_ok Δ' -> fill_tele Θ Ξ B Γ Δ Δ'.
  Proof.
    intros; eapply tele_fill_sound; [ apply Forall_forall; intros; apply fill_fn_sound_all | eassumption ].
  Qed.

  Lemma fill_mod_fn_sound : forall Γ y H H' op, fill_mod_fn Γ y H = fill_ok (H', op) -> fill_mod Θ Ξ B Γ H H' op.
  Proof. intros; eapply fill_mod_of_read_sound; [ apply fill_fn_sound_all | eassumption ]. Qed.

  Lemma fill_fields_fn_sound : forall Γ fs fs', fill_fields_fn Γ fs = fill_ok fs' -> fill_fields Θ Ξ B Γ fs fs'.
  Proof.
    intros Γ fs; revert Γ; induction fs as [| [f T] fs IH]; intros Γ fs' E; cbn in E; bind_inv; constructor;
      [ apply fill_exp_fn_sound; assumption | apply IH; assumption ].
  Qed.

  Lemma fill_fields_fn_complete : forall Γ fs fs', fill_fields Θ Ξ B Γ fs fs' -> fill_fields_fn Γ fs = fill_ok fs'.
  Proof.
    induction 1 as [| Γ f T T' fs fs' HT _ IH]; cbn; [ reflexivity |].
    rewrite (proj1 fill_fn_complete_all _ _ _ HT); cbn; rewrite IH; reflexivity.
  Qed.

  (** A mutual definition's heads, filled as the relation fills them. *)
  Lemma fill_rfun_heads_fn_sound : forall Γ fs hs,
      fill_rfun_heads_fn Γ fs = fill_ok hs -> Forall2 (fill_raw_fun_head Θ Ξ B Γ) fs hs.
  Proof.
    intros Γ fs; induction fs as [| f fs IH]; intros hs E; cbn in E; bind_inv; constructor; [| apply IH; assumption ].
    constructor; cbn; [ reflexivity | apply fill_tele_fn_sound; assumption | apply fill_exp_fn_sound; assumption
                      | reflexivity | reflexivity ].
  Qed.

  Lemma fill_rfun_heads_fn_complete : forall Γ fs hs,
      Forall2 (fill_raw_fun_head Θ Ξ B Γ) fs hs -> fill_rfun_heads_fn Γ fs = fill_ok hs.
  Proof.
    pose proof fill_fn_complete_all as (Ce & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
    induction 1 as [| f h fs hs [En Ep Es Er Ec] _ IH]; cbn; [ reflexivity |].
    rewrite (Ct _ _ _ Ep); cbn; rewrite (Ce _ _ _ Es); cbn; rewrite IH; cbn.
    rewrite <- (raw_fun_parts_eq (mk_rfun (raw_fun_name f) (raw_fun_nparams h) (raw_fun_scrut h) (raw_fun_res f) (raw_fun_clauses f)) h
                  En eq_refl eq_refl Er Ec); reflexivity.
  Qed.

  (** A mutual definition's results, then its clauses, filled as the
      relation fills them: the results keep the parameters, which, with
      them, fix the motives. *)
  Lemma fill_rfun_bodies_parts_sound : forall Γ pq D Us As hs ms rs fs',
      fill_rfun_results_fn Γ pq D Us (List.combine hs ms) = fill_ok rs ->
      fill_rfun_clauses_fn Γ pq D Us As (List.combine rs ms) = fill_ok fs' ->
      Forall2 (fun fm f' => fill_raw_fun_body Θ Ξ B pq D Us Γ As (fst fm) (snd fm) f') (List.combine hs ms) fs' /\
      Forall2 (fun f1 f2 => raw_fun_nparams f1 = raw_fun_nparams f2 /\ raw_fun_res f1 = raw_fun_res f2) fs' rs.
  Proof.
    intros Γ pq D Us As hs; induction hs as [| h hs IH]; intros [| m ms] rs fs' Er Ec; cbn in Er;
      bind_inv; cbn in Ec; bind_inv; try (split; constructor).
    destruct (ind_member D m) as [Mm |] eqn:Hj; [| discriminate ]; bind_inv; cbn in Ec.
    rewrite Hj in Ec; bind_inv.
    destruct (IH _ _ _ H0 H2) as [Hb Hrs].
    split; constructor; cbn; [| exact Hb | split; reflexivity | exact Hrs ].
    constructor; cbn; [ reflexivity | reflexivity | reflexivity | congruence | | ].
    - intros Mm' Hj'; rewrite Hj in Hj'; injection Hj' as <-; apply fill_exp_fn_sound; assumption.
    - intros Mm' Hj'; rewrite Hj in Hj'; injection Hj' as <-; eapply brs_fill_sound; [| eassumption ].
      apply Forall_forall; intros; apply fill_fn_sound_all.
  Qed.

  Lemma fill_rfun_bodies_parts_complete : forall Γ pq D Us As hs ms fs',
      Forall2 (fun fm f' => fill_raw_fun_body Θ Ξ B pq D Us Γ As (fst fm) (snd fm) f') (List.combine hs ms) fs' ->
      exists rs, fill_rfun_results_fn Γ pq D Us (List.combine hs ms) = fill_ok rs /\
        Forall2 (fun f1 f2 => raw_fun_nparams f1 = raw_fun_nparams f2 /\ raw_fun_res f1 = raw_fun_res f2) rs fs' /\
        fill_rfun_clauses_fn Γ pq D Us As (List.combine rs ms) = fill_ok fs'.
  Proof.
    pose proof fill_fn_complete_all as (Ce & _ & _ & Cb & _).
    intros Γ pq D Us As hs; induction hs as [| h hs IH]; intros [| m ms] fs' Hb; cbn in Hb;
      inversion Hb as [| ? f' ? fs'' [En Ep Es Hm Hr Hc] Hb']; subst; try (exists nil; repeat split; constructor).
    cbn [fst snd] in *.
    destruct (ind_member D m) as [Mm |] eqn:Hj; [| contradiction ].
    destruct (IH _ _ Hb') as (rs & Er & Hrs & Ec).
    exists (mk_rfun (raw_fun_name h) (raw_fun_nparams h) (raw_fun_scrut h) (raw_fun_res f') (raw_fun_clauses h) :: rs); cbn.
    rewrite Hj, (Ce _ _ _ (Hr Mm eq_refl)); cbn; rewrite Er; cbn.
    split; [ reflexivity | split; [ constructor; [ cbn; split; [ exact (eq_sym Ep) | reflexivity ] | exact Hrs ] |] ].
    rewrite (Cb _ _ _ _ _ _ _ _ (Hc Mm eq_refl)); cbn; rewrite Ec; cbn.
    rewrite (raw_fun_parts_eq f' (mk_rfun (raw_fun_name h) (raw_fun_nparams h) (raw_fun_scrut h) (raw_fun_res f') (raw_fun_clauses f'))
               (eq_sym En) (eq_sym Ep) (eq_sym Es) eq_refl eq_refl); reflexivity.
  Qed.

  (** ** A Group's Fill *)

  Lemma zip_ass_sound : forall ys es a, zip_ass ys es = Some a ->
      List.map fst a = ys /\ List.map (fun x => ce_ass (snd x)) a = es.
  Proof.
    induction ys as [| y ys IH]; intros [| [A | A M | U | A M U] es] a E; cbn in E; try discriminate;
      [ injection E as <-; split; reflexivity |].
    destruct (zip_ass ys es) as [a0 |] eqn:E0; cbn in E; [| discriminate ]; injection E as <-.
    destruct (IH _ _ E0) as [<- <-]; split; reflexivity.
  Qed.

  Lemma zip_ass_complete : forall a, zip_ass (List.map fst a) (List.map (fun x => ce_ass (snd x)) a) = Some a.
  Proof. induction a as [| [y A] a IH]; cbn; [ reflexivity | rewrite IH; reflexivity ]. Qed.

  Lemma fill_raw_args_fn_sound : forall Γ args args',
      fill_raw_args_fn Γ args = fill_ok args' -> fill_raw_args Θ Ξ B Γ args args'.
  Proof.
    intros * E; unfold fill_raw_args_fn in E; bind_inv.
    destruct (zip_ass _ _) as [a |] eqn:Ez; [| discriminate ]; injection E as <-.
    destruct (zip_ass_sound _ _ _ Ez) as [En Et].
    constructor; [ exact En |].
    replace (rtele a) with x; [ apply fill_tele_fn_sound; assumption |].
    unfold rtele; rewrite Et, rev_involutive; reflexivity.
  Qed.

  Lemma fill_raw_args_fn_complete : forall Γ args args',
      fill_raw_args Θ Ξ B Γ args args' -> fill_raw_args_fn Γ args = fill_ok args'.
  Proof.
    pose proof fill_fn_complete_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
    intros * [En Ht]; unfold fill_raw_args_fn; rewrite (Ct _ _ _ Ht); cbn [fill_result_bind].
    rewrite <- En; unfold rtele; rewrite rev_involutive, zip_ass_complete; reflexivity.
  Qed.

  Lemma fill_raw_cons_fn_sound : forall Γ cs cs', fill_raw_cons_fn Γ cs = fill_ok cs' ->
      Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_raw_args Θ Ξ B Γ (snd rc) (snd rc')) cs cs'.
  Proof.
    intros Γ cs; induction cs as [| [c args] cs IH]; intros cs' E; cbn in E; bind_inv; [ constructor |].
    constructor; [ split; [ reflexivity | apply fill_raw_args_fn_sound; assumption ] | apply IH; assumption ].
  Qed.

  Lemma fill_raw_cons_fn_complete : forall Γ cs cs',
      Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_raw_args Θ Ξ B Γ (snd rc) (snd rc')) cs cs' ->
      fill_raw_cons_fn Γ cs = fill_ok cs'.
  Proof.
    induction 1 as [| [c args] [c' args'] cs cs' [Ef Ha] _ IH]; cbn; [ reflexivity |].
    cbn in Ef, Ha; subst; rewrite (fill_raw_args_fn_complete _ _ _ Ha); cbn [fill_result_bind]; rewrite IH; reflexivity.
  Qed.

  Lemma fill_raw_heads_fn_sound : forall Γ ms hs, fill_raw_heads_fn Γ ms = fill_ok hs ->
      Forall2 (fun Mr Mh => raw_member_name Mh = raw_member_name Mr /\ fill_tele Θ Ξ B Γ (raw_member_nparams Mr) (raw_member_nparams Mh) /\
                            fill_exp Θ Ξ B Γ (raw_member_sort Mr) (raw_member_sort Mh) /\ raw_member_cons Mh = raw_member_cons Mr) ms hs.
  Proof.
    intros Γ ms; induction ms as [| Mr ms IH]; intros hs E; cbn in E; bind_inv; [ constructor |].
    constructor; [ cbn; repeat split; [ apply fill_tele_fn_sound | apply fill_exp_fn_sound ]; assumption
                 | apply IH; assumption ].
  Qed.

  Lemma fill_raw_bodies_fn_sound : forall Rh hs ms', fill_raw_bodies_at (gs_tele Ξ) Rh hs = fill_ok ms' ->
      Forall2 (fun Mh Mr' => raw_member_name Mr' = raw_member_name Mh /\ raw_member_nparams Mr' = raw_member_nparams Mh /\ raw_member_sort Mr' = raw_member_sort Mh /\
                             Forall2 (fun rc rc' => fst rc' = fst rc /\ fill_raw_args Θ Ξ B (rm_pctx Ξ Rh Mh) (snd rc) (snd rc'))
                               (raw_member_cons Mh) (raw_member_cons Mr')) hs ms'.
  Proof.
    intros Rh hs; induction hs as [| Mh hs IH]; intros ms' E; cbn in E; bind_inv; [ constructor |].
    constructor; [ cbn; repeat split; apply fill_raw_cons_fn_sound; assumption | apply IH; assumption ].
  Qed.

  (** The members' heads, then their constructors, filled in the group of
      the filled heads: the relation's members of the filled group. *)
  Lemma fill_raw_members_compose : forall ups rec hsG msG ms hs ms',
      Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2) hsG msG ->
      Forall2 (fun Mr Mh => raw_member_name Mh = raw_member_name Mr /\ fill_tele Θ Ξ B (ups ++ gs_tele Ξ) (raw_member_nparams Mr) (raw_member_nparams Mh) /\
                            fill_exp Θ Ξ B (ups ++ gs_tele Ξ) (raw_member_sort Mr) (raw_member_sort Mh) /\ raw_member_cons Mh = raw_member_cons Mr) ms hs ->
      Forall2 (fun Mh Mr' => raw_member_name Mr' = raw_member_name Mh /\ raw_member_nparams Mr' = raw_member_nparams Mh /\ raw_member_sort Mr' = raw_member_sort Mh /\
                             Forall2 (fun rc rc' => fst rc' = fst rc /\
                                                    fill_raw_args Θ Ξ B (rm_pctx Ξ (mk_raw ups hsG rec) Mh) (snd rc) (snd rc'))
                               (raw_member_cons Mh) (raw_member_cons Mr')) hs ms' ->
      Forall2 (fill_raw_member Θ Ξ B (mk_raw ups msG rec)) ms ms'.
  Proof.
    intros * HG Hh; revert ms'; induction Hh as [| Mr Mh ms hs (En & Hn & Hs & Hc) _ IH]; intros ms' Hb;
      inversion Hb as [| ? Mr' ? ms'' (En' & Ep' & Es' & Hc') Hb']; subst; constructor; [| exact (IH _ Hb') ].
    rewrite (rm_pctx_heads_eq Ξ (mk_raw ups hsG rec) (mk_raw ups msG rec) Mh Mr' eq_refl HG (eq_sym Ep')) in Hc'.
    rewrite Hc in Hc'.
    constructor; cbn; [ congruence | rewrite Ep'; exact Hn | rewrite Es'; exact Hs | exact Hc' ].
  Qed.

  (** The computed fill of a group is the relation's. *)
  Lemma fill_raw_decl_fn_sound : forall R R', fill_raw_decl_at (gs_tele Ξ) R = fill_ok R' -> fill_raw_decl Θ Ξ B R R'.
  Proof.
    intros R R' E; unfold fill_raw_decl_at in E; bind_inv.
    rename x into ups', x0 into hs, x1 into ms'.
    pose proof (fill_raw_heads_fn_sound _ _ _ H0) as Hh.
    pose proof (fill_raw_bodies_fn_sound _ _ _ H1) as Hb.
    assert (Hhb : Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2) hs ms').
    { eapply Forall2_impl; [| exact Hb ]; intros Mh Mr' (_ & Ep & Es & _); split; symmetry; assumption. }
    constructor; cbn; [ apply fill_tele_fn_sound; assumption | reflexivity |].
    exact (fill_raw_members_compose _ _ _ _ _ _ _ Hhb Hh Hb).
  Qed.

  (** The relation's fill of a group is computed. *)
  Lemma fill_raw_heads_fn_complete : forall R' ms ms', Forall2 (fill_raw_member Θ Ξ B R') ms ms' ->
      exists hs, fill_raw_heads_fn (raw_decl_uparams R' ++ gs_tele Ξ) ms = fill_ok hs /\
        Forall2 (fun Mh Mr' => raw_member_name Mh = raw_member_name Mr' /\ raw_member_nparams Mh = raw_member_nparams Mr' /\ raw_member_sort Mh = raw_member_sort Mr' /\
                               Forall2 (fun rc rc' => fst rc' = fst rc /\
                                                      fill_raw_args Θ Ξ B (rm_pctx Ξ R' Mr') (snd rc) (snd rc'))
                                 (raw_member_cons Mh) (raw_member_cons Mr')) hs ms'.
  Proof.
    pose proof fill_fn_complete_all as (Ce & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
    induction 1 as [| Mr Mr' ms ms' [En Hn Hs Hc] _ (hs & Eh & Hhs)]; [ exists nil; split; [ reflexivity | constructor ] |].
    exists (mk_rmem (raw_member_name Mr) (raw_member_nparams Mr') (raw_member_sort Mr') (raw_member_cons Mr) :: hs); cbn.
    rewrite (Ct _ _ _ Hn); cbn [fill_result_bind]; rewrite (Ce _ _ _ Hs); cbn [fill_result_bind]; rewrite Eh.
    split; [ reflexivity | constructor; [ cbn; repeat split; [ exact (eq_sym En) | exact Hc ] | exact Hhs ] ].
  Qed.

  Lemma fill_raw_bodies_fn_complete : forall Rh R' hs ms', raw_decl_uparams Rh = raw_decl_uparams R' ->
      Forall2 (fun M1 M2 => raw_member_nparams M1 = raw_member_nparams M2 /\ raw_member_sort M1 = raw_member_sort M2) (raw_decl_members Rh) (raw_decl_members R') ->
      Forall2 (fun Mh Mr' => raw_member_name Mh = raw_member_name Mr' /\ raw_member_nparams Mh = raw_member_nparams Mr' /\ raw_member_sort Mh = raw_member_sort Mr' /\
                             Forall2 (fun rc rc' => fst rc' = fst rc /\
                                                    fill_raw_args Θ Ξ B (rm_pctx Ξ R' Mr') (snd rc) (snd rc'))
                               (raw_member_cons Mh) (raw_member_cons Mr')) hs ms' ->
      fill_raw_bodies_at (gs_tele Ξ) Rh hs = fill_ok ms'.
  Proof.
    intros * Eu HG; induction 1 as [| Mh Mr' hs ms' (En & Ep & Es & Hc) _ IH]; cbn; [ reflexivity |].
    change (rm_pctx_at (gs_tele Ξ)) with (rm_pctx Ξ).
    rewrite (rm_pctx_heads_eq Ξ Rh R' Mh Mr' Eu HG Ep), (fill_raw_cons_fn_complete _ _ _ Hc); cbn [fill_result_bind].
    rewrite IH; cbn [fill_result_bind].
    rewrite (raw_member_parts_eq Mr' (mk_rmem (raw_member_name Mh) (raw_member_nparams Mh) (raw_member_sort Mh) (raw_member_cons Mr')) En Ep Es eq_refl);
      reflexivity.
  Qed.

  Lemma fill_raw_decl_fn_complete : forall R R', fill_raw_decl Θ Ξ B R R' -> fill_raw_decl_at (gs_tele Ξ) R = fill_ok R'.
  Proof.
    pose proof fill_fn_complete_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
    intros R R' [Hu Hr Hm]; unfold fill_raw_decl_at; rewrite (Ct _ _ _ Hu); cbn [fill_result_bind].
    destruct (fill_raw_heads_fn_complete _ _ _ Hm) as (hs & Eh & Hhs); rewrite Eh; cbn [fill_result_bind].
    rewrite (fill_raw_bodies_fn_complete (mk_raw (raw_decl_uparams R') hs (raw_decl_rec_field R)) R' hs (raw_decl_members R') eq_refl); cbn.
    - rewrite (raw_decl_parts_eq R' (mk_raw (raw_decl_uparams R') (raw_decl_members R') (raw_decl_rec_field R)) eq_refl eq_refl (eq_sym Hr));
        reflexivity.
    - eapply Forall2_impl; [| exact Hhs ]; intros Mh Mr' (_ & Ep & Es & _); split; assumption.
    - exact Hhs.
  Qed.

  (** A mutual definition's bodies, filled as the relation fills them. *)
  Lemma fill_rfun_bodies_fn_sound : forall Γ Δ' h0 hs0 fs',
      Γ = (Δ' ++ gs_tele Ξ)%list ->
      fill_rfun_bodies_fn Γ Δ' (h0 :: hs0) = fill_ok fs' ->
      exists f0' fs0' pq m0 Ps D Us ms, fs' = f0' :: fs0' /\
        mdef_group Θ Ξ Δ' h0 hs0 pq m0 Ps D Us ms /\
        Forall2 (fun fm f' => fill_raw_fun_body Θ Ξ B pq D Us Γ
                                (blocks_motives (mdef_blocks 0 (ind_nblk D) (f0' :: fs0') ms))
                                (fst fm) (snd fm) f')
          (List.combine (h0 :: hs0) ms) (f0' :: fs0').
  Proof.
    intros * -> E; unfold fill_rfun_bodies_fn in E.
    destruct (mdef_group_dec F Hg Δ' h0 hs0) as [[[[[[[pq m0] Ps] D] Us] ms] Hgp] | e]; [| discriminate ].
    bind_inv.
    destruct (fill_rfun_bodies_parts_sound _ _ _ _ _ _ _ _ _ H E) as [Hb Hrs].
    pose proof (mdef_group_members _ _ _ _ _ _ _ _ _ _ _ Hgp) as Hms.
    destruct ms as [| m ms]; [ inversion Hms |]; cbn in Hb.
    inversion Hb as [| ? f0' ? fs0' ? ?]; subst.
    exists f0', fs0', pq, m0, Ps, D, Us, (m :: ms); split; [ reflexivity | split; [ exact Hgp |] ].
    rewrite (mdef_blocks_motives_eq _ _ _ _ _ Hrs); exact Hb.
  Qed.

  Lemma fill_rfun_bodies_fn_complete : forall Δ' h0 hs0 f0' fs0' pq m0 Ps D Us ms,
      mdef_group Θ Ξ Δ' h0 hs0 pq m0 Ps D Us ms ->
      Forall2 (fun fm f' => fill_raw_fun_body Θ Ξ B pq D Us (Δ' ++ gs_tele Ξ)%list
                              (blocks_motives (mdef_blocks 0 (ind_nblk D) (f0' :: fs0') ms))
                              (fst fm) (snd fm) f')
        (List.combine (h0 :: hs0) ms) (f0' :: fs0') ->
      fill_rfun_bodies_fn (Δ' ++ gs_tele Ξ)%list Δ' (h0 :: hs0) = fill_ok (f0' :: fs0').
  Proof.
    intros * Hgp Hb; unfold fill_rfun_bodies_fn.
    destruct (mdef_group_dec_complete _ Hg _ _ _ _ _ _ _ _ _ Hgp) as [Hp ->].
    destruct (fill_rfun_bodies_parts_complete _ _ _ _ _ _ _ _ Hb) as (rs & Er & Hrs & Ec).
    rewrite Er; cbn; rewrite (mdef_blocks_motives_eq _ _ _ _ _ Hrs); exact Ec.
  Qed.

  (** The computed fill of a command is the relation's. *)
  Theorem fill_cmd_fn_sound : forall c c', fill_cmd_fn c = fill_ok c' -> fill_cmd Θ Ξ B c c'.
  Proof.
    intros c c'; rewrite fill_cmd_fn_core; destruct c; cbn [fill_cmd_at]; intros E; bind_inv; try discriminate.
    - constructor; [ apply fill_exp_fn_sound | apply fill_oexp_fn_sound ]; assumption.
    - constructor; apply fill_tele_fn_sound; assumption.
    - destruct x0 as [E' op]; econstructor; [ apply fill_tele_fn_sound | eapply fill_mod_fn_sound ]; eassumption.
    - constructor.
    - destruct x as [E' op]; destruct x0; apply sels_check_spec in H0.
      econstructor; [ eapply fill_mod_fn_sound; eassumption | exact H0 ].
    - constructor; [ apply fill_exp_fn_sound | apply fill_oexp_fn_sound ]; assumption.
    - (* a group *)
      constructor; apply fill_raw_decl_fn_sound; assumption.
    - (* a mutual definition: its telescope, its heads, then its bodies *)
      match goal with
      | Ht : fill_tele_fn _ _ = fill_ok _, Hh : fill_rfun_heads_fn _ ?fs = fill_ok ?hs,
        Hb : fill_rfun_bodies_fn _ _ ?hs = fill_ok _ |- _ =>
          destruct hs as [| h0 hs0]; [ discriminate |];
          destruct (fill_rfun_bodies_fn_sound _ _ _ _ _ eq_refl Hb)
            as (f0' & fs0' & pq & m0 & Ps & D & Us & ms & -> & Hgp & Hb');
          pose proof (fill_rfun_heads_fn_sound _ _ _ Hh) as Hh';
          destruct fs as [| f0 fs]; [ inversion Hh' |];
          eapply fill_cmd_mdef; [ apply fill_tele_fn_sound; exact Ht | exact Hh' | exact Hgp | exact Hb' ]
      end.
    - destruct x as [E' [p |]]; cbn [fst snd] in *; bind_inv; try discriminate.
      constructor; eapply fill_mod_fn_sound; eassumption.
    - destruct x0 as [E' [p |]]; cbn [fst snd] in *; bind_inv; try discriminate.
      constructor; [ apply fill_tele_fn_sound | eapply fill_mod_fn_sound ]; eassumption.
    - destruct x0 as [E' [p |]]; cbn [fst snd] in *; bind_inv; try discriminate.
      constructor; [ apply fill_tele_fn_sound | eapply fill_mod_fn_sound ]; eassumption.
    - constructor; [ apply fill_tele_fn_sound | apply fill_exp_fn_sound | apply fill_fields_fn_sound ]; assumption.
    - constructor.
  Qed.

  (** The relation's fill of a command is computed. *)
  Theorem fill_cmd_fn_complete : forall c c', fill_cmd Θ Ξ B c c' -> fill_cmd_fn c = fill_ok c'.
  Proof.
    pose proof fill_fn_complete_all as (Ce & _ & _ & _ & Co & _ & Cm & _ & _ & Ct & _).
    intros c c' H; rewrite fill_cmd_fn_core; inversion H; subst; cbn [fill_cmd_at]; try reflexivity.
    - rewrite (Ce _ _ _ H0); cbn; rewrite (Co _ _ _ H1); reflexivity.
    - rewrite (Ct _ _ _ H0); reflexivity.
    - rewrite (Ct _ _ _ H0); cbn; rewrite (Cm _ _ _ _ H1 ""); reflexivity.
    - rewrite (Ct _ _ _ H0); cbn; rewrite (Cm _ _ _ _ H1 ""); reflexivity.
    - rewrite (Ct _ _ _ H0); cbn; rewrite (Cm _ _ _ _ H1 ""); reflexivity.
    - rewrite (Cm _ _ _ _ H0 ""); cbn; rewrite (proj2 (sels_check_spec _ _) H1); reflexivity.
    - rewrite (Cm _ _ _ _ H0 ""); reflexivity.
    - rewrite (Ce _ _ _ H0); cbn; rewrite (Co _ _ _ H1); reflexivity.
    - (* a group *)
      rewrite (fill_raw_decl_fn_complete _ _ H0); reflexivity.
    - (* a mutual definition: its telescope, its heads, then its bodies *)
      rewrite (Ct _ _ _ H0); cbn [fill_result_bind]; rewrite (fill_rfun_heads_fn_complete _ _ _ H1);
        cbn [fill_result_bind].
      rewrite (fill_rfun_bodies_fn_complete _ _ _ _ _ _ _ _ _ _ _ H2 H3); reflexivity.
    - rewrite (Ct _ _ _ H0); cbn; rewrite (Ce _ _ _ H1); cbn; rewrite (fill_fields_fn_complete _ _ _ H2); reflexivity.
  Qed.

  (** A unit's parameters, likewise. *)
  Theorem fill_params_fn_sound : forall Δ Δ', fill_params_fn Δ = fill_ok Δ' -> fill_params Θ Ξ B Δ Δ'.
  Proof. intros * E; rewrite fill_params_fn_core in E; apply fill_tele_fn_sound; exact E. Qed.

  Theorem fill_params_fn_complete : forall Δ Δ', fill_params Θ Ξ B Δ Δ' -> fill_params_fn Δ = fill_ok Δ'.
  Proof.
    pose proof fill_fn_complete_all as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ct & _).
    intros * H; rewrite fill_params_fn_core; exact (Ct _ _ _ H).
  Qed.

  (** A record declaration's telescope, sort and fields filled. *)
  Definition fill_record_fn (x : string) (pv : bool) (Δ : ctx) (Srt : typ) (fs : list (string * typ)) (cs : list core_cmd) :
      fill_result (ctx * typ * list (string * typ))%type :=
    match fill_cmd_fn (core_cmd_record x pv Δ Srt fs cs) with
    | fill_ok (core_cmd_record _ _ Δ' Srt' fs' _) => fill_ok (Δ', Srt', fs')
    | fill_ok _ => fill_error (fill_failure_message "internal error: a record declaration filled to no record declaration")
    | fill_error e => fill_error e
    end.

  Lemma fill_cmd_record_inv : forall x pv Δ Srt fs cs c',
      fill_cmd Θ Ξ B (core_cmd_record x pv Δ Srt fs cs) c' -> exists Δ' Srt' fs', c' = core_cmd_record x pv Δ' Srt' fs' cs.
  Proof. intros * H; inversion H; subst; eauto. Qed.

  Lemma fill_record_fn_sound : forall x pv Δ Srt fs cs Δ' Srt' fs',
      fill_record_fn x pv Δ Srt fs cs = fill_ok (Δ', Srt', fs') ->
      fill_cmd Θ Ξ B (core_cmd_record x pv Δ Srt fs cs) (core_cmd_record x pv Δ' Srt' fs' cs).
  Proof.
    intros * E; unfold fill_record_fn in E.
    destruct (fill_cmd_fn (core_cmd_record x pv Δ Srt fs cs)) as [c' | e] eqn:Ef; [| discriminate ].
    pose proof (fill_cmd_fn_sound _ _ Ef) as Hf.
    destruct (fill_cmd_record_inv _ _ _ _ _ _ _ Hf) as (Δ0 & S0 & fs0 & ->).
    injection E as -> -> ->; exact Hf.
  Qed.

  Lemma fill_record_fn_complete : forall x pv Δ Srt fs cs Δ' Srt' fs',
      fill_cmd Θ Ξ B (core_cmd_record x pv Δ Srt fs cs) (core_cmd_record x pv Δ' Srt' fs' cs) ->
      fill_record_fn x pv Δ Srt fs cs = fill_ok (Δ', Srt', fs').
  Proof. intros * H; unfold fill_record_fn; rewrite (fill_cmd_fn_complete _ _ H); reflexivity. Qed.
End Decide.
