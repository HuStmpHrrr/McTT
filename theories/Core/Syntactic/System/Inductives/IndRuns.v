(** * An Accepted Declaration Runs

    For an inductive declaration [rc_ind] classifies, files and checks,
    the commands it generates always run ([rc_ind_runs]): each declared
    member's module, its constructors, the recursor [rec] of a group of
    one member, and the recursor module [Rec] ([ind_mod_cmds]); then, for
    a group declared by [mutual T where], [T.Rec] ([rec_cmds]).  So the
    premises of [rc_ind] up to [gen_names_free], with the members' names
    distinct and fresh, are enough for it to derive. *)

From Stdlib Require Import Lia List PeanoNat String Ascii DecimalNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Syntax.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Paths.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core.Syntactic.System.Inductives Require Import Runs GrecTyped.
Import Syntax_Notations Wk_Notations GlobalCtx_Notations.
#[local] Open Scope list_scope.

(** ** The Names of the Recursor Module's Functions Are Distinct *)

Lemma uint_string_inj : forall d1 d2, uint_string d1 = uint_string d2 -> d1 = d2.
Proof.
  induction d1; destruct d2; cbn; intros H; try discriminate; try reflexivity;
    injection H as H; f_equal; auto.
Qed.

Lemma string_app_inv_head : forall x s1 s2, (x ++ s1 = x ++ s2)%string -> s1 = s2.
Proof. induction x as [| a x IH]; cbn; intros * H; [ exact H | injection H as H; exact (IH _ _ H) ]. Qed.

Lemma string_length_app : forall x s, String.length (x ++ s)%string = String.length x + String.length s.
Proof. induction x as [| a x IH]; cbn; intros; [ reflexivity | rewrite IH; reflexivity ]. Qed.

(** The [n]-th candidate for the name [x]: [x], then [x_2], [x_3], …. *)
Definition grec_cand (x : string) (n : nat) : string :=
  match n with 0 => x | _ => (x ++ "_" ++ uint_string (Nat.to_uint (S n)))%string end.

Lemma grec_cand_inj : forall x n m, grec_cand x n = grec_cand x m -> n = m.
Proof.
  intros x [| n] [| m]; cbn [grec_cand]; intros H; try reflexivity.
  - apply (f_equal String.length) in H; rewrite string_length_app in H; cbn in H; lia.
  - apply (f_equal String.length) in H; rewrite string_length_app in H; cbn in H; lia.
  - apply string_app_inv_head in H; injection H as H; apply uint_string_inj in H.
    apply (f_equal Nat.of_uint) in H; rewrite !DecimalNat.Unsigned.of_to in H; lia.
Qed.

(** Trying the candidates from the [n]-th, [m] of them checked against
    [seen]: the search of [grec_fresh_names]. *)
Fixpoint grec_try (x : string) (seen : list string) (n m : nat) : string :=
  match m with
  | 0 => grec_cand x n
  | S m' => if List.existsb (String.eqb (grec_cand x n)) seen then grec_try x seen (S n) m' else grec_cand x n
  end.

Lemma grec_try_spec : forall x seen m n,
    ~ In (grec_try x seen n m) seen \/
    (grec_try x seen n m = grec_cand x (n + m) /\ forall j, n <= j < n + m -> In (grec_cand x j) seen).
Proof.
  intros x seen; induction m as [| m IH]; intros n; cbn [grec_try].
  - right; rewrite Nat.add_0_r; split; [ reflexivity | intros; lia ].
  - destruct (List.existsb (String.eqb (grec_cand x n)) seen) eqn:E.
    + destruct (IH (S n)) as [H | [H1 H2]]; [ left; exact H | right ].
      split; [ rewrite H1; f_equal; lia |].
      intros j Hj; destruct (Nat.eq_dec j n) as [-> |].
      * apply List.existsb_exists in E as (y & Hy & Hq); apply String.eqb_eq in Hq; subst y; exact Hy.
      * apply H2; lia.
    + left; intros Hin.
      assert (Hx : List.existsb (String.eqb (grec_cand x n)) seen = true)
        by (apply List.existsb_exists; exists (grec_cand x n); split; [ exact Hin | apply String.eqb_refl ]).
      rewrite Hx in E; discriminate.
Qed.

(** The candidate picked is new: by pigeonhole, as the first [|seen| + 1]
    candidates are distinct. *)
Lemma grec_try_new : forall x seen, ~ In (grec_try x seen 0 (List.length seen)) seen.
Proof.
  intros x seen; destruct (grec_try_spec x seen (List.length seen) 0) as [H | [H1 H2]]; [ exact H |].
  rewrite H1; cbn [Nat.add]; intros Hin.
  assert (Hnd : NoDup (List.map (grec_cand x) (List.seq 0 (S (List.length seen))))).
  { apply List.NoDup_map_NoDup_ForallPairs; [ intros n m _ _; apply grec_cand_inj | apply List.seq_NoDup ]. }
  assert (Hinc : incl (List.map (grec_cand x) (List.seq 0 (S (List.length seen)))) seen).
  { intros y Hy; apply List.in_map_iff in Hy as (j & <- & Hj); apply List.in_seq in Hj.
    destruct (Nat.eq_dec j (List.length seen)) as [-> | ]; [ exact Hin | apply H2; lia ]. }
  pose proof (NoDup_incl_length Hnd Hinc) as Hl; rewrite List.length_map, List.length_seq in Hl; lia.
Qed.

Lemma grec_fresh_names_cons : forall seen x xs,
    grec_fresh_names seen (x :: xs) =
      grec_try x seen 0 (List.length seen) :: grec_fresh_names (seen ++ grec_try x seen 0 (List.length seen) :: nil) xs.
Proof.
  intros seen x xs; cbn [grec_fresh_names].
  assert (H : forall n m, (fix try (n m : nat) {struct m} : string :=
             let cand := match n with 0 => x | _ => (x ++ "_" ++ uint_string (Nat.to_uint (S n)))%string end in
             match m with
             | 0 => cand
             | S m' => if List.existsb (String.eqb cand) seen then try (S n) m' else cand
             end) n m = grec_try x seen n m).
  { intros n m; revert n; induction m as [| m IH]; intros n; cbn; [ reflexivity |]; rewrite IH; reflexivity. }
  rewrite H; reflexivity.
Qed.

Lemma grec_fresh_names_nodup : forall xs seen, NoDup seen -> NoDup (seen ++ grec_fresh_names seen xs).
Proof.
  induction xs as [| x xs IH]; intros seen Hs; [ cbn; rewrite List.app_nil_r; exact Hs |].
  rewrite grec_fresh_names_cons.
  replace (seen ++ grec_try x seen 0 (List.length seen) :: grec_fresh_names (seen ++ grec_try x seen 0 (List.length seen) :: nil) xs)
    with ((seen ++ grec_try x seen 0 (List.length seen) :: nil) ++ grec_fresh_names (seen ++ grec_try x seen 0 (List.length seen) :: nil) xs)
    by (rewrite <- List.app_assoc; reflexivity).
  apply IH; apply NoDup_app; [ exact Hs | constructor; [ intros [] | constructor ] |].
  intros y Hy [<- | []]; exact (grec_try_new x seen Hy).
Qed.

Lemma length_grec_fresh_names : forall xs seen, List.length (grec_fresh_names seen xs) = List.length xs.
Proof. induction xs as [| x xs IH]; intros; [ reflexivity | rewrite grec_fresh_names_cons; cbn [List.length]; rewrite IH; reflexivity ]. Qed.

(** The functions' names are distinct, one per member. *)
Lemma grec_names_nodup : forall Θ Ξ D, NoDup (grec_names Θ Ξ D).
Proof.
  intros; unfold grec_names.
  apply List.NoDup_map_NoDup_ForallPairs; [ intros a b _ _ H; exact (string_app_inv_head _ _ _ H) |].
  exact (grec_fresh_names_nodup _ nil (NoDup_nil _)).
Qed.

Lemma length_grec_names : forall Θ Ξ D, List.length (grec_names Θ Ξ D) = List.length (ind_members D).
Proof. intros; unfold grec_names; rewrite List.length_map, length_grec_fresh_names, List.length_map; reflexivity. Qed.

(** ** The Recursor Module's Parameters Are Assumptions *)

Lemma grec_case_tys_ass : forall pq D ms i k, tele_ass (grec_case_tys pq D i k ms).
Proof.
  intros pq D ms; induction ms as [| M ms IH]; intros i k; [ constructor |].
  rewrite grec_case_tys_cons; apply List.Forall_app; split; [| apply IH ].
  generalize k; induction (im_cons M) as [| [c gs] cs IHc]; intros k'; cbn; constructor; [ eexists; reflexivity | apply IHc ].
Qed.

Lemma grec_tele_ass : forall pq D Δu, tele_ass Δu -> tele_ass (grec_tele pq D Δu).
Proof.
  intros * H; unfold grec_tele; apply List.Forall_app; split; [ apply List.Forall_rev, grec_case_tys_ass |].
  apply List.Forall_app; split; [| constructor; [ eexists; reflexivity | exact H ] ].
  apply List.Forall_rev; unfold grec_motive_tys; apply List.Forall_map, List.Forall_forall; intros; eexists; reflexivity.
Qed.

(** ** What the Declared Members Meet

    Shared with the checker ([Extraction.Command.members_step]). *)

(** The group [Dd] at [pq] is filed at the entry of its first declared
    member, in the innermost frame of [Ξ]: so the later members are
    checked. *)
#[warnings="-cannot-define-projection"]
Record first_filed (Ξ : gstack) (pq : qname) (Dd : ind_decl) : Prop := mk_first_filed
  { (** The innermost frame's path *)
    ff_frame : qname
    (** Its kind *)
  ; ff_kind : frame_kind
    (** Its parameters *)
  ; ff_params : ctx
    (** Its members so far *)
  ; ff_mod : gmod
    (** The frames outside it *)
  ; ff_rest : gstack
    (** The first declared member's name *)
  ; ff_name : string
    (** Whether that member is private *)
  ; ff_pv : bool
    (** The body of its module *)
  ; ff_body : gmod
    (** The stack is that frame on the others *)
  ; ff_stack : Ξ = (ff_frame, ff_kind, gu_body ff_params ff_mod) :: ff_rest
    (** The first member's entry is in it *)
  ; ff_entry : gm_entry ff_mod (ff_name :: nil) = Some (ge_ind ff_pv pq 0 Dd ff_body)
    (** The group is filed at that entry *)
  ; ff_at : pq = qname_in ff_frame ff_name }.

(** What the declared members [k], [k + 1], … of the group [Dd] at [pq],
    named [xs], meet at the stack [Ξ] they are filed from, read off the
    declaration: it is checked once, before the first member. *)
Record mems_pre (Ξ : gstack) (R : raw_decl) (pq : qname) (Dd : ind_decl) (k : nat) (xs : list string) : Prop :=
  mk_mems_pre
  { (** The group's uniform parameters are its own, over the frames' *)
    mp_uparams : ind_uparams Dd = (rd_uparams R ++ gs_tele Ξ)%list
    (** The names are distinct *)
  ; mp_nodup : List.NoDup xs
    (** and fresh *)
  ; mp_fresh : Forall (fun x => gs_fresh x Ξ) xs
    (** Each names its member *)
  ; mp_heads : forall i x, List.nth_error xs i = Some x ->
      exists M, ind_member Dd (k + i) = Some M /\ im_head M = mh_decl (ind_qname Ξ x)
    (** The members are declared ones *)
  ; mp_count : k + List.length xs <= ind_ndecl Dd
    (** The group is at the first member *)
  ; mp_first : k = 0 -> forall x xs', xs = x :: xs' -> pq = ind_qname Ξ x
    (** After the first member, the group is filed at its entry *)
  ; mp_later : 0 < k -> first_filed Ξ pq Dd }.

Lemma mems_fresh_head {Ξ R pq Dd k x xs} : mems_pre Ξ R pq Dd k (x :: xs) -> gs_fresh x Ξ.
Proof. intros Hp; exact (Forall_inv (mp_fresh _ _ _ _ _ _ Hp)). Qed.

(** After the member [k] is filed, the next ones meet the same. *)
Lemma mems_pre_tail {Ξ R pq Dd k x xs} : mems_pre Ξ R pq Dd k (x :: xs) ->
    forall pv Φ, mems_pre (gs_add x (ge_ind pv pq k Dd Φ) Ξ) R pq Dd (S k) xs.
Proof.
  intros [Hu Hnd Hfr Hh Hc Hf Hl] pv Φ.
  inversion Hnd as [| ? ? Hx Hnd']; subst; inversion Hfr as [| ? ? Hfx Hfr']; subst.
  constructor.
  - rewrite gs_tele_add; exact Hu.
  - exact Hnd'.
  - eapply Forall_impl; [| apply Forall_forall; intros y Hy; exact (conj (proj1 (Forall_forall _ _) Hfr' y Hy) Hy) ].
    intros y [Hy Hin]; apply gs_fresh_add; [ exact Hy | intros ->; exact (Hx Hin) ].
  - intros i y Hi; unfold ind_qname; rewrite gs_path_add.
    change (S k + i) with (S (k + i)); rewrite <- PeanoNat.Nat.add_succ_r; exact (Hh (S i) y Hi).
  - cbn [List.length] in Hc; change (S k + List.length xs) with (S (k + List.length xs));
      rewrite <- PeanoNat.Nat.add_succ_r; exact Hc.
  - intros [=].
  - intros _; destruct k as [| k].
    + pose proof (Hf eq_refl x xs eq_refl) as ->.
      destruct Ξ as [| [[mq Kq] [Δ Dq]] Ξ0]; [ contradiction |].
      apply (mk_first_filed _ _ _ mq Kq Δ (gu_mod (gu_mk Δ Dq) ⊳ x ↦ ge_ind pv (ind_qname ((mq, Kq, gu_mk Δ Dq) :: Ξ0) x) 0 Dd Φ)
               Ξ0 x pv Φ); [ reflexivity | cbn; rewrite String.eqb_refl; reflexivity | reflexivity ].
    + destruct (Hl ltac:(apply PeanoNat.Nat.lt_0_succ)) as [mq Kq Δ Φ0 Ξ0 y0 pv0 Φm -> He Hat].
      apply (mk_first_filed _ _ _ mq Kq Δ (Φ0 ⊳ x ↦ ge_ind pv pq (S k) Dd Φ) Ξ0 y0 pv0 Φm);
        [ reflexivity | apply gm_entry_ext_fresh; [ exact Hfx | exact He ] | exact Hat ].
Qed.

(** A filed declaration meets them from its first member on. *)
Lemma ind_mems_pre {Θ0 Ξ R Mr0 Mrs Vs Ss csD csV Nvs Dd} :
    rd_members R = Mr0 :: Mrs -> rd_filed Θ0 Ξ R Vs Ss csD csV Nvs = Some Dd ->
    List.NoDup (List.map rm_name (rd_members R)) -> Forall (fun Mr => gs_fresh (rm_name Mr) Ξ) (rd_members R) ->
    mems_pre Ξ R (ind_qname Ξ (rm_name Mr0)) Dd 0 (List.map rm_name (rd_members R)).
Proof.
  intros HR Hfil Hnd Hfr; destruct (rd_filed_decl _ _ _ _ _ _ _ _ _ Hfil) as [Hn Hh].
  constructor.
  - exact (rd_filed_uparams _ _ _ _ _ _ _ _ _ Hfil).
  - exact Hnd.
  - apply Forall_map; exact Hfr.
  - intros i x Hi; rewrite List.nth_error_map in Hi.
    destruct (List.nth_error (rd_members R) i) as [Mr |] eqn:Ei; [| discriminate ].
    injection Hi as <-; exact (Hh _ _ Ei).
  - rewrite List.length_map, Hn; reflexivity.
  - intros _ x xs; rewrite HR; intros [= <- _]; reflexivity.
  - intros Hk; exfalso; exact (PeanoNat.Nat.lt_irrefl _ Hk).
Qed.


(** ** Runs of Generated Commands *)
Section IndRuns.
  Variable load_path : path -> option string.
  Variable read : string -> option Cst.prog.
  Variable to_core : Cst.prog -> option cunit.

  (** A generated command run, then the rest: it is taken as generated,
      with no reference to check. *)
  Lemma run_gen_cons : forall ch B Rb Θ Ξ c cs B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_gen c ⇝ Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_gen c :: cs ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2.
  Proof.
    intros * H1 H2; eapply rcs_cons; [ constructor | reflexivity | exists nil; split; [ constructor | reflexivity ] | exact H1 | exact H2 ].
  Qed.

  Lemma run_cmds_app : forall ch cs1 cs2 B Rb Θ Ξ B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs1 ⇝* Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs2 ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs1 ++ cs2 ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2.
  Proof.
    intros ch cs1; induction cs1 as [| c cs1 IH]; intros * H1 H2; inversion H1; subst; [ exact H2 |].
    eapply rcs_cons; [ eassumption | eassumption | eassumption | eassumption | eapply IH; eassumption ].
  Qed.

  (** Generated definitions [ds], their names distinct and fresh in the
      innermost frame, each typed at every stack the frame grows to: they
      run, the frame growing by them. *)
  Lemma gen_defs_run : forall ch B Rb Θ mp K Δ Ξ0 b pv (ds : list (string * (typ * exp))) Φ,
      ⊢ᵍ Θ ⍮ (mp, K, gu_body Δ Φ) :: Ξ0 ->
      NoDup (List.map fst ds) -> Forall (fun d => gm_fresh (fst d) Φ) ds ->
      (forall Φ', ⊢ᵍ Θ ⍮ (mp, K, gu_body Δ Φ') :: Ξ0 -> gc_sub Θ ((mp, K, gu_body Δ Φ) :: Ξ0) Θ ((mp, K, gu_body Δ Φ') :: Ξ0) ->
         Forall (fun d => Θ ⍮ (mp, K, gu_body Δ Φ') :: Ξ0 ⍮ Δ ++ gs_tele Ξ0 ⊢ snd (snd d) : fst (snd d)) ds) ->
      exists Φ',
        Θ ⍮ (mp, K, gu_body Δ Φ) :: Ξ0 ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩
          List.map (fun d => cc_gen (cc_def (fst d) b pv (fst (snd d)) (Some (snd (snd d))))) ds ⇝*
          Θ ⍮ (mp, K, gu_body Δ Φ') :: Ξ0 ⍮ B ⍮ Rb /\
        ⊢ᵍ Θ ⍮ (mp, K, gu_body Δ Φ') :: Ξ0 /\
        gc_sub Θ ((mp, K, gu_body Δ Φ) :: Ξ0) Θ ((mp, K, gu_body Δ Φ') :: Ξ0) /\
        (forall y, gm_fresh y Φ -> ~ In y (List.map fst ds) -> gm_fresh y Φ').
  Proof.
    intros ch B Rb Θ mp K Δ Ξ0 b pv ds; induction ds as [| [x [A M]] ds IH]; intros Φ Hg Hnd Hfr Hty.
    - exists Φ; split; [ constructor | split; [ exact Hg | split; [ apply gc_sub_refl | auto ] ] ].
    - cbn [List.map fst snd] in *; inversion Hnd as [| ? ? Hx Hnd']; subst; inversion Hfr as [| ? ? Hx0 Hfr']; subst.
      pose proof (Hty Φ Hg (gc_sub_refl _ _)) as Hall; inversion Hall as [| ? ? HM _]; subst; cbn [fst snd] in HM.
      set (Φ1 := (Φ ⊳ x ↦ gs_def b pv ((mp, K, gu_body Δ Φ) :: Ξ0) A M)).
      assert (Hadd : gs_add x (gs_def b pv ((mp, K, gu_body Δ Φ) :: Ξ0) A M) ((mp, K, gu_body Δ Φ) :: Ξ0) = (mp, K, gu_body Δ Φ1) :: Ξ0)
        by reflexivity.
      assert (Hg1 : ⊢ᵍ Θ ⍮ (mp, K, gu_body Δ Φ1) :: Ξ0) by (rewrite <- Hadd; apply add_def_wf; [ exact Hg | exact HM | exact Hx0 ]).
      assert (Hs1 : gc_sub Θ ((mp, K, gu_body Δ Φ) :: Ξ0) Θ ((mp, K, gu_body Δ Φ1) :: Ξ0))
        by (rewrite <- Hadd; apply gc_sub_add; [ exact Hg | exact Hx0 ]).
      assert (Hfr1 : forall y, gm_fresh y Φ -> y <> x -> gm_fresh y Φ1)
        by (intros y Hy Hne; unfold Φ1, gm_fresh; cbn [gm_names]; intros [-> | Hin]; [ exact (Hne eq_refl) | exact (Hy Hin) ]).
      destruct (IH Φ1 Hg1 Hnd') as (Φ' & Hr & Hg' & Hs' & Hf').
      + apply Forall_forall; intros [y d] Hin; cbn [fst]; apply Hfr1; [ exact (proj1 (Forall_forall _ _) Hfr' _ Hin) |].
        intros ->; apply Hx; apply List.in_map_iff; exists (x, d); split; [ reflexivity | exact Hin ].
      + intros Φ2 Hg2 Hs2; pose proof (Hty Φ2 Hg2 (gc_sub_trans _ _ _ _ _ _ Hs1 Hs2)) as H; inversion H; assumption.
      + exists Φ'; split; [| split; [ exact Hg' | split; [ eapply gc_sub_trans; eassumption |] ] ].
        * eapply run_gen_cons; [| exact Hr ].
          rewrite <- Hadd; constructor; [ exact HM | exact Hx0 ].
        * intros y Hy Hn; apply Hf'; [ apply Hfr1; [ exact Hy | intros ->; apply Hn; left; reflexivity ] | intros Hin; apply Hn; right; exact Hin ].
  Qed.

  Lemma In_combine_seq : forall {X} (ms : list X) j M, In (j, M) (List.combine (List.seq 0 (List.length ms)) ms) -> List.nth_error ms j = Some M.
  Proof.
    intros * Hin; apply List.In_nth_error in Hin as [n Hn]; rewrite nth_error_combine_seq in Hn.
    destruct (List.nth_error ms n) eqn:E; cbn in Hn; [ injection Hn as <- <-; exact E | discriminate ].
  Qed.

  Lemma map_snd_combine_le : forall {X Y} (l1 : list X) (l2 : list Y), List.length l2 <= List.length l1 -> List.map snd (List.combine l1 l2) = l2.
  Proof. intros X Y l1; induction l1 as [| a l1 IH]; intros [| b l2] Hle; cbn in *; try reflexivity; [ lia | rewrite IH by lia; reflexivity ]. Qed.

  (** Where a group is found, it is typed and closed, over well-formed
      uniform parameters. *)
  Lemma group_facts : forall Θ Ξ pq D, ⊢ᵍ Θ ⍮ Ξ -> ind_lookup Θ Ξ pq = Some D ->
      decls_typed Θ Ξ /\ decl_typed Θ Ξ D /\ decl_closed D /\ ⊢ Θ ⍮ Ξ ⍮ ind_uparams D /\ tele_ass (ind_uparams D).
  Proof.
    intros * Hg Hl; pose proof (wf_ctx_empty _ _ Hg) as H0.
    destruct (decl_of_lookup _ _ _ _ _ H0 Hl) as [HD Hc]; destruct (decl_typed_uparams _ _ _ HD) as [HU Ha].
    exact (conj (decls_of_ctx _ _ _ H0) (conj HD (conj Hc (conj HU Ha)))).
  Qed.

  Lemma grec_tele_app : forall pq D Δu Γ,
      grec_tele pq D Δu ++ Γ = List.rev (grec_case_tys pq D 0 0 (ind_members D)) ++ List.rev (grec_motive_tys pq D) ++ ce_ass (a_level 0) :: (Δu ++ Γ).
  Proof. intros; unfold grec_tele; rewrite <- !List.app_assoc; reflexivity. Qed.

  (** The recursor module of a group found at [pq], at a stack over its
      uniform parameters [Δu], where [Rec] is fresh: it runs, whatever
      stack its names are read at. *)
  Lemma grec_mod_run : forall ch B Rb Θ Ξ pq D Δu Θ0 Ξ0,
      ⊢ᵍ Θ ⍮ Ξ -> ind_lookup Θ Ξ pq = Some D -> ind_uparams D = Δu ++ gs_tele Ξ -> gs_fresh "Rec" Ξ ->
      exists U, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ grec_mod_cmd Θ0 Ξ0 pq D Δu ⇝
        Θ ⍮ gs_add "Rec" (ge_body false (grec_tele pq D Δu) (gu_mod U)) Ξ ⍮ B ⍮ Rb.
  Proof.
    intros * Hg Hl Hu Hfr.
    destruct (group_facts _ _ _ _ Hg Hl) as (Hds & HD & Hc & HU & Ha).
    assert (HaΔ : tele_ass Δu) by (rewrite Hu in Ha; apply List.Forall_app in Ha; tauto).
    assert (HT : grec_tele pq D Δu ++ gs_tele Ξ = List.rev (grec_case_tys pq D 0 0 (ind_members D)) ++ List.rev (grec_motive_tys pq D) ++ ce_ass (a_level 0) :: ind_uparams D)
      by (rewrite grec_tele_app, Hu; reflexivity).
    destruct Ξ as [| [[mq Kq] Uq] Ξs]; [ contradiction |].
    set (Ξ := (mq, Kq, Uq) :: Ξs) in *.
    set (mr := qname_in (gs_path Ξ) "Rec").
    assert (Hpush : ⊢ᵍ Θ ⍮ (mr, fk_module, gu_body (grec_tele pq D Δu) ⋄) :: Ξ).
    { apply wf_gstack_cons; [ exact Hg | constructor; [ apply grec_tele_ass; exact HaΔ | rewrite HT; exact (CT_wf _ _ _ _ Hg Hds HD Hc Hl HU) ] |].
      cbn; exists "Rec"%string; split; [ reflexivity | exact Hfr ]. }
    set (ds := List.map (fun jx => let '(j, Mj, x) := jx in (x, (grec_fn_ty pq D j Mj, grec_fn pq D j Mj)))
                 (List.combine (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D)) (grec_names Θ0 Ξ0 D))).
    assert (Hcmds : List.map (fun jx => let '(j, Mj, x) := jx in cc_gen (cc_def x true false (grec_fn_ty pq D j Mj) (Some (grec_fn pq D j Mj))))
                      (List.combine (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D)) (grec_names Θ0 Ξ0 D))
                    = List.map (fun d => cc_gen (cc_def (fst d) true false (fst (snd d)) (Some (snd (snd d))))) ds).
    { unfold ds; rewrite List.map_map; apply List.map_ext; intros [[j Mj] x]; reflexivity. }
    assert (Hnames : List.map fst ds = grec_names Θ0 Ξ0 D).
    { unfold ds; rewrite List.map_map.
      transitivity (List.map snd (List.combine (List.combine (List.seq 0 (List.length (ind_members D))) (ind_members D)) (grec_names Θ0 Ξ0 D))).
      - apply List.map_ext; intros [[j Mj] x]; reflexivity.
      - apply map_snd_combine_le; rewrite List.length_combine, List.length_seq, length_grec_names; lia. }
    destruct (gen_defs_run ch B Rb Θ mr fk_module (grec_tele pq D Δu) Ξ true false ds ⋄ Hpush) as (Φ' & Hr & _).
    - rewrite Hnames; apply grec_names_nodup.
    - apply Forall_forall; intros; intros [].
    - intros Φ' Hg' Hs'.
      assert (Hl' : ind_lookup Θ ((mr, fk_module, gu_body (grec_tele pq D Δu) Φ') :: Ξ) pq = Some D).
      { eapply ind_lookup_gc_sub; [ exact Hs' |].
        eapply ind_lookup_gc_sub; [ apply gc_sub_push; exact (proj2 (proj2 (wf_gstack_cons_inv _ _ _ _ _ Hpush))) | exact Hl ]. }
      destruct (group_facts _ _ _ _ Hg' Hl') as (Hds' & HD' & _ & HU' & _).
      apply Forall_forall; intros d Hin; unfold ds in Hin; apply List.in_map_iff in Hin as ([[j Mj] x] & <- & Hin); cbn [fst snd].
      apply List.in_combine_l in Hin; apply In_combine_seq in Hin.
      rewrite HT.
      exact (grec_fn_typed _ _ _ _ Hg' Hds' HD' Hc Hl' HU' j Mj Hin).
    - exists (gu_body (grec_tele pq D Δu) Φ'); unfold grec_mod_cmd; rewrite Hcmds.
      eapply rc_gen_mod; [ apply grec_tele_ass; exact HaΔ | rewrite HT; exact (CT_wf _ _ _ _ Hg Hds HD Hc Hl HU) | exact Hfr | exact Hr ].
  Qed.

  (** A member's frame names its group, found where it is open. *)
  Lemma ind_frame_lookup : forall Θ mp pq k D U Ξ, ⊢ᵍ Θ ⍮ (mp, fk_ind pq k D, U) :: Ξ -> ind_lookup Θ ((mp, fk_ind pq k D, U) :: Ξ) pq = Some D.
  Proof. intros * Hg; eapply frame_ind_lookup; [ exact Hg |]; cbn [gs_find_ind]; rewrite qname_strip_refl; reflexivity. Qed.

  (** The module of a declared member [k], [M], well formed with an empty
      module where it is declared: its commands run in its frame, the
      constructors, then [rec], then [Rec], whatever stack the names of
      [Rec]'s functions are read at, when [rec] and [Rec] are no
      constructor of the first member ([gen_names_free]). *)
  Lemma ind_mod_run : forall ch B Rb Θ Ξ pv R pq D k x M pm Θ0 Ξ0,
      ⊢ᵍ Θ ⍮ Ξ -> ind_uparams D = rd_uparams R ++ gs_tele Ξ -> gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k D ⋄ ->
      ind_member D k = Some M -> im_head M = mh_decl pm ->
      (ind_has_rec D = true -> forall M0, ind_member D 0 = Some M0 -> ~ In "rec"%string (List.map fst (im_cons M0))) ->
      (rd_rec R = false -> forall M0, ind_member D 0 = Some M0 -> ~ In "Rec"%string (List.map fst (im_cons M0))) ->
      exists U, Θ ⍮ gs_push_ind (ind_qname Ξ x) pq k D (rd_uparams R) Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩
        ind_mod_cmds Θ0 Ξ0 R pq D k M ⇝* Θ ⍮ (ind_qname Ξ x, fk_ind pq k D, U) :: Ξ ⍮ B ⍮ Rb.
  Proof.
    intros * Hg Hu Hfr HE HM Hh Hrnc Hrmnc.
    destruct (ind_nil_entry_uparams _ _ _ _ _ _ _ _ HE Hu) as [Htel HΔ].
    destruct Ξ as [| [[mq Kq] Uq] Ξs]; [ contradiction |].
    set (Ξ := (mq, Kq, Uq) :: Ξs) in *.
    set (mp := ind_qname Ξ x); set (Δu := rd_uparams R); set (K := fk_ind pq k D).
    assert (Hpush : ⊢ᵍ Θ ⍮ (mp, K, gu_body Δu ⋄) :: Ξ).
    { apply wf_gstack_cons; [ exact Hg | eapply wf_gmod_ind_nil; eassumption |].
      cbn; exists x; split; [ reflexivity | exact Hfr ]. }
    assert (Hfacts : forall Φ', ⊢ᵍ Θ ⍮ (mp, K, gu_body Δu Φ') :: Ξ ->
              ind_lookup Θ ((mp, K, gu_body Δu Φ') :: Ξ) pq = Some D /\ decls_typed Θ ((mp, K, gu_body Δu Φ') :: Ξ) /\
              decl_typed Θ ((mp, K, gu_body Δu Φ') :: Ξ) D /\ decl_closed D /\ ⊢ Θ ⍮ (mp, K, gu_body Δu Φ') :: Ξ ⍮ ind_uparams D).
    { intros Φ' Hg'; pose proof (ind_frame_lookup _ _ _ _ _ _ _ Hg') as Hl.
      destruct (group_facts _ _ _ _ Hg' Hl) as (? & ? & ? & ? & _); tauto. }
    destruct (Hfacts ⋄ Hpush) as (_ & _ & HD & Hc & _).
    pose proof (dt_nodup _ _ _ HD _ _ HM) as Hnd.
    (* the constructors *)
    set (ds1 := List.map (fun cg => (fst cg, (ctx_pi (im_nparams M) (ctx_pi (cargs_ctx pq D M (snd cg)) (apps (a_ind pq k) (ind_pvars D M (List.length (snd cg))))),
                                            apps (a_con pq k (fst cg)) (vars_from 0 (ind_nu D))))) (im_cons M)).
    assert (Hn1 : List.map fst ds1 = List.map fst (im_cons M)) by (unfold ds1; rewrite List.map_map; reflexivity).
    destruct (gen_defs_run ch B Rb Θ mp K Δu Ξ true false ds1 ⋄ Hpush) as (Φ1 & Hr1 & Hg1 & _ & Hf1).
    { rewrite Hn1; exact Hnd. }
    { apply Forall_forall; intros; intros []. }
    { intros Φ' Hg' _; destruct (Hfacts Φ' Hg') as (Hl' & Hds' & HD' & _ & HU').
      apply Forall_forall; intros d Hin; unfold ds1 in Hin; apply List.in_map_iff in Hin as ([c gs] & <- & Hin); cbn [fst snd].
      change (Δu ++ gs_tele Ξ) with (gs_tele ((mp, K, gu_body Δu Φ') :: Ξ)) in *.
      cbn [gs_tele gu_params]; unfold Δu; rewrite <- Hu.
      exact (con_gen_typed _ _ _ _ _ _ _ _ _ Hg' Hds' HD' Hc Hl' HM Hh HU' (cons_lookup_nodup _ _ _ Hnd Hin)). }
    assert (HRec1 : (Nat.eqb k 0 && negb (rd_rec R))%bool = true -> gm_fresh "Rec" Φ1).
    { intros Hb; apply andb_prop in Hb as [Hk Hr]; apply Nat.eqb_eq in Hk; subst k; apply Bool.negb_true_iff in Hr.
      apply Hf1; [ intros [] | rewrite Hn1; exact (Hrmnc Hr M HM) ]. }
    (* the recursor, of a one-member group *)
    assert (Hrec : exists Φ2, Θ ⍮ (mp, K, gu_body Δu Φ1) :: Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ ind_rec_cmds pq D M ⇝*
                     Θ ⍮ (mp, K, gu_body Δu Φ2) :: Ξ ⍮ B ⍮ Rb /\ ⊢ᵍ Θ ⍮ (mp, K, gu_body Δu Φ2) :: Ξ /\
                     ((Nat.eqb k 0 && negb (rd_rec R))%bool = true -> gm_fresh "Rec" Φ2)).
    { unfold ind_rec_cmds; destruct (ind_has_rec D) eqn:Hhr; [| exists Φ1; split; [ constructor | split; [ exact Hg1 | exact HRec1 ] ] ].
      assert (Hone : ind_members D = M :: nil /\ k = 0).
      { unfold ind_has_rec in Hhr; apply Nat.eqb_eq in Hhr; unfold ind_member in HM.
        destruct (ind_members D) as [| M0 [| M1 Ms]]; cbn in Hhr; try discriminate.
        destruct k as [| [| k']]; cbn in HM; try discriminate; injection HM as <-; split; reflexivity. }
      destruct Hone as [Hone Hk0].
      destruct (gen_defs_run ch B Rb Θ mp K Δu Ξ true false (("rec"%string, (rec_ty pq D M, rec_fn pq D M)) :: nil) Φ1 Hg1)
        as (Φ2 & Hr2 & Hg2 & _ & Hf2).
      - constructor; [ intros [] | constructor ].
      - constructor; [| constructor ]; cbn [fst]; apply Hf1; [ intros [] |].
        rewrite Hn1; subst k; exact (Hrnc eq_refl M HM).
      - intros Φ' Hg' _; destruct (Hfacts Φ' Hg') as (Hl' & Hds' & HD' & _ & HU').
        constructor; [| constructor ]; cbn [fst snd]; cbn [gs_tele gu_params]; unfold Δu; rewrite <- Hu.
        exact (rec_typed _ _ _ _ _ _ Hg' Hds' HD' Hc Hl' Hone Hh HU').
      - exists Φ2; split; [ exact Hr2 | split; [ exact Hg2 |] ].
        intros Hb; apply Hf2; [ exact (HRec1 Hb) | cbn; intros [H | []]; discriminate H ]. }
    destruct Hrec as (Φ2 & Hr2 & Hg2 & HRec2).
    (* the recursor module, in the first member's module *)
    assert (Hgrec : exists U, Θ ⍮ (mp, K, gu_body Δu Φ2) :: Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ ind_grec_cmds Θ0 Ξ0 R pq D k ⇝*
                     Θ ⍮ (mp, K, U) :: Ξ ⍮ B ⍮ Rb).
    { unfold ind_grec_cmds; destruct ((Nat.eqb k 0 && negb (rd_rec R))%bool) eqn:Hb; [| exists (gu_body Δu Φ2); constructor ].
      destruct (grec_mod_run ch B Rb Θ ((mp, K, gu_body Δu Φ2) :: Ξ) pq D nil Θ0 Ξ0 Hg2 (proj1 (Hfacts _ Hg2))
                  ltac:(cbn [gs_tele gu_params List.app]; unfold Δu; exact Hu) (HRec2 eq_refl)) as [U HU].
      eexists; unfold grec_mod_cmd in HU |- *; eapply run_gen_cons; [ exact HU | constructor ]. }
    destruct Hgrec as [U Hr3].
    exists U; unfold ind_mod_cmds, gs_push_ind.
    eapply run_cmds_app; [| eapply run_cmds_app; [ exact Hr2 | exact Hr3 ] ].
    replace (List.map (ind_con_cmd pq D k M) (im_cons M))
      with (List.map (fun d => cc_gen (cc_def (fst d) true false (fst (snd d)) (Some (snd (snd d))))) ds1)
      by (unfold ds1; rewrite List.map_map; apply List.map_ext; intros [c gs]; reflexivity).
    exact Hr1.
  Qed.

  (** The declared members [k], [k + 1], … named [xs], the first well
      formed with an empty module where it is declared: each runs its
      module and is filed, the frames' parameters kept, and the names not
      among [xs] left fresh. *)
  Lemma ind_members_run : forall xs ch B Rb Θ Ξ pv R pq D k,
      ⊢ᵍ Θ ⍮ Ξ -> mems_pre Ξ R pq D k xs ->
      (forall x xs', xs = x :: xs' -> Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k D ⋄) ->
      (ind_has_rec D = true -> forall M0, ind_member D 0 = Some M0 -> ~ In "rec"%string (List.map fst (im_cons M0))) ->
      (rd_rec R = false -> forall M0, ind_member D 0 = Some M0 -> ~ In "Rec"%string (List.map fst (im_cons M0))) ->
      exists Ξ', run_ind_members load_path read to_core ch B Rb Θ Ξ pv R pq D k xs B Rb Θ Ξ' /\ ⊢ᵍ Θ ⍮ Ξ' /\
        gs_tele Ξ' = gs_tele Ξ /\ (forall y, gs_fresh y Ξ -> ~ In y xs -> gs_fresh y Ξ').
  Proof.
    induction xs as [| x xs IH]; intros * Hg Hp HE Hrnc Hrmnc.
    - exists Ξ; split; [ constructor | split; [ exact Hg | split; [ reflexivity | auto ] ] ].
    - pose proof (mems_fresh_head Hp) as Hfr; pose proof (mp_uparams _ _ _ _ _ _ Hp) as Hu.
      destruct (mp_heads _ _ _ _ _ _ Hp 0 x eq_refl) as (M & HM & Hh); rewrite Nat.add_0_r in HM.
      pose proof (HE x xs eq_refl) as HE0.
      destruct (ind_mod_run ch B Rb Θ Ξ pv R pq D k x M (ind_qname Ξ x) Θ (gs_push_ind (ind_qname Ξ x) pq k D (rd_uparams R) Ξ)
                  Hg Hu Hfr HE0 HM Hh Hrnc Hrmnc) as [U Hr].
      destruct (ind_member_run_gen load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hu Hfr HE0 Hr) as [_ _ _ Hg1 _].
      pose proof (mems_pre_tail Hp pv (gu_mod U)) as Hp1.
      destruct (IH ch B Rb Θ (gs_add x (ge_ind pv pq k D (gu_mod U)) Ξ) pv R pq D (S k) Hg1 Hp1) as (Ξ' & Hr' & Hg' & Ht' & Hf').
      + intros y ys ->.
        destruct (mp_later _ _ _ _ _ _ Hp1 ltac:(apply Nat.lt_0_succ)) as [mq Kq Δ Φ Ξ0 y0 pv0 Φm HΞ He Hat].
        destruct (mp_heads _ _ _ _ _ _ Hp1 0 y eq_refl) as (My & HMy & Hhy); rewrite Nat.add_0_r in HMy.
        pose proof (mp_count _ _ _ _ _ _ Hp1) as Hc; cbn [List.length] in Hc.
        pose proof (mp_uparams _ _ _ _ _ _ Hp1) as Hu1.
        rewrite HΞ in Hg1, Hhy, Hu1 |- *; rewrite Hat; rewrite Hat in He.
        eapply later_member_entry; [ exact Hg1 | exact He | exact HMy | apply Nat.lt_0_succ | lia | exact Hhy | exact Hu1 ].
      + exact Hrnc.
      + exact Hrmnc.
      + exists Ξ'; split; [ econstructor; [ exact HM | exact Hfr | exact HE0 | exact Hr | exact Hr' ] | split; [ exact Hg' |] ].
        split; [ rewrite Ht', gs_tele_add; reflexivity |].
        intros y Hy Hn; apply Hf'; [ apply gs_fresh_add; [ exact Hy | intros ->; apply Hn; left; reflexivity ] | intros Hin; apply Hn; right; exact Hin ].
  Qed.

  (** ** An Accepted Declaration Runs

      A group [rc_ind] classifies, files, checks at its views' instances
      and finds its generated names free, its members' names distinct and
      fresh: its declared members run, each with its module, then, for a
      group declared by [mutual T where], [T.Rec]; so [rc_ind] derives. *)
  Theorem rc_ind_runs : forall ch B Rb Θ Ξ pv R Mr0 Mrs csD Vs Ss csV Nvs D,
      ⊢ᵍ Θ ⍮ Ξ ->
      rd_members R = Mr0 :: Mrs ->
      Forall (fun Mr => rm_sort Mr = rm_sort Mr0) Mrs ->
      Forall2 (rm_cls Θ Ξ R) (rd_members R) csD ->
      Forall2 (view_sibs Θ Ξ R) Vs Ss ->
      Forall2 (view_cls Θ Ξ R) Vs csV ->
      Forall2 (view_nps Θ Ξ R) Vs Nvs ->
      views_bfs (sibs_tbl Vs Ss) (meets_tbl Vs csV) nil (List.concat (List.map rcons_views csD)) Vs ->
      rd_filed Θ Ξ R Vs Ss csD csV Nvs = Some D ->
      ind_nil_at Θ Ξ (ind_qname Ξ (rm_name Mr0)) D (grp_self_insts (ind_qname Ξ (rm_name Mr0)) D) ->
      gen_names_free Ξ R D ->
      List.NoDup (List.map rm_name (rd_members R)) -> Forall (fun Mr => gs_fresh (rm_name Mr) Ξ) (rd_members R) ->
      exists Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cc_ind pv R ⇝ Θ ⍮ Ξ' ⍮ B ⍮ Rb.
  Proof.
    intros * Hg HR Hs Hcls Hsibs Hvcls Hnps Hbfs Hfil Hnil Hgn Hnd Hfr.
    set (pq := ind_qname Ξ (rm_name Mr0)).
    pose proof (ind_mems_pre HR Hfil Hnd Hfr) as Hp.
    pose proof (mp_uparams _ _ _ _ _ _ Hp) as Hu.
    destruct (ind_members_run (List.map rm_name (rd_members R)) ch B Rb Θ Ξ pv R pq D 0 Hg Hp) as (Ξ1 & Hr1 & Hg1 & Ht1 & Hf1).
    { rewrite HR; cbn [List.map]; intros x xs [= <- _]; exact (ind_nil_at_entry _ _ _ _ _ Hnil pv). }
    { exact (rec_not_constructor _ _ _ Hgn). }
    { exact (rec_module_not_constructor _ _ _ Hgn). }
    assert (Hrec : exists Ξ2, Θ ⍮ Ξ1 ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ rec_cmds Θ Ξ1 R pq D ⇝* Θ ⍮ Ξ2 ⍮ B ⍮ Rb).
    { unfold rec_cmds; destruct (rd_rec R) eqn:Hrr; [| exists Ξ1; constructor ].
      assert (Hl1 : ind_lookup Θ Ξ1 pq = Some D).
      { rewrite HR in Hr1; cbn [List.map] in Hr1; exact (ind_members_run_lookup load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr1 Hg Hu). }
      destruct (grec_mod_run ch B Rb Θ Ξ1 pq D (rd_uparams R) Θ Ξ1 Hg1 Hl1 ltac:(rewrite Ht1; exact Hu)
                  (Hf1 _ (mutual_rec_fresh _ _ _ Hgn Hrr) (mutual_rec_not_member _ _ _ Hgn Hrr))) as [U HU].
      eexists; unfold grec_mod_cmd in HU |- *; eapply run_gen_cons; [ exact HU | constructor ]. }
    destruct Hrec as [Ξ2 Hr2].
    exists Ξ2; eapply rc_ind; eassumption.
  Qed.
End IndRuns.
