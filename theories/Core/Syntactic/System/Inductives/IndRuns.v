(** * An Accepted Declaration Runs

    For an inductive declaration [run_cmd_ind_case] classifies, files and checks,
    the commands it generates always run ([run_cmd_ind_runs]): each declared
    member's module, its constructors, the recursor [rec] of a group of
    one member, and the recursor module [Rec] ([ind_mod_cmds]); then, for
    a group declared by [mutual T where], [T.Rec] ([rec_cmds]).  So the
    premises of [run_cmd_ind_case] up to [gen_names_free], with the members' names
    distinct and fresh, are enough for it to derive. *)

From Stdlib Require Import Lia List PeanoNat String Ascii DecimalNat.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import SystemOpt.
From Mctt.Core.Syntactic.System Require Import Scoping.
From Mctt.Core.Syntactic.System.Global Require Import Presup.
From Mctt.Core.Syntactic.System.Inductives Require Import Typing Syntax.
From Mctt.Core.Syntactic.System.Global Require Import MemberLemmas Paths LookupSound.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core.Syntactic.System.Inductives Require Import Runs GrecTyped.
From Mctt.Algorithmic.Typing Require Import Definitions Lemmas.
From Mctt.Core.Completeness.Consequences Require Import Types.
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
Definition recursor_candidate (x : string) (n : nat) : string :=
  match n with 0 => x | _ => (x ++ "_" ++ uint_string (Nat.to_uint (S n)))%string end.

Lemma recursor_candidate_inj : forall x n m, recursor_candidate x n = recursor_candidate x m -> n = m.
Proof.
  intros x [| n] [| m]; cbn [recursor_candidate]; intros H; try reflexivity.
  - apply (f_equal String.length) in H; rewrite string_length_app in H; cbn in H; lia.
  - apply (f_equal String.length) in H; rewrite string_length_app in H; cbn in H; lia.
  - apply string_app_inv_head in H; injection H as H; apply uint_string_inj in H.
    apply (f_equal Nat.of_uint) in H; rewrite !DecimalNat.Unsigned.of_to in H; lia.
Qed.

(** Trying the candidates from the [n]-th, [m] of them checked against
    [seen]: the search of [recursor_fresh_names]. *)
Fixpoint recursor_try (x : string) (seen : list string) (n m : nat) : string :=
  match m with
  | 0 => recursor_candidate x n
  | S m' => if List.existsb (String.eqb (recursor_candidate x n)) seen then recursor_try x seen (S n) m' else recursor_candidate x n
  end.

Lemma recursor_try_spec : forall x seen m n,
    ~ In (recursor_try x seen n m) seen \/
    (recursor_try x seen n m = recursor_candidate x (n + m) /\ forall j, n <= j < n + m -> In (recursor_candidate x j) seen).
Proof.
  intros x seen; induction m as [| m IH]; intros n; cbn [recursor_try].
  - right; rewrite Nat.add_0_r; split; [ reflexivity | intros; lia ].
  - destruct (List.existsb (String.eqb (recursor_candidate x n)) seen) eqn:E.
    + destruct (IH (S n)) as [H | [H1 H2]]; [ left; exact H | right ].
      split; [ rewrite H1; f_equal; lia |].
      intros j Hj; destruct (Nat.eq_dec j n) as [-> |].
      * apply List.existsb_exists in E as (y & Hy & Hq); apply String.eqb_eq in Hq; subst y; exact Hy.
      * apply H2; lia.
    + left; intros Hin.
      assert (Hx : List.existsb (String.eqb (recursor_candidate x n)) seen = true)
        by (apply List.existsb_exists; exists (recursor_candidate x n); split; [ exact Hin | apply String.eqb_refl ]).
      rewrite Hx in E; discriminate.
Qed.

(** The candidate picked is new: by pigeonhole, as the first [|seen| + 1]
    candidates are distinct. *)
Lemma recursor_try_new : forall x seen, ~ In (recursor_try x seen 0 (List.length seen)) seen.
Proof.
  intros x seen; destruct (recursor_try_spec x seen (List.length seen) 0) as [H | [H1 H2]]; [ exact H |].
  rewrite H1; cbn [Nat.add]; intros Hin.
  assert (Hnd : NoDup (List.map (recursor_candidate x) (List.seq 0 (S (List.length seen))))).
  { apply List.NoDup_map_NoDup_ForallPairs; [ intros n m _ _; apply recursor_candidate_inj | apply List.seq_NoDup ]. }
  assert (Hinc : incl (List.map (recursor_candidate x) (List.seq 0 (S (List.length seen)))) seen).
  { intros y Hy; apply List.in_map_iff in Hy as (j & <- & Hj); apply List.in_seq in Hj.
    destruct (Nat.eq_dec j (List.length seen)) as [-> | ]; [ exact Hin | apply H2; lia ]. }
  pose proof (NoDup_incl_length Hnd Hinc) as Hl; rewrite List.length_map, List.length_seq in Hl; lia.
Qed.

Lemma recursor_fresh_names_cons : forall seen x xs,
    recursor_fresh_names seen (x :: xs) =
      recursor_try x seen 0 (List.length seen) :: recursor_fresh_names (seen ++ recursor_try x seen 0 (List.length seen) :: nil) xs.
Proof.
  intros seen x xs; cbn [recursor_fresh_names].
  assert (H : forall n m, (fix try (n m : nat) {struct m} : string :=
             let cand := match n with 0 => x | _ => (x ++ "_" ++ uint_string (Nat.to_uint (S n)))%string end in
             match m with
             | 0 => cand
             | S m' => if List.existsb (String.eqb cand) seen then try (S n) m' else cand
             end) n m = recursor_try x seen n m).
  { intros n m; revert n; induction m as [| m IH]; intros n; cbn; [ reflexivity |]; rewrite IH; reflexivity. }
  rewrite H; reflexivity.
Qed.

Lemma recursor_fresh_names_nodup : forall xs seen, NoDup seen -> NoDup (seen ++ recursor_fresh_names seen xs).
Proof.
  induction xs as [| x xs IH]; intros seen Hs; [ cbn; rewrite List.app_nil_r; exact Hs |].
  rewrite recursor_fresh_names_cons.
  replace (seen ++ recursor_try x seen 0 (List.length seen) :: recursor_fresh_names (seen ++ recursor_try x seen 0 (List.length seen) :: nil) xs)
    with ((seen ++ recursor_try x seen 0 (List.length seen) :: nil) ++ recursor_fresh_names (seen ++ recursor_try x seen 0 (List.length seen) :: nil) xs)
    by (rewrite <- List.app_assoc; reflexivity).
  apply IH; apply NoDup_app; [ exact Hs | constructor; [ intros [] | constructor ] |].
  intros y Hy [<- | []]; exact (recursor_try_new x seen Hy).
Qed.

Lemma length_recursor_fresh_names : forall xs seen, List.length (recursor_fresh_names seen xs) = List.length xs.
Proof. induction xs as [| x xs IH]; intros; [ reflexivity | rewrite recursor_fresh_names_cons; cbn [List.length]; rewrite IH; reflexivity ]. Qed.

(** The functions' names are distinct, one per member. *)
Lemma recursor_names_nodup : forall Θ Ξ D, NoDup (recursor_names Θ Ξ D).
Proof.
  intros; unfold recursor_names.
  apply List.NoDup_map_NoDup_ForallPairs; [ intros a b _ _ H; exact (string_app_inv_head _ _ _ H) |].
  exact (recursor_fresh_names_nodup _ nil (NoDup_nil _)).
Qed.

Lemma length_recursor_names : forall Θ Ξ D, List.length (recursor_names Θ Ξ D) = List.length (ind_block_members D).
Proof. intros; unfold recursor_names; rewrite List.length_map, length_recursor_fresh_names, List.length_map; reflexivity. Qed.

(** ** The Recursor Module's Parameters Are Assumptions *)

Lemma recursor_case_tys_ass : forall pq D ms i k, all_assumptions (recursor_case_tys pq D i k ms).
Proof.
  intros pq D ms; induction ms as [| M ms IH]; intros i k; [ constructor |].
  rewrite recursor_case_tys_cons; apply List.Forall_app; split; [| apply IH ].
  generalize k; induction (im_cons M) as [| [c gs] cs IHc]; intros k'; cbn;
    [ constructor | constructor; [ do 2 eexists; reflexivity | apply IHc ] ].
Qed.

Lemma recursor_tele_all_assumptions : forall pq D Δu, all_assumptions Δu -> all_assumptions (recursor_tele pq D Δu).
Proof.
  intros * H; unfold recursor_tele; apply List.Forall_app; split; [ apply List.Forall_rev, recursor_case_tys_ass |].
  apply List.Forall_app; split; [| constructor; [ do 2 eexists; reflexivity | exact H ] ].
  apply List.Forall_rev; unfold recursor_motive_tys; apply List.Forall_map, List.Forall_forall; intros; do 2 eexists; reflexivity.
Qed.

(** ** What the Declared Members Meet

    Shared with the checker ([Extraction.Command.members_step]). *)

(** The group [Dd] at [pq] is filed at the entry of its first declared
    member, in the innermost frame of [Ξ]: so the later members are
    checked. *)
#[warnings="-cannot-define-projection"]
Record first_filed (Ξ : gstack) (pq : qname) (Dd : ind_decl) : Prop := mk_first_filed
  { (** The innermost frame's path *)
    first_filed_frame : qname
    (** Its kind *)
  ; first_filed_kind : frame_kind
    (** Its parameters *)
  ; first_filed_params : ctx
    (** Its members so far *)
  ; first_filed_mod : gmod
    (** The frames outside it *)
  ; first_filed_rest : gstack
    (** The first declared member's name *)
  ; first_filed_name : string
    (** Whether that member is private *)
  ; first_filed_pv : bool
    (** The body of its module *)
  ; first_filed_body : gmod
    (** The stack is that frame on the others *)
  ; first_filed_stack : Ξ = (first_filed_frame, first_filed_kind, gu_body first_filed_params first_filed_mod) :: first_filed_rest
    (** The first member's entry is in it *)
  ; first_filed_entry : gm_entry first_filed_mod (first_filed_name :: nil) = Some (ge_ind first_filed_pv pq 0 Dd first_filed_body)
    (** The group is filed at that entry *)
  ; first_filed_at : pq = qname_in first_filed_frame first_filed_name }.

(** What the declared members [k], [k + 1], … of the group [Dd] at [pq],
    named [xs], meet at the stack [Ξ] they are filed from, read off the
    declaration: it is checked once, before the first member. *)
Record mems_pre (Ξ : gstack) (R : raw_decl) (pq : qname) (Dd : ind_decl) (k : nat) (xs : list string) : Prop :=
  mk_mems_pre
  { (** The group's uniform parameters are its own, over the frames' *)
    mems_pre_uparams : ind_uparams Dd = (raw_decl_uparams R ++ gs_tele Ξ)%list
    (** The names are distinct *)
  ; mems_pre_nodup : List.NoDup xs
    (** and fresh *)
  ; mems_pre_fresh : Forall (fun x => gs_fresh x Ξ) xs
    (** Each names its member *)
  ; mems_pre_heads : forall i x, List.nth_error xs i = Some x ->
      exists M, ind_member Dd (k + i) = Some M /\ im_head M = mh_decl (ind_qname Ξ x)
    (** The members are declared ones *)
  ; mems_pre_count : k + List.length xs <= ind_ndecl Dd
    (** The group is at the first member *)
  ; mems_pre_first : k = 0 -> forall x xs', xs = x :: xs' -> pq = ind_qname Ξ x
    (** After the first member, the group is filed at its entry *)
  ; mems_pre_later : 0 < k -> first_filed Ξ pq Dd }.

Lemma mems_fresh_head {Ξ R pq Dd k x xs} : mems_pre Ξ R pq Dd k (x :: xs) -> gs_fresh x Ξ.
Proof. intros Hp; exact (Forall_inv (mems_pre_fresh _ _ _ _ _ _ Hp)). Qed.

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
    raw_decl_members R = Mr0 :: Mrs -> raw_decl_filed Θ0 Ξ R Vs Ss csD csV Nvs = Some Dd ->
    List.NoDup (List.map raw_member_name (raw_decl_members R)) -> Forall (fun Mr => gs_fresh (raw_member_name Mr) Ξ) (raw_decl_members R) ->
    mems_pre Ξ R (ind_qname Ξ (raw_member_name Mr0)) Dd 0 (List.map raw_member_name (raw_decl_members R)).
Proof.
  intros HR Hfil Hnd Hfr; destruct (raw_decl_filed_decl _ _ _ _ _ _ _ _ _ Hfil) as [Hn Hh].
  constructor.
  - exact (raw_decl_filed_uparams _ _ _ _ _ _ _ _ _ Hfil).
  - exact Hnd.
  - apply Forall_map; exact Hfr.
  - intros i x Hi; rewrite List.nth_error_map in Hi.
    destruct (List.nth_error (raw_decl_members R) i) as [Mr |] eqn:Ei; [| discriminate ].
    injection Hi as <-; exact (Hh _ _ Ei).
  - rewrite List.length_map, Hn; reflexivity.
  - intros _ x xs; rewrite HR; intros [= <- _]; reflexivity.
  - intros Hk; exfalso; exact (PeanoNat.Nat.lt_irrefl _ Hk).
Qed.


(** ** Runs of Generated Commands *)

(** A generated definition, as its command files it. *)
Record gen_def : Set := mk_gen_def
  { (** The name it is filed at *)
    gen_def_name : string
    (** The kind of its type *)
  ; gen_def_kind : abs_kind
    (** Its type *)
  ; gen_def_type : typ
    (** Its body *)
  ; gen_def_body : exp }.

(** The core command filing the generated definition [d], transparent
    when [b], private when [pv]. *)
Definition gen_def_cmd (b pv : bool) (d : gen_def) : core_cmd :=
  core_cmd_def (gen_def_name d) b pv (gen_def_kind d) (gen_def_type d) (Some (gen_def_body d)).

Section IndRuns.
  Variable load_path : path -> option string.
  Variable read : string -> option Cst.prog.
  Variable to_core : Cst.prog -> option surface_compilation_unit.

  (** A run of a list of items, then of another: a run of both, one
      after the other. *)
  Lemma run_cmds_concat : forall ch cs1 cs2 B Rb Θ Ξ B1 Rb1 Θ1 Ξ1 B2 Rb2 Θ2 Ξ2,
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs1 ⇝* Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ->
      Θ1 ⍮ Ξ1 ⍮ B1 ⍮ Rb1 ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs2 ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2 ->
      Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ cs1 ++ cs2 ⇝* Θ2 ⍮ Ξ2 ⍮ B2 ⍮ Rb2.
  Proof.
    intros ch cs1; induction cs1 as [| c cs1 IH]; intros * H1 H2; inversion H1; subst; [ exact H2 | |].
    - eapply run_cmds_written; [ eassumption | eassumption | eassumption | eapply IH; eassumption ].
    - eapply run_cmds_core; [ eassumption | eapply IH; eassumption ].
  Qed.

  (** Generated definitions [ds], their names distinct and fresh in the
      innermost frame, none of a type of levels, each typed at every stack
      the frame grows to, its type of its kind's sort: they run, the frame
      growing by them. *)
  Lemma gen_defs_run : forall ch B Rb Θ mp K Δ Ξ0 b pv (ds : list gen_def) Φ,
      ⊢ᵍ Θ ⍮ (mp, K, gu_body Δ Φ) :: Ξ0 ->
      NoDup (List.map gen_def_name ds) -> Forall (fun d => gm_fresh (gen_def_name d) Φ) ds ->
      Forall (fun d => gen_def_kind d <> ak_level) ds ->
      (forall Φ', ⊢ᵍ Θ ⍮ (mp, K, gu_body Δ Φ') :: Ξ0 -> gc_sub Θ ((mp, K, gu_body Δ Φ) :: Ξ0) Θ ((mp, K, gu_body Δ Φ') :: Ξ0) ->
         Forall (fun d => (exists i : nat, Θ ⍮ (mp, K, gu_body Δ Φ') :: Ξ0 ⍮ Δ ++ gs_tele Ξ0 ⊢ gen_def_type d : abs_kind_sort (gen_def_kind d) Typeω@i) /\
                          Θ ⍮ (mp, K, gu_body Δ Φ') :: Ξ0 ⍮ Δ ++ gs_tele Ξ0 ⊢ gen_def_body d : gen_def_type d) ds) ->
      exists Φ',
        Θ ⍮ (mp, K, gu_body Δ Φ) :: Ξ0 ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩
          List.map (fun d => ci_core (gen_def_cmd b pv d)) ds ⇝*
          Θ ⍮ (mp, K, gu_body Δ Φ') :: Ξ0 ⍮ B ⍮ Rb /\
        ⊢ᵍ Θ ⍮ (mp, K, gu_body Δ Φ') :: Ξ0 /\
        gc_sub Θ ((mp, K, gu_body Δ Φ) :: Ξ0) Θ ((mp, K, gu_body Δ Φ') :: Ξ0) /\
        (forall y, gm_fresh y Φ -> ~ In y (List.map gen_def_name ds) -> gm_fresh y Φ').
  Proof.
    intros ch B Rb Θ mp K Δ Ξ0 b pv ds; induction ds as [| [x κ A M] ds IH]; intros Φ Hg Hnd Hfr Hk Hty.
    - exists Φ; split; [ constructor | split; [ exact Hg | split; [ apply gc_sub_refl | auto ] ] ].
    - cbn [List.map gen_def_name gen_def_kind gen_def_type gen_def_body] in *.
      inversion Hnd as [| ? ? Hx Hnd']; subst; inversion Hfr as [| ? ? Hx0 Hfr']; subst.
      inversion Hk as [| ? ? Hκ Hk']; subst.
      pose proof (Hty Φ Hg (gc_sub_refl _ _)) as Hall; inversion Hall as [| ? ? [[i HAr] HM] _]; subst.
      cbn [gen_def_name gen_def_kind gen_def_type gen_def_body] in Hκ, HAr, HM.
      assert (Hlv : κ = ak_level -> level_sorted_parameters (gs_tele ((mp, K, gu_body Δ Φ) :: Ξ0))) by (intros E; contradiction).
      set (Φ1 := (Φ ⊳ x ↦ gs_def b pv κ ((mp, K, gu_body Δ Φ) :: Ξ0) A M)).
      assert (Hadd : gs_add x (gs_def b pv κ ((mp, K, gu_body Δ Φ) :: Ξ0) A M) ((mp, K, gu_body Δ Φ) :: Ξ0) = (mp, K, gu_body Δ Φ1) :: Ξ0)
        by reflexivity.
      assert (Hg1 : ⊢ᵍ Θ ⍮ (mp, K, gu_body Δ Φ1) :: Ξ0)
        by (rewrite <- Hadd; eapply add_def_wf; [ exact Hg | exact HAr | exact Hlv | exact HM | exact Hx0 ]).
      assert (Hs1 : gc_sub Θ ((mp, K, gu_body Δ Φ) :: Ξ0) Θ ((mp, K, gu_body Δ Φ1) :: Ξ0))
        by (rewrite <- Hadd; apply gc_sub_add; [ exact Hg | exact Hx0 ]).
      assert (Hfr1 : forall y, gm_fresh y Φ -> y <> x -> gm_fresh y Φ1)
        by (intros y Hy Hne; unfold Φ1, gm_fresh; cbn [gm_names]; intros [-> | Hin]; [ exact (Hne eq_refl) | exact (Hy Hin) ]).
      destruct (IH Φ1 Hg1 Hnd') as (Φ' & Hr & Hg' & Hs' & Hf').
      + apply Forall_forall; intros d Hin; apply Hfr1; [ exact (proj1 (Forall_forall _ _) Hfr' _ Hin) |].
        intros E; apply Hx; apply List.in_map_iff; exists d; split; [ exact E | exact Hin ].
      + exact Hk'.
      + intros Φ2 Hg2 Hs2; pose proof (Hty Φ2 Hg2 (gc_sub_trans _ _ _ _ _ _ Hs1 Hs2)) as H; inversion H; assumption.
      + exists Φ'; split; [| split; [ exact Hg' | split; [ eapply gc_sub_trans; eassumption |] ] ].
        * eapply run_cmds_core; [| exact Hr ].
          rewrite <- Hadd; unfold gen_def_cmd; cbn [gen_def_name gen_def_kind gen_def_type gen_def_body].
          eapply run_cmd_def; [ exact HAr | exact Hlv | exact HM | exact Hx0 ].
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
      decls_typed Θ Ξ /\ decl_typed Θ Ξ D /\ decl_closed D /\ ⊢ Θ ⍮ Ξ ⍮ ind_uparams D /\ all_assumptions (ind_uparams D).
  Proof.
    intros * Hg Hl; pose proof (wf_ctx_empty _ _ Hg) as H0.
    destruct (decl_of_lookup _ _ _ _ _ H0 Hl) as [HD Hc]; destruct (decl_typed_uparams _ _ _ HD) as [HU Ha].
    exact (conj (decls_of_ctx _ _ _ H0) (conj HD (conj Hc (conj HU Ha)))).
  Qed.

  Lemma recursor_tele_app : forall pq D Δu Γ,
      recursor_tele pq D Δu ++ Γ = List.rev (recursor_case_tys pq D 0 0 (ind_block_members D)) ++ List.rev (recursor_motive_tys pq D) ++ ce_ass ak_level (a_level 0) :: (Δu ++ Γ).
  Proof. intros; unfold recursor_tele; rewrite <- !List.app_assoc; reflexivity. Qed.

  (** The recursor module of a group found at [pq], at a stack over its
      uniform parameters [Δu], where [Rec] is fresh: it runs, whatever
      stack its names are read at. *)
  Lemma recursor_mod_run : forall ch B Rb Θ Ξ pq D Δu lu Θ0 Ξ0,
      ⊢ᵍ Θ ⍮ Ξ -> ind_lookup Θ Ξ pq = Some D -> ind_uparams D = Δu ++ gs_tele Ξ -> gs_fresh "Rec" Ξ ->
      params_evaluated Θ Ξ (gs_tele Ξ) Δu lu ->
      exists U, Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ List.map ci_core (recursor_mod_cmds Θ0 Ξ0 pq D Δu) ⇝*
        Θ ⍮ gs_add "Rec" (ge_body false (recursor_tele pq D Δu) (gu_mod U)) Ξ ⍮ B ⍮ Rb.
  Proof.
    intros * Hg Hl Hu Hfr HRu.
    destruct (group_facts _ _ _ _ Hg Hl) as (Hds & HD & Hc & HU & Ha).
    assert (HaΔ : all_assumptions Δu) by (rewrite Hu in Ha; apply List.Forall_app in Ha; tauto).
    assert (HT : recursor_tele pq D Δu ++ gs_tele Ξ = List.rev (recursor_case_tys pq D 0 0 (ind_block_members D)) ++ List.rev (recursor_motive_tys pq D) ++ ce_ass ak_level (a_level 0) :: ind_uparams D)
      by (rewrite recursor_tele_app, Hu; reflexivity).
    (** The telescope's types are types of universes or of levels: the
        uniform parameters', the level's, the motives' and the cases'. *)
    assert (HRt : exists lr, params_evaluated Θ Ξ (gs_tele Ξ) (recursor_tele pq D Δu) lr).
    { destruct (MT_evaluated _ _ _ _ Hg Hds HD Hc Hl HU) as [lm Hm].
      destruct (CT_evaluated _ _ _ _ Hg Hds HD Hc Hl HU) as [lc Hcs].
      assert (HL : params_evaluated Θ Ξ (Δu ++ gs_tele Ξ) (ce_ass ak_level (a_level 0) :: nil) 0).
      { intros [| e Δ1] κ T Δ2 E; cbn in E; [ injection E as <- <- <-; cbn; right; apply wf_level; rewrite <- Hu; exact HU
                                           | destruct Δ1; discriminate ]. }
      pose proof (params_evaluated_app _ _ _ _ _ _ _ HL HRu) as H1.
      rewrite Hu in Hm, Hcs.
      pose proof (params_evaluated_app _ _ (gs_tele Ξ) _ (ce_ass ak_level (a_level 0) :: Δu) _ _ Hm H1) as H2.
      assert (Hcs' : params_evaluated Θ Ξ ((List.rev (recursor_motive_tys pq D) ++ ce_ass ak_level (a_level 0) :: Δu) ++ gs_tele Ξ)
                       (List.rev (recursor_case_tys pq D 0 0 (ind_block_members D))) lc)
        by (rewrite <- List.app_assoc; exact Hcs).
      pose proof (params_evaluated_app _ _ (gs_tele Ξ) _ _ _ _ Hcs' H2) as H3.
      eexists; rewrite <- (List.app_nil_r (recursor_tele pq D Δu)), recursor_tele_app, List.app_nil_r; exact H3. }
    destruct HRt as [lr HRt].
    destruct (params_evaluated_sorts _ _ _ _ _ HRt) as (ps & Hps & HTs).
    destruct Ξ as [| [[mq Kq] Uq] Ξs]; [ contradiction |].
    set (Ξ := (mq, Kq, Uq) :: Ξs) in *.
    set (mr := qname_in (gs_path Ξ) "Rec").
    assert (HCT : ⊢ Θ ⍮ Ξ ⍮ recursor_tele pq D Δu ++ gs_tele Ξ) by (rewrite HT; exact (CT_wf _ _ _ _ Hg Hds HD Hc Hl HU)).
    assert (Hpush : ⊢ᵍ Θ ⍮ (mr, fk_module, gu_body (recursor_tele pq D Δu) ⋄) :: Ξ).
    { apply wf_gstack_cons; [ exact Hg | eapply wf_gmod_nil;
        [ apply recursor_tele_all_assumptions; exact HaΔ | exact HCT | exact Hps | exact HTs ] |].
      cbn; exists "Rec"%string; split; [ reflexivity | exact Hfr ]. }
    set (ds := List.map (fun jx => let '(j, Mj, x) := jx in mk_gen_def x ak_relevant (recursor_fn_ty pq D j Mj) (recursor_fn pq D j Mj))
                 (List.combine (List.combine (List.seq 0 (ind_nblk D)) (ind_block_members D)) (recursor_names Θ0 Ξ0 D))).
    assert (Hcmds : List.map ci_core (List.map (fun jx => let '(j, Mj, x) := jx in core_cmd_def x true false ak_relevant (recursor_fn_ty pq D j Mj) (Some (recursor_fn pq D j Mj)))
                      (List.combine (List.combine (List.seq 0 (ind_nblk D)) (ind_block_members D)) (recursor_names Θ0 Ξ0 D)))
                    = List.map (fun d => ci_core (gen_def_cmd true false d)) ds).
    { unfold ds; rewrite !List.map_map; apply List.map_ext; intros [[j Mj] x]; reflexivity. }
    assert (Hnames : List.map gen_def_name ds = recursor_names Θ0 Ξ0 D).
    { unfold ds; rewrite List.map_map.
      transitivity (List.map snd (List.combine (List.combine (List.seq 0 (ind_nblk D)) (ind_block_members D)) (recursor_names Θ0 Ξ0 D))).
      - apply List.map_ext; intros [[j Mj] x]; reflexivity.
      - apply map_snd_combine_le; rewrite List.length_combine, List.length_seq, length_recursor_names, length_ind_block_members; lia. }
    destruct (gen_defs_run ch B Rb Θ mr fk_module (recursor_tele pq D Δu) Ξ true false ds ⋄ Hpush) as (Φ' & Hr & _).
    - rewrite Hnames; apply recursor_names_nodup.
    - apply Forall_forall; intros; intros [].
    - apply Forall_forall; intros d Hin; unfold ds in Hin; apply List.in_map_iff in Hin as ([[j Mj] x] & <- & _); discriminate.
    - intros Φ' Hg' Hs'.
      assert (Hl' : ind_lookup Θ ((mr, fk_module, gu_body (recursor_tele pq D Δu) Φ') :: Ξ) pq = Some D).
      { eapply ind_lookup_gc_sub; [ exact Hs' |].
        eapply ind_lookup_gc_sub; [ apply gc_sub_push; exact (proj2 (proj2 (wf_gstack_cons_inv _ _ _ _ _ Hpush))) | exact Hl ]. }
      destruct (group_facts _ _ _ _ Hg' Hl') as (Hds' & HD' & _ & HU' & _).
      apply Forall_forall; intros d Hin; unfold ds in Hin; apply List.in_map_iff in Hin as ([[j Mj] x] & <- & Hin);
        cbn [gen_def_kind gen_def_type gen_def_body abs_kind_sort].
      apply List.in_combine_l in Hin; rewrite <- length_ind_block_members in Hin; apply In_combine_seq in Hin.
      rewrite HT.
      exact (conj (recursor_fn_ty_typed _ _ _ _ Hg' Hds' HD' Hc Hl' HU' j Mj Hin) (recursor_fn_typed _ _ _ _ Hg' Hds' HD' Hc Hl' HU' j Mj Hin)).
    - exists (gu_body (recursor_tele pq D Δu) Φ'); unfold recursor_mod_cmds; rewrite List.map_cons, List.map_app, Hcmds.
      eapply run_cmds_core; [ eapply run_cmd_mod_open; [ apply recursor_tele_all_assumptions; exact HaΔ | exact HCT | exact HRt | exact Hfr ] |].
      eapply run_cmds_concat; [ exact Hr |].
      eapply run_cmds_core; [ apply run_cmd_close_mod; [ reflexivity | exact Hfr ] | constructor ].
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
      ⊢ᵍ Θ ⍮ Ξ -> ind_uparams D = raw_decl_uparams R ++ gs_tele Ξ -> gs_fresh x Ξ ->
      Θ ⍮ Ξ ⍮ ind_qname Ξ x ⊢ᵉ ge_ind pv pq k D ⋄ ->
      ind_member D k = Some M -> im_head M = mh_decl pm ->
      (ind_has_rec D = true -> forall M0, ind_member D 0 = Some M0 -> ~ In "rec"%string (List.map fst (im_cons M0))) ->
      (raw_decl_rec_field R = false -> forall M0, ind_member D 0 = Some M0 -> ~ In "Rec"%string (List.map fst (im_cons M0))) ->
      exists U, Θ ⍮ gs_push_ind (ind_qname Ξ x) pq k D (raw_decl_uparams R) Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩
        List.map ci_core (ind_mod_cmds Θ0 Ξ0 R pq D k M) ⇝* Θ ⍮ (ind_qname Ξ x, fk_ind pq k D, U) :: Ξ ⍮ B ⍮ Rb.
  Proof.
    intros * Hg Hu Hfr HE HM Hh Hrnc Hrmnc.
    destruct (ind_nil_entry_uparams _ _ _ _ _ _ _ _ HE Hu) as [Htel HΔ].
    destruct (ind_empty_entry_params_evaluated _ _ _ _ _ _ _ _ HE Hu) as [lu HRu].
    destruct (params_evaluated_sorts _ _ _ _ _ HRu) as (ps & Hps & HTs).
    destruct Ξ as [| [[mq Kq] Uq] Ξs]; [ contradiction |].
    set (Ξ := (mq, Kq, Uq) :: Ξs) in *.
    set (mp := ind_qname Ξ x); set (Δu := raw_decl_uparams R); set (K := fk_ind pq k D).
    assert (Hpush : ⊢ᵍ Θ ⍮ (mp, K, gu_body Δu ⋄) :: Ξ).
    { apply wf_gstack_cons; [ exact Hg | eapply wf_gmod_ind_nil with (param_level := lu) (param_sorts := ps); eassumption |].
      cbn; exists x; split; [ reflexivity | exact Hfr ]. }
    assert (Hfacts : forall Φ', ⊢ᵍ Θ ⍮ (mp, K, gu_body Δu Φ') :: Ξ ->
              ind_lookup Θ ((mp, K, gu_body Δu Φ') :: Ξ) pq = Some D /\ decls_typed Θ ((mp, K, gu_body Δu Φ') :: Ξ) /\
              decl_typed Θ ((mp, K, gu_body Δu Φ') :: Ξ) D /\ decl_closed D /\ ⊢ Θ ⍮ (mp, K, gu_body Δu Φ') :: Ξ ⍮ ind_uparams D).
    { intros Φ' Hg'; pose proof (ind_frame_lookup _ _ _ _ _ _ _ Hg') as Hl.
      destruct (group_facts _ _ _ _ Hg' Hl) as (? & ? & ? & ? & _); tauto. }
    destruct (Hfacts ⋄ Hpush) as (_ & _ & HD & Hc & _).
    pose proof (decl_typed_nodup _ _ _ HD _ _ HM) as Hnd.
    (* the constructors *)
    set (ds1 := List.map (fun cg => mk_gen_def (fst cg) ak_relevant
                                      (ctx_pi (im_nparams M) (ctx_pi (cargs_ctx pq D M (snd cg)) (apps (a_ind pq k) (ind_pvars D M (List.length (snd cg))))))
                                      (apps (a_con pq k (fst cg)) (vars_from 0 (ind_nu D)))) (im_cons M)).
    assert (Hn1 : List.map gen_def_name ds1 = List.map fst (im_cons M)) by (unfold ds1; rewrite List.map_map; reflexivity).
    destruct (gen_defs_run ch B Rb Θ mp K Δu Ξ true false ds1 ⋄ Hpush) as (Φ1 & Hr1 & Hg1 & _ & Hf1).
    { rewrite Hn1; exact Hnd. }
    { apply Forall_forall; intros; intros []. }
    { apply Forall_forall; intros d Hin; unfold ds1 in Hin; apply List.in_map_iff in Hin as (cg & <- & _); discriminate. }
    { intros Φ' Hg' _; destruct (Hfacts Φ' Hg') as (Hl' & Hds' & HD' & _ & HU').
      apply Forall_forall; intros d Hin; unfold ds1 in Hin; apply List.in_map_iff in Hin as ([c gs] & <- & Hin);
        cbn [fst snd gen_def_kind gen_def_type gen_def_body abs_kind_sort].
      change (Δu ++ gs_tele Ξ) with (gs_tele ((mp, K, gu_body Δu Φ') :: Ξ)) in *.
      cbn [gs_tele gu_params]; unfold Δu; rewrite <- Hu.
      pose proof (cons_lookup_nodup _ _ _ Hnd Hin) as Hcon.
      exact (conj (con_gen_ty_typed _ _ _ _ _ _ _ _ _ Hg' Hds' Hl' HM Hh Hcon)
                  (con_gen_typed _ _ _ _ _ _ _ _ _ Hg' Hds' HD' Hc Hl' HM Hh HU' Hcon)). }
    assert (HRec1 : (Nat.eqb k 0 && negb (raw_decl_rec_field R))%bool = true -> gm_fresh "Rec" Φ1).
    { intros Hb; apply andb_prop in Hb as [Hk Hr]; apply Nat.eqb_eq in Hk; subst k; apply Bool.negb_true_iff in Hr.
      apply Hf1; [ intros [] | rewrite Hn1; exact (Hrmnc Hr M HM) ]. }
    (* the recursor, of a one-member group *)
    assert (Hrec : exists Φ2, Θ ⍮ (mp, K, gu_body Δu Φ1) :: Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ List.map ci_core (ind_rec_cmds pq D M) ⇝*
                     Θ ⍮ (mp, K, gu_body Δu Φ2) :: Ξ ⍮ B ⍮ Rb /\ ⊢ᵍ Θ ⍮ (mp, K, gu_body Δu Φ2) :: Ξ /\
                     ((Nat.eqb k 0 && negb (raw_decl_rec_field R))%bool = true -> gm_fresh "Rec" Φ2)).
    { unfold ind_rec_cmds; destruct (ind_has_rec D) eqn:Hhr; [| exists Φ1; split; [ constructor | split; [ exact Hg1 | exact HRec1 ] ] ].
      assert (Hone : ind_nblk D = 1) by (unfold ind_has_rec in Hhr; apply Nat.eqb_eq in Hhr; exact Hhr).
      (* the declared member is the one with a block, the first *)
      assert (Hk0 : k = 0).
      { pose proof (rview_struct_suffix _ _ _ (decl_typed_record_struct _ _ _ HD) _ _ HM) as Hs.
        assert (Hr : im_is_rview M = false) by (unfold im_is_rview; rewrite Hh; reflexivity).
        destruct (Nat.ltb_spec k 1) as [| Hle]; [ lia |].
        rewrite <- Hone in Hle; apply Hs in Hle; congruence. }
      assert (HM0 : ind_member D 0 = Some M) by (rewrite <- Hk0; exact HM).
      destruct (gen_defs_run ch B Rb Θ mp K Δu Ξ true false (mk_gen_def "rec" ak_relevant (rec_ty pq D M) (rec_fn pq D M) :: nil) Φ1 Hg1)
        as (Φ2 & Hr2 & Hg2 & _ & Hf2).
      - constructor; [ intros [] | constructor ].
      - constructor; [| constructor ]; cbn [gen_def_name]; apply Hf1; [ intros [] |].
        rewrite Hn1; subst k; exact (Hrnc eq_refl M HM).
      - constructor; [ discriminate | constructor ].
      - intros Φ' Hg' _; destruct (Hfacts Φ' Hg') as (Hl' & Hds' & HD' & _ & HU').
        constructor; [| constructor ]; cbn [gen_def_kind gen_def_type gen_def_body abs_kind_sort]; cbn [gs_tele gu_params]; unfold Δu; rewrite <- Hu.
        exact (conj (rec_ty_typed _ _ _ _ _ _ Hg' Hds' HD' Hc Hl' Hone HM0 Hh HU') (rec_typed _ _ _ _ _ _ Hg' Hds' HD' Hc Hl' Hone HM0 Hh HU')).
      - exists Φ2; split; [ exact Hr2 | split; [ exact Hg2 |] ].
        intros Hb; apply Hf2; [ exact (HRec1 Hb) | cbn; intros [H | []]; discriminate H ]. }
    destruct Hrec as (Φ2 & Hr2 & Hg2 & HRec2).
    (* the recursor module, in the first member's module *)
    assert (Hgrec : exists U, Θ ⍮ (mp, K, gu_body Δu Φ2) :: Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩
                     List.map ci_core (ind_recursor_cmds Θ0 Ξ0 R pq D k) ⇝* Θ ⍮ (mp, K, U) :: Ξ ⍮ B ⍮ Rb).
    { unfold ind_recursor_cmds; destruct ((Nat.eqb k 0 && negb (raw_decl_rec_field R))%bool) eqn:Hb; [| exists (gu_body Δu Φ2); constructor ].
      destruct (recursor_mod_run ch B Rb Θ ((mp, K, gu_body Δu Φ2) :: Ξ) pq D nil 0 Θ0 Ξ0 Hg2 (proj1 (Hfacts _ Hg2))
                  ltac:(cbn [gs_tele gu_params List.app]; unfold Δu; exact Hu) (HRec2 eq_refl) (params_evaluated_nil _ _ _ _)) as [U HU].
      eexists; exact HU. }
    destruct Hgrec as [U Hr3].
    exists U; unfold ind_mod_cmds, gs_push_ind; rewrite !List.map_app.
    eapply run_cmds_concat; [| eapply run_cmds_concat; [ exact Hr2 | exact Hr3 ] ].
    replace (List.map ci_core (List.map (ind_con_cmd pq D k M) (im_cons M)))
      with (List.map (fun d => ci_core (gen_def_cmd true false d)) ds1)
      by (unfold ds1; rewrite !List.map_map; apply List.map_ext; intros [c gs]; reflexivity).
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
      (raw_decl_rec_field R = false -> forall M0, ind_member D 0 = Some M0 -> ~ In "Rec"%string (List.map fst (im_cons M0))) ->
      exists Ξ', run_ind_members load_path read to_core ch B Rb Θ Ξ pv R pq D k xs B Rb Θ Ξ' /\ ⊢ᵍ Θ ⍮ Ξ' /\
        gs_tele Ξ' = gs_tele Ξ /\ (forall y, gs_fresh y Ξ -> ~ In y xs -> gs_fresh y Ξ') /\ gc_sub Θ Ξ Θ Ξ'.
  Proof.
    induction xs as [| x xs IH]; intros * Hg Hp HE Hrnc Hrmnc.
    - exists Ξ; split; [ constructor | split; [ exact Hg | split; [ reflexivity | split; [ auto | apply gc_sub_refl ] ] ] ].
    - pose proof (mems_fresh_head Hp) as Hfr; pose proof (mems_pre_uparams _ _ _ _ _ _ Hp) as Hu.
      destruct (mems_pre_heads _ _ _ _ _ _ Hp 0 x eq_refl) as (M & HM & Hh); rewrite Nat.add_0_r in HM.
      pose proof (HE x xs eq_refl) as HE0.
      destruct (ind_mod_run ch B Rb Θ Ξ pv R pq D k x M (ind_qname Ξ x) Θ (gs_push_ind (ind_qname Ξ x) pq k D (raw_decl_uparams R) Ξ)
                  Hg Hu Hfr HE0 HM Hh Hrnc Hrmnc) as [U Hr].
      destruct (ind_member_run_gen load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hg Hu Hfr HE0 Hr) as [_ _ _ Hg1 _ _ _].
      pose proof (mems_pre_tail Hp pv (gu_mod U)) as Hp1.
      destruct (IH ch B Rb Θ (gs_add x (ge_ind pv pq k D (gu_mod U)) Ξ) pv R pq D (S k) Hg1 Hp1) as (Ξ' & Hr' & Hg' & Ht' & Hf' & Hs').
      + intros y ys ->.
        destruct (mems_pre_later _ _ _ _ _ _ Hp1 ltac:(apply Nat.lt_0_succ)) as [mq Kq Δ Φ Ξ0 y0 pv0 Φm HΞ He Hat].
        destruct (mems_pre_heads _ _ _ _ _ _ Hp1 0 y eq_refl) as (My & HMy & Hhy); rewrite Nat.add_0_r in HMy.
        pose proof (mems_pre_count _ _ _ _ _ _ Hp1) as Hc; cbn [List.length] in Hc.
        pose proof (mems_pre_uparams _ _ _ _ _ _ Hp1) as Hu1.
        (** The uniform parameters are relevant where the first member is
            declared, and so after it is filed. *)
        destruct (ind_empty_entry_params_evaluated _ _ _ _ _ _ _ _ HE0 Hu) as [lu HRu].
        assert (HRu1 : params_evaluated Θ (gs_add x (ge_ind pv pq k D (gu_mod U)) Ξ)
                         (gs_tele (gs_add x (ge_ind pv pq k D (gu_mod U)) Ξ)) (raw_decl_uparams R) lu)
          by (rewrite gs_tele_add;
              exact (params_evaluated_embed _ _ _ _ _ _ _ (Build_gctx_embedding _ _ _ _ Hg1 (gc_sub_add _ _ _ _ Hg Hfr)) HRu)).
        rewrite HΞ in Hg1, Hhy, Hu1, HRu1 |- *; rewrite Hat; rewrite Hat in He.
        eapply later_member_entry; [ exact Hg1 | exact He | exact HMy | apply Nat.lt_0_succ | lia | exact Hhy | exact Hu1 | exact HRu1 ].
      + exact Hrnc.
      + exact Hrmnc.
      + exists Ξ'; split; [ econstructor; [ exact HM | exact Hfr | exact HE0 | exact Hr | exact Hr' ] | split; [ exact Hg' |] ].
        split; [ rewrite Ht', gs_tele_add; reflexivity |].
        split; [| exact (gc_sub_trans _ _ _ _ _ _ (gc_sub_add _ _ _ _ Hg Hfr) Hs') ].
        intros y Hy Hn; apply Hf'; [ apply gs_fresh_add; [ exact Hy | intros ->; apply Hn; left; reflexivity ] | intros Hin; apply Hn; right; exact Hin ].
  Qed.

  (** ** An Accepted Declaration Runs

      A group [run_cmd_ind_case] classifies, files, checks at its views' instances
      and finds its generated names free, its members' names distinct and
      fresh: its declared members run, each with its module, then, for a
      group declared by [mutual T where], [T.Rec]; so [run_cmd_ind_case] derives. *)
  Theorem run_cmd_ind_runs : forall ch B Rb Θ Ξ pv R Mr0 Mrs csD Vs Ss csV Nvs D,
      ⊢ᵍ Θ ⍮ Ξ ->
      raw_decl_members R = Mr0 :: Mrs ->
      Forall (fun Mr => raw_member_sort Mr = raw_member_sort Mr0) Mrs ->
      Forall2 (raw_member_classify Θ Ξ R) (raw_decl_members R) csD ->
      Forall2 (view_siblings Θ Ξ R) Vs Ss ->
      Forall2 (view_classify Θ Ξ R) Vs csV ->
      Forall2 (view_nparams Θ Ξ R) Vs Nvs ->
      views_dfs (siblings_table Vs Ss) (meets_table Vs csV) nil (List.concat (List.map classified_cons_views csD)) Vs ->
      raw_decl_filed Θ Ξ R Vs Ss csD csV Nvs = Some D ->
      ind_nil_at Θ Ξ (ind_qname Ξ (raw_member_name Mr0)) D (grp_self_insts (ind_qname Ξ (raw_member_name Mr0)) D) ->
      gen_names_free Ξ R D ->
      List.NoDup (List.map raw_member_name (raw_decl_members R)) -> Forall (fun Mr => gs_fresh (raw_member_name Mr) Ξ) (raw_decl_members R) ->
      exists Ξ', Θ ⍮ Ξ ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ core_cmd_inductive pv R ⇝ Θ ⍮ Ξ' ⍮ B ⍮ Rb.
  Proof.
    intros * Hg HR Hs Hcls Hsibs Hvcls Hnps Hbfs Hfil Hnil Hgn Hnd Hfr.
    set (pq := ind_qname Ξ (raw_member_name Mr0)).
    pose proof (ind_mems_pre HR Hfil Hnd Hfr) as Hp.
    pose proof (mems_pre_uparams _ _ _ _ _ _ Hp) as Hu.
    destruct (ind_members_run (List.map raw_member_name (raw_decl_members R)) ch B Rb Θ Ξ pv R pq D 0 Hg Hp) as (Ξ1 & Hr1 & Hg1 & Ht1 & Hf1 & Hs1).
    { rewrite HR; cbn [List.map]; intros x xs [= <- _]; exact (ind_nil_at_entry _ _ _ _ _ Hnil pv). }
    { exact (rec_not_constructor _ _ _ Hgn). }
    { exact (rec_module_not_constructor _ _ _ Hgn). }
    assert (Hrec : exists Ξ2, Θ ⍮ Ξ1 ⍮ B ⍮ Rb ⊢[ch]⟨load_path ⍮ read ⍮ to_core⟩ List.map ci_core (rec_cmds Θ Ξ1 R pq D) ⇝* Θ ⍮ Ξ2 ⍮ B ⍮ Rb).
    { unfold rec_cmds; destruct (raw_decl_rec_field R) eqn:Hrr; [| exists Ξ1; constructor ].
      assert (Hl1 : ind_lookup Θ Ξ1 pq = Some D).
      { rewrite HR in Hr1; cbn [List.map] in Hr1; exact (ind_members_run_lookup load_path read to_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr1 Hg Hu). }
      (** The uniform parameters are relevant where the group is declared
          ([ind_empty_entry_params_evaluated]), and so after its members. *)
      destruct (ind_empty_entry_params_evaluated _ _ _ _ _ _ _ _ (ind_nil_at_entry _ _ _ _ _ Hnil pv) Hu) as [lu HRu].
      assert (HRu1 : params_evaluated Θ Ξ1 (gs_tele Ξ1) (raw_decl_uparams R) lu)
        by (rewrite Ht1; exact (params_evaluated_embed _ _ _ _ _ _ _ (Build_gctx_embedding _ _ _ _ Hg1 Hs1) HRu)).
      destruct (recursor_mod_run ch B Rb Θ Ξ1 pq D (raw_decl_uparams R) lu Θ Ξ1 Hg1 Hl1 ltac:(rewrite Ht1; exact Hu)
                  (Hf1 _ (mutual_rec_fresh _ _ _ Hgn Hrr) (mutual_rec_not_member _ _ _ Hgn Hrr)) HRu1) as [U HU].
      eexists; exact HU. }
    destruct Hrec as [Ξ2 Hr2].
    exists Ξ2; eapply run_cmd_ind_case; eassumption.
  Qed.
End IndRuns.
