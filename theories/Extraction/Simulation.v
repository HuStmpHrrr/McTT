(** * The Fast Evaluation Simulates the Reference One

    [Extraction.FastEval] skips the recursive result of the eliminator when
    the successor case does not read it.  Its values then differ from the
    reference ones only in entries of environments that nothing reads:

    - [dsim a a'], between a reference value [a] and a fast one [a'], is
      equality of the two up to the entries of closures' environments at
      which the closure's body is fresh ([exp_fresh]);
    - [env_agree P ρ ρ'] is agreement of two environments at the entries
      [P] selects; a term is evaluated in environments that agree where the
      term may read, [fun x => ~ exp_fresh x M].

    Evaluation, from environments that agree where the term may read, gives
    values related by [dsim] ([feval_sim]), and readback of related values
    gives the same normal form ([fread_sim]).  So both evaluations normalize
    alike, which is what [Extraction.NbE] needs. *)
From Stdlib Require Import Lia List PeanoNat String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Substitution Members Fresh.
From Mctt.Core.Semantic Require Import Domain Evaluation Readback Avoid.
From Mctt.Extraction Require Import FastEval.
Import Domain_Notations.
#[local] Open Scope list_scope.

(** ** The Relation *)

Inductive dsim : domain -> domain -> Prop :=
| ds_nat : dsim ℕᵈ ℕᵈ
| ds_pi : forall a a' (ρ ρ' : env) B,
    dsim a a' ->
    (forall x, ~ exp_fresh (S x) B -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim (Πᵈ a ρ B) (Πᵈ a' ρ' B)
| ds_univ : forall i, dsim 𝕌ω@i 𝕌ω@i
| ds_suniv : forall l l', dsim l l' -> dsim 𝕌@l 𝕌@l'
| ds_level : forall n, dsim (Levelᵈ@n) (Levelᵈ@n)
| ds_lvl : forall c xs xs', dsim_la xs xs' -> dsim (lvᵈ c xs) (lvᵈ c xs')
| ds_zero : dsim zeroᵈ zeroᵈ
| ds_succ : forall m m', dsim m m' -> dsim (succᵈ m) (succᵈ m')
| ds_True : dsim ⊤ᵈ ⊤ᵈ
| ds_true : dsim ⋆ᵈ ⋆ᵈ
| ds_False : dsim ⊥ᵈ ⊥ᵈ
| ds_fn : forall (ρ ρ' : env) M,
    (forall x, ~ exp_fresh (S x) M -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim (λᵈ ρ M) (λᵈ ρ' M)
| ds_neut : forall a a' m m', dsim a a' -> dsim_ne m m' -> dsim (⇑ a m) (⇑ a' m')
| ds_member : forall h h' ch, dmsim h h' -> dsim (d_member h ch) (d_member h' ch)
with dsim_ne : domain_ne -> domain_ne -> Prop :=
| dsn_var : forall x, dsim_ne (#ᵈ x) (#ᵈ x)
| dsn_app : forall m m' n n', dsim_ne m m' -> dsim_nf n n' -> dsim_ne (m $ᵈ n) (m' $ᵈ n')
| dsn_natrec : forall (ρ ρ' : env) A mz mz' MS m m',
    (forall x, ~ exp_fresh (S x) A -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    (forall x, ~ exp_fresh (S (S x)) MS -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim mz mz' -> dsim_ne m m' ->
    dsim_ne (recᵈ m under ρ return A | zero -> mz | succ -> MS end)
            (recᵈ m' under ρ' return A | zero -> mz' | succ -> MS end)
| dsn_exfalso : forall (ρ ρ' : env) A m m',
    (forall x, ~ exp_fresh (S x) A -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim_ne m m' ->
    dsim_ne (efqᵈ m under ρ return A) (efqᵈ m' under ρ' return A)
| dsn_glob : forall p, dsim_ne (d_glob p) (d_glob p)
with dsim_nf : domain_nf -> domain_nf -> Prop :=
| dsf_dom : forall a a' m m', dsim a a' -> dsim m m' -> dsim_nf (⇓ a m) (⇓ a' m')
with dmsim : dmod -> dmod -> Prop :=
| dms_global : forall p args args', dsim_list args args' -> dmsim (dm_global p args) (dm_global p args')
| dms_local : forall (ρ ρ' : env) U args args',
    (forall x, ~ gunit_fresh x U -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim_list args args' ->
    dmsim (dm_local ρ U args) (dm_local ρ' U args')
| dms_member : forall h h' ch, dmsim h h' -> dmsim (dm_member h ch) (dm_member h' ch)
with dsim_la : list (nat * nat * domain_ne) -> list (nat * nat * domain_ne) -> Prop :=
| dsl_nil : dsim_la nil nil
| dsl_cons : forall k n m m' xs xs', dsim_ne m m' -> dsim_la xs xs' -> dsim_la ((k, n, m) :: xs) ((k, n, m') :: xs')
with dsim_list : list domain -> list domain -> Prop :=
| dsa_nil : dsim_list nil nil
| dsa_cons : forall a a' args args', dsim a a' -> dsim_list args args' -> dsim_list (a :: args) (a' :: args')
with desim : dentry -> dentry -> Prop :=
| des_term : forall d d', dsim d d' -> desim (de_term d) (de_term d')
| des_mod : forall h h', dmsim h h' -> desim (de_mod h) (de_mod h').

#[export]
Hint Constructors dsim dsim_ne dsim_nf dmsim dsim_la dsim_list desim : mctt.

(** Agreement of two environments at the entries [P] selects. *)
Definition env_agree (P : nat -> Prop) (ρ ρ' : env) : Prop :=
  forall x, P x -> desim (env_entry ρ x) (env_entry ρ' x).

(** ** Environments *)

Lemma env_agree_mono : forall P Q ρ ρ', env_agree P ρ ρ' -> (forall x, Q x -> P x) -> env_agree Q ρ ρ'.
Proof. intros * H HQ x Hx; apply H, HQ, Hx. Qed.

Lemma env_agree_nil : forall P, env_agree P nil nil.
Proof. intros P x _; induction x; cbn; [ repeat constructor | exact IHx ]. Qed.

Lemma env_agree_cons : forall P Q e e' ρ ρ',
    env_agree P ρ ρ' -> desim e e' -> (forall y, Q (S y) -> P y) -> env_agree Q (e :: ρ) (e' :: ρ').
Proof. intros * H He HQ [| y] Hy; cbn; [ exact He | apply H, HQ, Hy ]. Qed.

(** An entry nothing reads may be anything. *)
Lemma env_agree_cons_unread : forall P Q e e' ρ ρ',
    env_agree P ρ ρ' -> ~ Q 0 -> (forall y, Q (S y) -> P y) -> env_agree Q (e :: ρ) (e' :: ρ').
Proof. intros * H H0 HQ [| y] Hy; cbn; [ contradiction | apply H, HQ, Hy ]. Qed.

Lemma dsim_list_length : forall args args', dsim_list args args' -> List.length args = List.length args'.
Proof. induction 1; cbn; congruence. Qed.

Lemma env_agree_args : forall args args' P Q ρ ρ',
    env_agree P ρ ρ' -> dsim_list args args' ->
    (forall y, Q (List.length args + y) -> P y) ->
    env_agree Q (env_args ρ args) (env_args ρ' args').
Proof.
  induction args as [| a args IH]; intros * Hρ Ha HQ; inversion Ha; subst; cbn.
  - eapply env_agree_mono; [ exact Hρ | intros y Hy; apply HQ, Hy ].
  - eapply IH; [ eapply env_agree_cons with (Q := fun y => match y with 0 => True | S y => P y end);
                 [ exact Hρ | constructor; assumption | intros; assumption ]
               | eassumption |].
    intros [| y] Hy; [ exact I |]; apply HQ.
    replace (List.length args + S y) with (S (List.length args) + y) in Hy by lia; exact Hy.
Qed.

Lemma env_agree_var : forall P ρ ρ' x, env_agree P ρ ρ' -> P x -> dsim (ρ x) (ρ' x).
Proof. intros * H Hx; unfold env_var; destruct (H x Hx); [ assumption | constructor ]. Qed.

Lemma env_agree_mod : forall P ρ ρ' x, env_agree P ρ ρ' -> P x -> dmsim (env_mod ρ x) (env_mod ρ' x).
Proof. intros * H Hx; unfold env_mod; destruct (H x Hx); [ repeat constructor | assumption ]. Qed.

(** ** Levels *)

Lemma dsort_sim : forall a a', dsim a a' -> dsort a = dsort a'.
Proof. intros * H; destruct H; reflexivity. Qed.

Lemma dlvl_cst_sim : forall d d', dsim d d' -> dlvl_cst d = dlvl_cst d'.
Proof. intros * H; destruct H; reflexivity. Qed.

Lemma dlvl_atoms_sim : forall d d', dsim d d' -> dsim_la (dlvl_atoms d) (dlvl_atoms d').
Proof.
  intros * H; destruct H; cbn; try constructor; try assumption.
  erewrite dsort_sim by eassumption; repeat constructor; assumption.
Qed.

Lemma dsim_la_suc : forall xs xs', dsim_la xs xs' ->
    dsim_la (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs)
            (List.map (fun ka => (S (fst (fst ka)), snd (fst ka), snd ka)) xs').
Proof. induction 1; cbn; constructor; assumption. Qed.

Lemma dsim_la_app : forall xs xs' ys ys', dsim_la xs xs' -> dsim_la ys ys' -> dsim_la (xs ++ ys) (xs' ++ ys').
Proof. induction 1; intros; cbn; [ assumption | constructor; auto ]. Qed.

Lemma dsim_lvl_suc : forall d d', dsim d d' -> dsim (dlvl_suc d) (dlvl_suc d').
Proof.
  intros * H; unfold dlvl_suc; rewrite (dlvl_cst_sim _ _ H).
  constructor; apply dsim_la_suc, dlvl_atoms_sim, H.
Qed.

Lemma dsim_lvl_max : forall d d' e e', dsim d d' -> dsim e e' -> dsim (dlvl_max d e) (dlvl_max d' e').
Proof.
  intros * Hd He; unfold dlvl_max; rewrite (dlvl_cst_sim _ _ Hd), (dlvl_cst_sim _ _ He).
  constructor; apply dsim_la_app; apply dlvl_atoms_sim; assumption.
Qed.

Lemma dsim_list_snoc : forall args args' n n', dsim_list args args' -> dsim n n' ->
    dsim_list (args ++ n :: nil) (args' ++ n' :: nil).
Proof. induction 1; intros; cbn; repeat constructor; auto. Qed.

#[export]
Hint Resolve dsim_lvl_suc dsim_lvl_max dsim_list_snoc env_agree_nil : mctt.

(** ** Environments of Bodies and Spines *)

(** The environment of a body agrees on the entries the body adds, and,
    above them, where the environment it extends did. *)
Definition above (n : nat) (P : nat -> Prop) (z : nat) : Prop := z < n \/ exists y, z = n + y /\ P y.

Lemma above_zero : forall P z, above 0 P z -> P z.
Proof. intros * [Hz | (y & -> & Hy)]; [ lia | exact Hy ]. Qed.

Lemma above_of : forall n (P Q : nat -> Prop), (forall y, Q (n + y) -> P y) -> forall z, Q z -> above n P z.
Proof.
  intros * H z Hz; destruct (Nat.lt_ge_cases z n) as [Hlt | Hge]; [ left; exact Hlt | right ].
  exists (z - n); split; [ lia | apply H; replace (n + (z - n)) with z by lia; exact Hz ].
Qed.

Lemma env_agree_above_cons : forall n P e e' ρ ρ',
    env_agree (above n P) ρ ρ' -> desim e e' -> env_agree (above (S n) P) (e :: ρ) (e' :: ρ').
Proof.
  intros * H He [| z] Hz; cbn; [ exact He |].
  apply H; destruct Hz as [Hz | (y & Hy & HP)]; [ left; lia | right; exists y; split; [ lia | exact HP ] ].
Qed.

Lemma nil_agree : forall x, desim (env_entry nil x) (env_entry nil x).
Proof. intros; apply env_agree_nil with (P := fun _ => True); exact I. Qed.

Lemma agree_spine : forall H R args pre y (ρ ρ' : env),
    modexp_spine H = (R, args, pre) ->
    env_agree (fun x => ~ exp_fresh x (a_mem H y)) ρ ρ' ->
    env_agree (fun x => ~ modexp_fresh x R) ρ ρ' /\ env_agree (fun x => ~ Forall (exp_fresh x) args) ρ ρ'.
Proof.
  intros * Hs Hρ; split; eapply env_agree_mono; try exact Hρ; intros x Hx Hf; apply Hx;
    cbn in Hf; destruct (modexp_spine_fresh _ _ _ _ _ Hs Hf); assumption.
Qed.

(** The environment of the step case of the eliminator: its last entry, the
    recursive result, may be anything when the step case does not read it. *)
Lemma env_agree_natrec_step : forall MS (ρ ρ' : env) b b' r r',
    env_agree (fun x => ~ exp_fresh (S (S x)) MS) ρ ρ' -> dsim b b' -> (exp_fresh 0 MS \/ dsim r r') ->
    env_agree (fun x => ~ exp_fresh x MS) (ρ ↦ b ↦ r) (ρ' ↦ b' ↦ r').
Proof.
  intros * Hρ Hb Hr [| [| x]] Hx; cbn.
  - destruct Hr; [ contradiction | constructor; assumption ].
  - constructor; assumption.
  - apply Hρ; exact Hx.
Qed.

#[export]
Hint Resolve nil_agree : mctt.

(** ** Evaluation *)

(** The parts of a term may read only what the term may. *)
Ltac nf_sub := let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
  intros x Hx Hf; apply Hx; cbn in Hf |- *; rewrite ?Forall_cons_iff in Hf; tauto.

(** Inversion of the relation on a value whose head is known. *)
Ltac sim_inv :=
  match goal with
  | H : dsim (_ _) _ |- _ => inversion H; subst; clear H
  | H : dsim (_ _ _) _ |- _ => inversion H; subst; clear H
  | H : dsim (_ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : dsim ℕᵈ _ |- _ => inversion H; subst; clear H
  | H : dsim zeroᵈ _ |- _ => inversion H; subst; clear H
  | H : dsim ⊤ᵈ _ |- _ => inversion H; subst; clear H
  | H : dsim ⋆ᵈ _ |- _ => inversion H; subst; clear H
  | H : dsim ⊥ᵈ _ |- _ => inversion H; subst; clear H
  | H : dmsim (_ _ _) _ |- _ => inversion H; subst; clear H
  | H : dmsim (_ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : dsim_list (_ :: _) _ |- _ => inversion H; subst; clear H
  | H : dsim_list nil _ |- _ => inversion H; subst; clear H
  | Hs : modexp_spine ?H = (?R, ?args, ?pre), Hρ : env_agree (fun x => ~ exp_fresh x (a_mem ?H _)) ?ρ ?ρ' |- _ =>
      destruct (agree_spine _ _ _ _ _ _ _ Hs Hρ); clear Hρ
  | H : forall x, ~ @?F x -> desim (env_entry ?ρ x) (env_entry ?ρ' x) |- _ =>
      change (env_agree (fun x => ~ F x) ρ ρ') in H; cbv beta in H
  end.

(** A related entry: a related value, or the closure of a unit over
    environments that agree where the unit may read. *)
Ltac ent_tac :=
  first [ constructor; eassumption
        | constructor; solve [ eauto with mctt ]
        | apply des_mod; apply dms_local; [| constructor ];
          eapply env_agree_mono; [ eassumption | nf_sub ] ].

(** An environment that agrees where a term may read, for one of its parts:
    the same environment, or one extended by related entries. *)
Ltac agree_tac :=
  first [ eassumption
        | match goal with Hρ : env_agree _ ?ρ _ |- env_agree _ ?ρ _ =>
            eapply env_agree_mono; [ exact Hρ | nf_sub ] end
        | match goal with
          | |- env_agree _ (_ :: ?ρ) _ => idtac
          | |- env_agree _ (extend_env ?ρ _) _ => unfold extend_env
          | |- env_agree _ (extend_env_mod ?ρ _) _ => unfold extend_env_mod
          end;
          match goal with |- env_agree _ (_ :: ?ρ) _ =>
            match goal with Hρ : env_agree _ ?ρ _ |- _ =>
              eapply env_agree_cons; [ exact Hρ | ent_tac | nf_sub ] end end
        | match goal with |- env_agree _ nil _ => apply env_agree_nil end
        | match goal with |- env_agree _ (env_args ?ρ ?args) _ =>
            match goal with Hρ : env_agree _ ?ρ _, Ha : dsim_list args _ |- _ =>
              eapply env_agree_args; [ exact Hρ | exact Ha |];
              let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
              intros y Hy Hf; apply Hy; cbn in Hf;
              repeat match goal with He : List.length args = List.length _ |- _ => rewrite He end;
              tauto end end ].

(** A premise on the length of the fast arguments, from the reference ones. *)
Ltac len_tac :=
  match goal with Hl : dsim_list ?a ?a' |- context [List.length ?a'] =>
    rewrite <- (dsim_list_length _ _ Hl); eassumption end.

(** Forward reasoning: each induction hypothesis, at the fast arguments that
    are related to its reference ones. *)
Ltac sim_fwd :=
  match goal with
  | IH : forall ρ0, env_agree ?P ?ρ ρ0 -> exists _, _ /\ _ |- _ =>
      let H' := fresh "Ha" in
      eassert (H' : env_agree P ρ _) by agree_tac;
      destruct (IH _ H') as (? & ? & ?); clear IH H'
  | IH : forall ρ0 m0, env_agree ?P1 ?ρ ρ0 -> env_agree ?P2 ?ρ ρ0 -> env_agree ?P3 ?ρ ρ0 -> dsim ?m m0 -> exists _, _ /\ _,
    Hm : dsim ?m ?m' |- _ =>
      let H1 := fresh "Ha" in let H2 := fresh "Ha" in let H3 := fresh "Ha" in
      eassert (H1 : env_agree P1 ρ _) by agree_tac;
      eassert (H2 : env_agree P2 ρ _) by agree_tac;
      eassert (H3 : env_agree P3 ρ _) by agree_tac;
      destruct (IH _ _ H1 H2 H3 Hm) as (? & ? & ?); clear IH H1 H2 H3
  | IH : forall m0 n0, dsim ?m m0 -> dsim ?n n0 -> exists _, _ /\ _, Hm : dsim ?m ?m', Hn : dsim ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0 n0, dsim ?m m0 -> dsim_list ?n n0 -> exists _, _ /\ _, Hm : dsim ?m ?m', Hn : dsim_list ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0 n0, dmsim ?m m0 -> dsim ?n n0 -> exists _, _ /\ _, Hm : dmsim ?m ?m', Hn : dsim ?n ?n' |- _ =>
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0, dmsim ?m m0 -> exists _, _ /\ _, Hm : dmsim ?m ?m' |- _ =>
      destruct (IH _ Hm) as (? & ? & ?); clear IH
  | IH : forall m0 n0, dsim ?m m0 -> dsim_list ?n n0 -> exists _, _ /\ _, Hn : dsim_list ?n ?n' |- _ =>
      let Hm := fresh "Hm" in
      eassert (Hm : dsim m _) by (eauto with mctt);
      destruct (IH _ _ Hm Hn) as (? & ? & ?); clear IH
  | IH : forall m0, dmsim ?m m0 -> exists _, _ /\ _ |- _ =>
      let Hm := fresh "Hm" in
      eassert (Hm : dmsim m _) by (eauto with mctt);
      destruct (IH _ Hm) as (? & ? & ?); clear IH
  end.

(** The goal: the fast rule, and the relation between the results, whose
    closures agree where the reference ones may read. *)
Ltac sim_fin :=
  eexists; split;
  [ econstructor; solve [ eassumption | len_tac ]
  | repeat first [ eassumption
                 | eapply env_agree_var; [ eassumption | cbn; intros Hne; apply Hne; reflexivity ]
                 | eapply env_agree_mod; [ eassumption | cbn; intros Hne; apply Hne; reflexivity ]
                 | solve [ eauto with mctt ]
                 | constructor
                 | match goal with |- forall x, ~ _ -> desim _ _ =>
                     let x := fresh "x" in let Hx := fresh "Hx" in
                     intros x Hx; match goal with Hρ : env_agree _ _ _ |- _ =>
                       apply Hρ; let Hf := fresh "Hf" in intros Hf; apply Hx; cbn in Hf; tauto end end ] ].

Section Eval.
  Variables (Θ : gdeps) (Ξ : gstack).

  Theorem feval_sim :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
       exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ dsim m m') /\
    (forall A MZ MS m ρ r, ⟦rec m return A | zero -> MZ | succ -> MS end ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r ->
       forall ρ' m', env_agree (fun x => ~ exp_fresh (S x) A) ρ ρ' -> env_agree (fun x => ~ exp_fresh x MZ) ρ ρ' ->
       env_agree (fun x => ~ exp_fresh (S (S x)) MS) ρ ρ' -> dsim m m' ->
       exists r', ⟦recᶠ m' return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ dsim r r') /\
    (forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> forall m' n', dsim m m' -> dsim n n' ->
       exists r', $ᶠ| m' & n' | Θ ⍮ Ξ ↘ r' /\ dsim r r') /\
    (forall Ms ρ ms, ⟦ Ms ⟧* Θ ⍮ Ξ ⍮ ρ ↘ ms -> forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
       exists ms', ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ms' /\ dsim_list ms ms') /\
    (forall m args r, $*| m & args | Θ ⍮ Ξ ↘ r -> forall m' args', dsim m m' -> dsim_list args args' ->
       exists r', $*ᶠ| m' & args' | Θ ⍮ Ξ ↘ r' /\ dsim r r') /\
    (forall H ρ h, ⟦ H ⟧ᵐ Θ ⍮ Ξ ⍮ ρ ↘ h -> forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' ->
       exists h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmsim h h') /\
    (forall h n r, $ᵐ| h & n | Θ ⍮ Ξ ↘ r -> forall h' n', dmsim h h' -> dsim n n' ->
       exists r', $ᵐᶠ| h' & n' | Θ ⍮ Ξ ↘ r' /\ dmsim r r') /\
    (forall h x r, h ·ₜ x Θ ⍮ Ξ ↘ r -> forall h', dmsim h h' -> exists r', h' ·ₜᶠ x Θ ⍮ Ξ ↘ r' /\ dsim r r') /\
    (forall h y r, h ·ₘ y Θ ⍮ Ξ ↘ r -> forall h', dmsim h h' -> exists r', h' ·ₘᶠ y Θ ⍮ Ξ ↘ r' /\ dmsim r r') /\
    (forall h ch r, h ·ₜ* ch Θ ⍮ Ξ ↘ r -> forall h', dmsim h h' -> exists r', h' ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dsim r r') /\
    (forall h ch r, h ·ₘ* ch Θ ⍮ Ξ ↘ r -> forall h', dmsim h h' -> exists r', h' ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dmsim r r') /\
    (forall ρ Φ ρ1, ⟦ Φ ⟧ᵇ Θ ⍮ Ξ ⍮ ρ ↘ ρ1 -> forall ρ' (P : nat -> Prop),
       (forall x, ~ gmod_fresh x Φ -> P x) -> env_agree P ρ ρ' ->
       exists ρ1', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1').
  Proof.
    apply (eval_mut_ind Θ Ξ
      (fun M ρ m _ => forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
         exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ dsim m m')
      (fun A MZ MS m ρ r _ => forall ρ' m', env_agree (fun x => ~ exp_fresh (S x) A) ρ ρ' ->
         env_agree (fun x => ~ exp_fresh x MZ) ρ ρ' -> env_agree (fun x => ~ exp_fresh (S (S x)) MS) ρ ρ' ->
         dsim m m' -> exists r', ⟦recᶠ m' return A | zero -> MZ | succ -> MS end ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ dsim r r')
      (fun m n r _ => forall m' n', dsim m m' -> dsim n n' -> exists r', $ᶠ| m' & n' | Θ ⍮ Ξ ↘ r' /\ dsim r r')
      (fun Ms ρ ms _ => forall ρ', env_agree (fun x => ~ Forall (exp_fresh x) Ms) ρ ρ' ->
         exists ms', ⟦ Ms ⟧*ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ms' /\ dsim_list ms ms')
      (fun m args r _ => forall m' args', dsim m m' -> dsim_list args args' ->
         exists r', $*ᶠ| m' & args' | Θ ⍮ Ξ ↘ r' /\ dsim r r')
      (fun H ρ h _ => forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' ->
         exists h', ⟦ H ⟧ᵐᶠ Θ ⍮ Ξ ⍮ ρ' ↘ h' /\ dmsim h h')
      (fun h n r _ => forall h' n', dmsim h h' -> dsim n n' -> exists r', $ᵐᶠ| h' & n' | Θ ⍮ Ξ ↘ r' /\ dmsim r r')
      (fun h x r _ => forall h', dmsim h h' -> exists r', h' ·ₜᶠ x Θ ⍮ Ξ ↘ r' /\ dsim r r')
      (fun h y r _ => forall h', dmsim h h' -> exists r', h' ·ₘᶠ y Θ ⍮ Ξ ↘ r' /\ dmsim r r')
      (fun h ch r _ => forall h', dmsim h h' -> exists r', h' ·ₜ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dsim r r')
      (fun h ch r _ => forall h', dmsim h h' -> exists r', h' ·ₘ*ᶠ ch Θ ⍮ Ξ ↘ r' /\ dmsim r r')
      (fun ρ Φ ρ1 _ => forall ρ' (P : nat -> Prop),
         (forall x, ~ gmod_fresh x Φ -> P x) -> env_agree P ρ ρ' ->
         exists ρ1', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1'));
      intros.
    all: repeat first [ sim_inv | sim_fwd ].
    all: try solve [ sim_fin ].
    (** The eliminator at a successor: the recursive result is computed or
        skipped, as the fast rule decides. *)
    all: try match goal with
      | IH : forall ρ0, env_agree (fun x => ~ exp_fresh x ?MS) (?ρ ↦ ?b ↦ ?r) ρ0 -> _,
        HS : env_agree (fun x => ~ exp_fresh (S (S x)) ?MS) ?ρ ?ρ',
        Hb : dsim ?b ?b', Hr : dsim ?r ?r' |- _ =>
          let Hf := fresh "Hf" in
          destruct (exp_freshb 0 MS) eqn:Hf;
          [ destruct (IH (ρ' ↦ b' ↦ zeroᵈ)
                       (env_agree_natrec_step _ _ _ _ _ _ _ HS Hb (or_introl (exp_freshb_sound _ _ Hf))))
              as (? & ? & ?);
            eexists; split; [ apply feval_natrec_skip; eassumption | eassumption ]
          | destruct (IH (ρ' ↦ b' ↦ r') (env_agree_natrec_step _ _ _ _ _ _ _ HS Hb (or_intror Hr)))
              as (? & ? & ?);
            eexists; split; [ eapply feval_natrec_succ; eassumption | eassumption ] ]
      end.
    (** A member of a saturated body: the environment of its parameters,
        then of the body up to it, agree where the body may read. *)
    all: try match goal with
      | Hl : List.length ?args = List.length ?Δ, Hp : gm_prefix_upto ?Φ _ = Some (gm_ext ?Φ' _ _),
        IHb : forall ρ0 (P : nat -> Prop), (forall x, ~ gmod_fresh x ?Φ' -> P x) -> env_agree P (env_args ?ρ ?args) ρ0 -> _,
        Hρ : env_agree (fun x => ~ gunit_fresh x (gu_body ?Δ ?Φ)) ?ρ ?ρ', Ha : dsim_list ?args ?args' |- _ =>
          let HA := fresh "HA" in let HP := fresh "HP" in
          assert (HA : env_agree (fun y => ~ gmod_fresh y Φ) (env_args ρ args) (env_args ρ' args'))
            by (eapply env_agree_args; [ exact Hρ | exact Ha |];
                let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                intros y Hy Hf; apply Hy; cbn in Hf; rewrite Hl; tauto);
          assert (HP : forall x, ~ gmod_fresh x Φ' -> ~ gmod_fresh x Φ)
            by (let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
                intros x Hx Hf; apply Hx; apply (prefix_upto_fresh _ _ _ _ Hp) in Hf; cbn in Hf; tauto);
          destruct (IHb _ _ HP HA) as (? & ? & ?); clear IHb
      end.
    all: try match goal with
      | Hp : gm_prefix_upto ?Φ _ = Some (gm_ext ?Φ' _ (ge_def _ _ _ (Some ?M))),
        IH : forall ρ0, env_agree (fun x => ~ exp_fresh x ?M) ?ρ1 ρ0 -> _,
        Hab : env_agree (above (gm_binders ?Φ') (fun y => ~ gmod_fresh y ?Φ)) ?ρ1 ?ρ1' |- _ =>
          let Hq := fresh "Hq" in
          assert (Hq : env_agree (fun x => ~ exp_fresh x M) ρ1 ρ1')
            by (eapply env_agree_mono; [ exact Hab | apply above_of ];
                let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                intros y Hy Hf; apply Hy; apply (prefix_upto_fresh _ _ _ _ Hp) in Hf; cbn in Hf; tauto);
          destruct (IH _ Hq) as (? & ? & ?);
          eexists; split; [ eapply feval_sel_body; (try len_tac); eassumption | eassumption ]
      | Hp : gm_prefix_upto ?Φ _ = Some (gm_ext ?Φ' _ (ge_mod _ ?Uy)),
        Hab : env_agree (above (gm_binders ?Φ') (fun y => ~ gmod_fresh y ?Φ)) ?ρ1 ?ρ1' |- _ =>
          eexists; split; [ eapply feval_selm_body; (try len_tac); eassumption |];
          constructor; [| constructor ];
          eapply env_agree_mono; [ exact Hab | apply above_of ];
          let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
          intros y Hy Hf; apply Hy; apply (prefix_upto_fresh _ _ _ _ Hp) in Hf; cbn in Hf; tauto
      end.
    (** The environment of a body, entry by entry. *)
    all: try match goal with
      | |- exists ρ1', ⟦ gm_nil ⟧ᵇᶠ _ ⍮ _ ⍮ _ ↘ ρ1' /\ _ =>
          eexists; split; [ constructor |];
          eapply env_agree_mono; [ eassumption | intros ? ?; apply above_zero; assumption ]
      | IH : forall ρ0 (P0 : nat -> Prop), (forall x, ~ gmod_fresh x ?Φ -> P0 x) -> env_agree P0 ?ρ ρ0 -> _,
        HQ : forall x, ~ gmod_fresh x (gm_ext ?Φ _ ?E) -> ?P x, Hρ : env_agree ?P ?ρ ?ρ' |- _ =>
          let HP := fresh "HP" in
          assert (HP : forall x, ~ gmod_fresh x Φ -> P x)
            by (let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
                intros x Hx; apply HQ; intros Hf; apply Hx; cbn in Hf; tauto);
          destruct (IH _ _ HP Hρ) as (ρ1' & ? & ?); clear IH
      end.
    all: try match goal with
      | HQ : forall x, ~ gmod_fresh x (gm_ext ?Φ _ (ge_def _ _ _ (Some ?M))) -> ?P x,
        IH : forall ρ0, env_agree (fun x => ~ exp_fresh x ?M) ?ρ1 ρ0 -> _,
        Hab : env_agree (above (gm_binders ?Φ) ?P) ?ρ1 ?ρ1' |- _ =>
          let Hq := fresh "Hq" in
          assert (Hq : env_agree (fun x => ~ exp_fresh x M) ρ1 ρ1')
            by (eapply env_agree_mono; [ exact Hab | apply above_of ];
                let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                intros y Hy; apply HQ; intros Hf; apply Hy; cbn in Hf; tauto);
          destruct (IH _ Hq) as (? & ? & ?);
          eexists; split; [ econstructor; eassumption |];
          cbn [gm_binders]; apply env_agree_above_cons; [ exact Hab | constructor; eassumption ]
      | HQ : forall x, ~ gmod_fresh x (gm_ext ?Φ _ (ge_mod _ ?Uy)) -> ?P x,
        Hab : env_agree (above (gm_binders ?Φ) ?P) ?ρ1 ?ρ1' |- _ =>
          eexists; split; [ econstructor; eassumption |];
          cbn [gm_binders]; apply env_agree_above_cons; [ exact Hab |];
          constructor; constructor; [| constructor ];
          eapply env_agree_mono; [ exact Hab | apply above_of ];
          let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
          intros y Hy; apply HQ; intros Hf; apply Hy; cbn in Hf; tauto
      end.
  Qed.
End Eval.

Section Read.
  Variables (Θ : gdeps) (Ξ : gstack).

  Lemma feval_exp_sim : forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
      exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ dsim m m'.
  Proof. exact (proj1 (feval_sim Θ Ξ)). Qed.

  Lemma feval_app_sim : forall m n r, $| m & n | Θ ⍮ Ξ ↘ r -> forall m' n', dsim m m' -> dsim n n' ->
      exists r', $ᶠ| m' & n' | Θ ⍮ Ξ ↘ r' /\ dsim r r'.
  Proof. exact (proj1 (proj2 (proj2 (feval_sim Θ Ξ)))). Qed.

  (** A closure, at one or two related arguments. *)
  Lemma feval_clo_sim : forall B (ρ ρ' : env) c c' b,
      env_agree (fun x => ~ exp_fresh (S x) B) ρ ρ' -> dsim c c' -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c') ↘ b' /\ dsim b b'.
  Proof.
    intros * Hρ Hc Hb; eapply feval_exp_sim; [ exact Hb |].
    intros [| x] Hx; cbn; [ constructor; exact Hc | apply Hρ, Hx ].
  Qed.

  Lemma feval_clo2_sim : forall B (ρ ρ' : env) c1 c1' c2 c2' b,
      env_agree (fun x => ~ exp_fresh (S (S x)) B) ρ ρ' -> dsim c1 c1' -> dsim c2 c2' ->
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c1' ↦ c2') ↘ b' /\ dsim b b'.
  Proof.
    intros * Hρ Hc1 Hc2 Hb; eapply feval_exp_sim; [ exact Hb |].
    intros [| [| x]] Hx; cbn; [ constructor; exact Hc2 | constructor; exact Hc1 | apply Hρ, Hx ].
  Qed.

  (** Readback of related values gives the same normal form. *)
  Theorem fread_sim :
    (forall s n W, Rnf n in Θ ⍮ Ξ ⍮ s ↘ W -> forall n', dsim_nf n n' -> Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s m W, Rne m in Θ ⍮ Ξ ⍮ s ↘ W -> forall m', dsim_ne m m' -> Rneᶠ m' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s a W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> forall a', dsim a a' -> Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys -> forall xs', dsim_la xs xs' -> Rlaᶠ xs' in Θ ⍮ Ξ ⍮ s ↘ ys).
  Proof.
    apply (read_mut_ind Θ Ξ
      (fun s n W _ => forall n', dsim_nf n n' -> Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W)
      (fun s m W _ => forall m', dsim_ne m m' -> Rneᶠ m' in Θ ⍮ Ξ ⍮ s ↘ W)
      (fun s a W _ => forall a', dsim a a' -> Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W)
      (fun s xs ys _ => forall xs', dsim_la xs xs' -> Rlaᶠ xs' in Θ ⍮ Ξ ⍮ s ↘ ys));
      intros;
      repeat match goal with
        | H : dsim_nf _ _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (_ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (_ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (_ _ _ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (d_natrec _ _ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_la (_ :: _) _ |- _ => inversion H; subst; clear H
        | H : dsim_la nil _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _) _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim ℕᵈ _ |- _ => inversion H; subst; clear H
        | H : dsim zeroᵈ _ |- _ => inversion H; subst; clear H
        | H : dsim ⊤ᵈ _ |- _ => inversion H; subst; clear H
        | H : dsim ⊥ᵈ _ |- _ => inversion H; subst; clear H
        end.
    (** The closures are evaluated at related arguments, then read back. *)
    all: repeat match goal with
      | He : ⟦ ?B ⟧ Θ ⍮ Ξ ⍮ ?ρ ↦ ?c1 ↦ ?c2 ↘ ?b,
        Hρ : forall x, ~ exp_fresh (S (S x)) ?B -> desim (env_entry ?ρ x) (env_entry ?ρ' x) |- _ =>
          destruct (feval_clo2_sim B ρ ρ' c1 _ c2 _ b Hρ ltac:(eauto with mctt) ltac:(eauto with mctt) He)
            as (? & ? & ?); clear He
      | He : ⟦ ?B ⟧ Θ ⍮ Ξ ⍮ ?ρ ↦ ?c ↘ ?b,
        Hρ : forall x, ~ exp_fresh (S x) ?B -> desim (env_entry ?ρ x) (env_entry ?ρ' x) |- _ =>
          destruct (feval_clo_sim B ρ ρ' c _ b Hρ ltac:(eauto with mctt) He) as (? & ? & ?); clear He
      | He : $| ?m & ?n | Θ ⍮ Ξ ↘ ?r, Hm : dsim ?m ?m' |- _ =>
          destruct (feval_app_sim _ _ _ He m' _ Hm ltac:(eauto with mctt)) as (? & ? & ?); clear He
      end.
    (** A neutral level's sort is read off its type, which is related. *)
    all: try (erewrite dsort_sim by eassumption).
    all: solve [ econstructor; eauto 6 with mctt ].
  Qed.

  Corollary fread_typ_sim : forall s a a' W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> dsim a a' -> Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros; eapply (proj1 (proj2 (proj2 fread_sim))); eassumption. Qed.

  Corollary fread_nf_sim : forall s n n' W, Rnf n in Θ ⍮ Ξ ⍮ s ↘ W -> dsim_nf n n' -> Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W.
  Proof. intros; eapply (proj1 fread_sim); eassumption. Qed.
End Read.
