(** * The Fast Evaluation Simulates the Reference One

    [Extraction.FastEval] skips the recursive result of a recursive
    argument of a constructor when the eliminator's branch does not read
    it.  Its values then differ from the reference ones only in entries of
    environments that nothing reads:

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
From Mctt.Core.Syntactic Require Import Substitution Members Fresh Inductives.
From Mctt.Core.Semantic Require Import Domain Evaluation Readback Avoid Kinds.
From Mctt.Extraction Require Import FastEval.
Import Domain_Notations.
#[local] Open Scope list_scope.

(** ** The Relation *)

(** The components of a shape, each under the domains before it, are fresh
    at [k]. *)
Fixpoint pt_fresh (k : nat) (t : ptyp) : Prop :=
  match t with
  | pt_pi B t => exp_fresh k B /\ pt_fresh (S k) t
  | pt_self _ Ps | pt_aux _ Ps => Forall (exp_fresh k) Ps
  end.

Inductive dsim : domain -> domain -> Prop :=
| ds_pi : forall a a' (ρ ρ' : env) B,
    dsim a a' ->
    (forall x, ~ exp_fresh (S x) B -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim (Πᵈ a ρ B) (Πᵈ a' ρ' B)
| ds_univ : forall i, dsim 𝕌ω@i 𝕌ω@i
| ds_suniv : forall l l', dsim l l' -> dsim 𝕌@l 𝕌@l'
| ds_level : forall n, dsim (Levelᵈ@n) (Levelᵈ@n)
| ds_lvl : forall c xs xs', dsim_la xs xs' -> dsim (lvᵈ c xs) (lvᵈ c xs')
| ds_True : dsim ⊤ᵈ ⊤ᵈ
| ds_true : dsim ⋆ᵈ ⋆ᵈ
| ds_False : dsim ⊥ᵈ ⊥ᵈ
| ds_fn : forall (ρ ρ' : env) M,
    (forall x, ~ exp_fresh (S x) M -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim (λᵈ ρ M) (λᵈ ρ' M)
| ds_neut : forall a a' m m', dsim a a' -> dsim_ne m m' -> dsim (⇑ a m) (⇑ a' m')
| ds_member : forall h h' ch, dmsim h h' -> dsim (d_member h ch) (d_member h' ch)
| ds_indty : forall p args args', dsim_list args args' -> dsim (d_ind p args) (d_ind p args')
| ds_con : forall p c args args', dsim_list args args' -> dsim (d_con p c args) (d_con p c args')
(** The recursive result of a function shape: the environments agree where
    the motive and the branches may read, as [dsn_elim]; the families of a
    function shape: where the rest of the shape may read under the domain
    the family binds, and where the motive may read under the shape's
    parameters and the argument. *)
| ds_ihfn : forall (ρ ρ' : env) nm A Bs t f f',
    (forall x, ~ exp_fresh (nm + x) A -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    (forall c n B, In (c, n, B) Bs -> forall x, ~ exp_fresh (n + x) B -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim f f' -> dsim (d_ihfn ρ nm A Bs t f) (d_ihfn ρ' nm A Bs t f')
| ds_shfam : forall p ups ups' (ρ ρ' : env) t,
    dsim_list ups ups' ->
    (forall x, ~ pt_fresh (S x) t -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim (d_shfam p ups ρ t) (d_shfam p ups' ρ' t)
| ds_ihfam : forall (ρm ρm' : env) A (ρ ρ' : env) t f f',
    (forall x, ~ exp_fresh (S (List.length (ptyp_ps t)) + x) A -> desim (env_entry ρm x) (env_entry ρm' x)) ->
    (forall x, ~ pt_fresh (S x) t -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim f f' -> dsim (d_ihfam ρm A ρ t f) (d_ihfam ρm' A ρ' t f')
with dsim_ne : domain_ne -> domain_ne -> Prop :=
| dsn_var : forall x, dsim_ne (#ᵈ x) (#ᵈ x)
| dsn_app : forall m m' n n', dsim_ne m m' -> dsim_nf n n' -> dsim_ne (m $ᵈ n) (m' $ᵈ n')
| dsn_exfalso : forall (ρ ρ' : env) A m m',
    (forall x, ~ exp_fresh (S x) A -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim_ne m m' ->
    dsim_ne (efqᵈ m under ρ return A) (efqᵈ m' under ρ' return A)
| dsn_glob : forall p, dsim_ne (d_glob p) (d_glob p)
(** A stuck eliminator: the environments agree where the motive and the
    branches may read, under their binders. *)
| dsn_elim : forall (ρ ρ' : env) nm A Bs p args args' m m',
    (forall x, ~ exp_fresh (nm + x) A -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    (forall c n B, In (c, n, B) Bs -> forall x, ~ exp_fresh (n + x) B -> desim (env_entry ρ x) (env_entry ρ' x)) ->
    dsim_list args args' -> dsim_ne m m' ->
    dsim_ne (d_elim ρ nm A Bs p args m) (d_elim ρ' nm A Bs p args' m')
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

Lemma dsim_list_app : forall args args' bs bs', dsim_list args args' -> dsim_list bs bs' ->
    dsim_list (args ++ bs) (args' ++ bs').
Proof. induction 1; intros; cbn; [ assumption | constructor; auto ]. Qed.

Lemma dsim_list_firstn : forall n args args', dsim_list args args' -> dsim_list (firstn n args) (firstn n args').
Proof. intros n args args' H; revert n; induction H; intros [| n]; cbn; constructor; auto. Qed.

Lemma dsim_list_skipn : forall n args args', dsim_list args args' -> dsim_list (skipn n args) (skipn n args').
Proof. intros n args args' H; revert n; induction H; intros [| n]; cbn; try constructor; auto. Qed.

(** Agreement everywhere: the environments of the telescopes of a
    declaration, whose types are read at every entry. *)
Lemma env_agree_all_args : forall args args' ρ ρ',
    env_agree (fun _ => True) ρ ρ' -> dsim_list args args' ->
    env_agree (fun _ => True) (env_args ρ args) (env_args ρ' args').
Proof. intros * Hρ Ha; eapply env_agree_args; [ exact Hρ | exact Ha | intros; exact I ]. Qed.

Lemma env_agree_all_cons : forall ρ ρ' d d',
    env_agree (fun _ => True) ρ ρ' -> dsim d d' -> env_agree (fun _ => True) (ρ ↦ d) (ρ' ↦ d').
Proof. intros * Hρ Hd; eapply env_agree_cons; [ exact Hρ | constructor; exact Hd | intros; exact I ]. Qed.

(** The environment of a closure under its [n] binders: the [n] entries are
    related, and the rest agree where the body may read. *)
Lemma env_agree_binders : forall n B args args' ρ ρ',
    env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ' -> dsim_list args args' -> List.length args = n ->
    env_agree (fun x => ~ exp_fresh x B) (env_args ρ args) (env_args ρ' args').
Proof. intros * Hρ Ha Hl; eapply env_agree_args; [ exact Hρ | exact Ha |]; intros y Hy; rewrite Hl in Hy; exact Hy. Qed.

(** Two lists of values related at the entries [P] selects, once they
    extend an environment: the entry of [a] in [env_args ρ (a :: l)] is
    [List.length l]. *)
Inductive dsim_list_at (P : nat -> Prop) : list domain -> list domain -> Prop :=
| dsat_nil : dsim_list_at P nil nil
| dsat_cons : forall a a' l l', (P (List.length l) -> dsim a a') -> dsim_list_at P l l' ->
    dsim_list_at P (a :: l) (a' :: l').

#[export]
Hint Constructors dsim_list_at : mctt.

Lemma dsim_list_at_app : forall P l1 l1' l2 l2', dsim_list l1 l1' -> dsim_list_at P l2 l2' ->
    dsim_list_at P (l1 ++ l2) (l1' ++ l2').
Proof. induction 1; intros; cbn; [ assumption | constructor; auto ]. Qed.

Lemma env_agree_args_at : forall P Q args args' ρ ρ',
    env_agree P ρ ρ' -> dsim_list_at Q args args' ->
    (forall y, Q (List.length args + y) -> P y) ->
    env_agree Q (env_args ρ args) (env_args ρ' args').
Proof.
  intros * Hρ Ha; revert P ρ ρ' Hρ; induction Ha as [| a a' l l' Hh Ht IH]; intros P ρ ρ' Hρ HQ; cbn.
  - eapply env_agree_mono; [ exact Hρ | intros y Hy; apply HQ, Hy ].
  - eapply IH with (P := fun y => Q (List.length l + y)); [| intros; assumption ].
    intros [| y] Hy; cbn.
    + constructor; apply Hh; rewrite Nat.add_0_r in Hy; exact Hy.
    + apply Hρ, HQ; cbn; replace (S (List.length l + y)) with (List.length l + S y) by lia; exact Hy.
Qed.

(** The environment of a branch under its [n] binders, whose last entries,
    the recursive results, are related only where the branch reads. *)
Lemma env_agree_binders_at : forall n B args args' ρ ρ',
    env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ' ->
    dsim_list_at (fun x => ~ exp_fresh x B) args args' -> List.length args = n ->
    env_agree (fun x => ~ exp_fresh x B) (env_args ρ args) (env_args ρ' args').
Proof. intros * Hρ Ha Hl; eapply env_agree_args_at; [ exact Hρ | exact Ha |]; intros y Hy; rewrite Hl in Hy; exact Hy. Qed.

(** The type of an argument of a function shape, and of its recursive
    result: a [Π] over a family in an environment that holds only it. *)
Lemma dsim_fam_pi : forall b b' d d', dsim b b' -> dsim d d' ->
    dsim (Πᵈ b (nil ↦ d) fam_cod) (Πᵈ b' (nil ↦ d') fam_cod).
Proof.
  intros * Hb Hd; constructor; [ exact Hb |].
  intros [| x] _; cbn; [ constructor; exact Hd | apply env_agree_nil with (P := fun _ => True); exact I ].
Qed.

(** The parts of an eliminator may read only what the eliminator may. *)
Lemma agree_elim_A : forall nm A Bs M ρ ρ',
    env_agree (fun x => ~ exp_fresh x (a_elim nm A Bs M)) ρ ρ' -> env_agree (fun x => ~ exp_fresh (nm + x) A) ρ ρ'.
Proof. intros * H x Hx; apply H; intros Hf; apply Hx; apply exp_fresh_elim in Hf; tauto. Qed.

Lemma agree_elim_B : forall nm A Bs M ρ ρ',
    env_agree (fun x => ~ exp_fresh x (a_elim nm A Bs M)) ρ ρ' ->
    forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ'.
Proof.
  intros * H c n B Hin x Hx; apply H; intros Hf; apply Hx.
  apply exp_fresh_elim in Hf as (_ & HF & _); exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.

#[export]
Hint Resolve dsim_lvl_suc dsim_lvl_max dsim_list_snoc env_agree_nil
  dsim_list_app dsim_list_firstn dsim_list_skipn env_agree_all_args env_agree_all_cons : mctt.

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

(** ** Kinds

    The kinds of members read an environment only through the module
    entries the syntax reads, so environments that agree where the syntax
    may read give the same kinds, and the same generated entries. *)

Lemma env_agree_kpad : forall n (P Q : nat -> Prop) ρ ρ', env_agree P ρ ρ' -> (forall y, Q (n + y) -> P y) ->
    env_agree Q (kpad n ρ) (kpad n ρ').
Proof.
  unfold kpad; induction n as [| n IH]; intros * Hρ HQ; cbn [List.repeat app].
  - eapply env_agree_mono; [ exact Hρ | exact HQ ].
  - eapply env_agree_cons with (P := fun y => Q (S y)); [| repeat constructor | intros; assumption ].
    eapply IH; [ exact Hρ | intros y Hy; apply HQ; exact Hy ].
Qed.

(** A weakening past [k] entries reads none of them. *)
Lemma modexp_unfresh_shiftn : forall E k z, ~ modexp_fresh z (modexp_wk E (wk_shiftn k)) ->
    exists w, z = k + w /\ ~ modexp_fresh w E.
Proof.
  intros * Hz.
  destruct (Nat.lt_ge_cases z k) as [Hlt | Hge].
  - exfalso; apply Hz; apply (proj1 (proj2 syn_wk_fresh)).
    intros x; cbn [wk_shiftn]; lia.
  - exists (z - k); split; [ lia |]; intros Hf; apply Hz.
    replace z with (k + (z - k)) by lia; apply modexp_fresh_shiftn; exact Hf.
Qed.

Lemma above_above : forall n m P z, above n (above m P) z -> above (n + m) P z.
Proof.
  intros * [Hz | (y & -> & [Hy | (w & -> & Hw)])]; [ left; lia | left; lia | right; exists w; split; [ lia | exact Hw ] ].
Qed.

Lemma above_above_inv : forall n m P z, above (n + m) P z -> above n (above m P) z.
Proof.
  intros * [Hz | (w & -> & Hw)].
  - destruct (Nat.lt_ge_cases z n) as [Hlt | Hge]; [ left; exact Hlt |].
    right; exists (z - n); split; [ lia | left; lia ].
  - right; exists (m + w); split; [ lia | right; exists w; split; [ reflexivity | exact Hw ] ].
Qed.

Section KindSim.
  Variables (Θ : gdeps) (Ξ : gstack).

  Lemma kgens_env_sim : forall ρ0 H its gs, kgens Θ Ξ ρ0 H its gs ->
      forall (Q : nat -> Prop), (forall x, ~ modexp_fresh x H -> Q x) ->
      forall gs1, (forall g, In g gs1 -> In g gs) ->
      forall k ρ ρ', env_agree (above k Q) ρ ρ' ->
      env_agree (above (List.length gs1 + k) Q) (kgens_env ρ k gs1) (kgens_env ρ' k gs1).
  Proof.
    intros * Hg Q HQ gs1; induction gs1 as [| g gs1 IH]; intros Hin k ρ ρ' Hρ; cbn [kgens_env List.length]; [ exact Hρ |].
    rewrite Nat.add_succ_comm; apply IH; [ intros; apply Hin; right; assumption |].
    apply env_agree_above_cons; [ exact Hρ |].
    destruct (kgens_no_ind _ _ _ _ _ _ Hg g (Hin g (or_introl eq_refl))) as [(d & pv & A0 & M & ->) | (d & pv & E & ->)];
      cbn [kentry]; [ repeat constructor |].
    constructor; constructor; [| constructor ].
    intros z Hz; apply Hρ; cbn in Hz.
    assert (Hz' : ~ modexp_fresh z (modexp_wk E (wk_shiftn k))) by (intros Hf; apply Hz; split; [ exact I | exact Hf ]).
    destruct (modexp_unfresh_shiftn _ _ _ Hz') as (w & -> & Hw).
    right; exists w; split; [ reflexivity | apply HQ ].
    destruct (kgens_alias_target _ _ _ _ _ _ Hg _ _ _ (Hin _ (or_introl eq_refl))) as [-> | (n & ->)]; [ exact Hw |].
    intros Hf; apply Hw; exact Hf.
  Qed.

  Lemma kind_sim :
    (forall h ch k, dkind Θ Ξ h ch k -> forall h', dmsim h h' -> dkind Θ Ξ h' ch k) /\
    (forall ρ U ch k, ukind Θ Ξ ρ U ch k -> forall ρ', env_agree (fun x => ~ gunit_fresh x U) ρ ρ' -> ukind Θ Ξ ρ' U ch k) /\
    (forall ρ H ch k, skind Θ Ξ ρ H ch k -> forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' -> skind Θ Ξ ρ' H ch k) /\
    (forall ρ Φ ρ1, kenv Θ Ξ ρ Φ ρ1 -> forall ρ' (P : nat -> Prop), (forall x, ~ gmod_fresh x Φ -> P x) -> env_agree P ρ ρ' ->
       exists ρ1', kenv Θ Ξ ρ' Φ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1') /\
    (forall ρ H its gs, kgens Θ Ξ ρ H its gs -> forall ρ', env_agree (fun x => ~ modexp_fresh x H) ρ ρ' -> kgens Θ Ξ ρ' H its gs).
  Proof.
    apply kind_mut_ind.
    (* values *)
    1-2: intros * Hr h' Hs; inversion Hs; subst; econstructor; eassumption.
    - intros * Hr Hu _ h' Hs; inversion Hs; subst; econstructor; eassumption.
    - intros * Hu IH h' Hs; inversion Hs; subst; constructor; auto.
    - intros * Hd IH h' Hs; inversion Hs; subst; constructor; auto.
    (* units *)
    - intros; constructor.
    - intros; econstructor; eassumption.
    - (* a module of a body, read in the environment of the body before it *)
      intros * Hp Hk IHk Hu IHu ρ' Hρ.
      destruct (IHk (kpad (List.length Δ) ρ') (fun x => ~ gmod_fresh x Φ)) as (ρ1' & Hk1 & Hρ1).
      { intros x Hx Hf; apply Hx; pose proof (prefix_upto_fresh _ _ _ _ Hp Hf) as Hf'; cbn in Hf'; tauto. }
      { eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf. }
      eapply uk_mod; [ eassumption | exact Hk1 |].
      apply IHu; eapply env_agree_mono; [ exact Hρ1 | apply above_of ].
      intros y0 Hy Hf; apply Hy; pose proof (prefix_upto_fresh _ _ _ _ Hp Hf) as Hf'; cbn in Hf'; tauto.
    - (* a name an open declares, read in the open's target *)
      intros * Hi Hk IHk Hs IHs ρ' Hρ.
      destruct (IHk (kpad (List.length Δ) ρ') (fun x => ~ gmod_fresh x Φ)) as (ρ0' & Hk0 & Hρ0).
      { intros x0 Hx Hf; apply Hx; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto. }
      { eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf. }
      eapply uk_item; [ eassumption | exact Hk0 |].
      apply IHs; eapply env_agree_mono; [ exact Hρ0 | apply above_of ].
      intros y0 Hy Hf; apply Hy; pose proof (item_upto_fresh _ _ _ _ _ _ _ Hi Hf) as Hf'; cbn in Hf'; tauto.
    - intros * Hs IH ρ' Hρ; constructor; apply IH.
      eapply env_agree_kpad; [ exact Hρ |]; intros y0 Hy Hf; apply Hy; cbn in Hf |- *; destruct Hf as [_ Hf]; exact Hf.
    (* module expressions *)
    - intros * Hd _ ρ' _; constructor; exact Hd.
    - intros * Hd IH ρ' Hρ; constructor; apply IH; eapply env_agree_mod; [ exact Hρ | cbn; intros Hne; apply Hne; reflexivity ].
    - intros * Hu IH ρ' Hρ; constructor; apply IH; eapply env_agree_mono; [ exact Hρ | intros x Hx Hf; apply Hx; exact Hf ].
    - intros * Hs IH ρ' Hρ; constructor; apply IH; eapply env_agree_mono; [ exact Hρ | intros x Hx Hf; apply Hx; exact Hf ].
    - intros * Hs IH ρ' Hρ; constructor; apply IH; eapply env_agree_mono; [ exact Hρ | intros x Hx Hf; apply Hx; cbn in Hf; tauto ].
    (* bodies *)
    - intros * HP Hρ; exists ρ'; split; [ constructor |].
      eapply env_agree_mono; [ exact Hρ | intros ? ?; apply above_zero; assumption ].
    - intros * Hk IH ρ' P HP Hρ.
      destruct (IH ρ' P) as (ρ1' & Hk1 & Hρ1); [ intros x Hx; apply HP; cbn; tauto | exact Hρ |].
      exists (kbentry ρ1' E :: ρ1'); split; [ constructor; exact Hk1 |].
      cbn [gm_binders]; apply env_agree_above_cons; [ exact Hρ1 |].
      destruct E as [? ? ? ? | pm U | ? ? ? | ? ? ? ?]; cbn [kbentry]; try (repeat constructor; fail).
      constructor; constructor; [| constructor ].
      eapply env_agree_mono; [ exact Hρ1 | apply above_of ].
      intros y0 Hy; apply HP; intros Hf; apply Hy; cbn in Hf; tauto.
    - intros * Hk IH Hg IHg ρ' P HP Hρ.
      destruct (IH ρ' P) as (ρ1' & Hk1 & Hρ1); [ intros x Hx; apply HP; cbn; tauto | exact Hρ |].
      assert (HH : forall x, ~ modexp_fresh x H -> above (gm_binders Φ) P x).
      { apply above_of; intros y0 Hy; apply HP; intros Hf; apply Hy; cbn in Hf; tauto. }
      assert (HHa : env_agree (fun x => ~ modexp_fresh x H) ρ1 ρ1')
        by (eapply env_agree_mono; [ exact Hρ1 | exact HH ]).
      exists (kgens_env ρ1' 0 gs); split; [ econstructor; [ exact Hk1 | auto ] |].
      cbn [gm_binders]; rewrite <- (kgens_length _ _ _ _ _ _ Hg).
      eapply env_agree_mono; [| intros z Hz; apply above_above_inv; exact Hz ].
      pose proof (kgens_env_sim _ _ _ _ Hg _ HH gs (fun g Hin => Hin) 0 ρ1 ρ1'
                    (env_agree_mono _ _ _ _ Hρ1 (fun z Hz => above_zero _ _ Hz))) as Hs.
      rewrite Nat.add_0_r in Hs; exact Hs.
    (* generated entries *)
    - intros; constructor.
    - intros * Hg IH ρ' Hρ; constructor; auto.
    - intros * Hs IHs Hg IH ρ' Hρ; constructor; auto.
    - intros * Hs IHs Hg IH ρ' Hρ; constructor; auto.
  Qed.
End KindSim.

Section Eval.
  Variables (Θ : gdeps) (Ξ : gstack).

  Theorem feval_sim :
    (forall M ρ m, ⟦ M ⟧ Θ ⍮ Ξ ⍮ ρ ↘ m -> forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
       exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ dsim m m') /\
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
       exists ρ1', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1') /\
    (forall ρ nm A Bs m r, ⟦elim m under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ r -> forall ρ' m',
       env_agree (fun x => ~ exp_fresh (nm + x) A) ρ ρ' ->
       (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
       dsim m m' -> exists r', ⟦elimᶠ m' under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ dsim r r') /\
    (forall ρ nm A Bs gs vs ihs, ⟦ihs vs of gs under nm A Bs ⟧ Θ ⍮ Ξ ⍮ ρ ↘ ihs -> forall ρ' vs' B,
       env_agree (fun x => ~ exp_fresh (nm + x) A) ρ ρ' ->
       (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
       dsim_list vs vs' -> exists ihs', ⟦ihsᶠ vs' of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ihs' /\
       dsim_list_at (fun x => ~ exp_fresh x B) ihs ihs') /\
    (forall ρ nm A Bs t m r, eval_ih Θ Ξ ρ nm A Bs t m r -> forall ρ' m',
       env_agree (fun x => ~ exp_fresh (nm + x) A) ρ ρ' ->
       (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
       dsim m m' -> exists r', feval_ih Θ Ξ ρ' nm A Bs t m' r' /\ dsim r r') /\
    (forall p ups ρ t a, eval_shty Θ Ξ p ups ρ t a -> forall ups' ρ',
       dsim_list ups ups' -> env_agree (fun x => ~ pt_fresh x t) ρ ρ' ->
       exists a', feval_shty Θ Ξ p ups' ρ' t a' /\ dsim a a') /\
    (forall ρm A ρ t m a, eval_ihty Θ Ξ ρm A ρ t m a -> forall ρm' ρ' m',
       env_agree (fun x => ~ exp_fresh (S (List.length (ptyp_ps t)) + x) A) ρm ρm' ->
       env_agree (fun x => ~ pt_fresh x t) ρ ρ' -> dsim m m' ->
       exists a', feval_ihty Θ Ξ ρm' A ρ' t m' a' /\ dsim a a').
  Proof.
    apply (eval_mut_ind Θ Ξ
      (fun M ρ m _ => forall ρ', env_agree (fun x => ~ exp_fresh x M) ρ ρ' ->
         exists m', ⟦ M ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ m' /\ dsim m m')
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
         exists ρ1', ⟦ Φ ⟧ᵇᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ρ1' /\ env_agree (above (gm_binders Φ) P) ρ1 ρ1')
      (fun ρ nm A Bs m r _ => forall ρ' m',
         env_agree (fun x => ~ exp_fresh (nm + x) A) ρ ρ' ->
         (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
         dsim m m' -> exists r', ⟦elimᶠ m' under nm A Bs ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ r' /\ dsim r r')
      (fun ρ nm A Bs gs vs ihs _ => forall ρ' vs' B,
         env_agree (fun x => ~ exp_fresh (nm + x) A) ρ ρ' ->
         (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
         dsim_list vs vs' -> exists ihs', ⟦ihsᶠ vs' of gs under nm A Bs for B ⟧ᶠ Θ ⍮ Ξ ⍮ ρ' ↘ ihs' /\
         dsim_list_at (fun x => ~ exp_fresh x B) ihs ihs')
      (fun ρ nm A Bs t m r _ => forall ρ' m',
         env_agree (fun x => ~ exp_fresh (nm + x) A) ρ ρ' ->
         (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
         dsim m m' -> exists r', feval_ih Θ Ξ ρ' nm A Bs t m' r' /\ dsim r r')
      (fun p ups ρ t a _ => forall ups' ρ',
         dsim_list ups ups' -> env_agree (fun x => ~ pt_fresh x t) ρ ρ' ->
         exists a', feval_shty Θ Ξ p ups' ρ' t a' /\ dsim a a')
      (fun ρm A ρ t m a _ => forall ρm' ρ' m',
         env_agree (fun x => ~ exp_fresh (S (List.length (ptyp_ps t)) + x) A) ρm ρm' ->
         env_agree (fun x => ~ pt_fresh x t) ρ ρ' -> dsim m m' ->
         exists a', feval_ihty Θ Ξ ρm' A ρ' t m' a' /\ dsim a a'));
      intros.
    all: repeat first [ sim_inv | sim_fwd ].
    all: try solve [ sim_fin ].
    (** Inductive types.  The eliminator: its parts agree where it does. *)
    all: try solve [ match goal with
      | IH : forall ρ0 m0, env_agree _ ?ρ ρ0 -> _ -> dsim ?m m0 -> exists _, _ /\ _,
        Hm : dsim ?m ?m', Hρ : env_agree (fun x => ~ exp_fresh x (a_elim ?nm ?A ?Bs ?M)) ?ρ ?ρ' |- _ =>
          let r' := fresh "r'" in
          destruct (IH ρ' m' (agree_elim_A _ _ _ _ _ _ Hρ) (agree_elim_B _ _ _ _ _ _ Hρ) Hm) as (r' & ? & ?);
          exists r'; split; [ econstructor; eassumption | assumption ]
      end ].
    (** On a constructor: the recursive results, then the branch, in the
        environment of the parameters, the arguments and the results. *)
    all: try solve [ match goal with
      | IHi : forall ρ0 vs0 B0, env_agree _ ?ρ ρ0 -> _ -> dsim_list (skipn _ ?vs) vs0 -> exists _, _ /\ _,
        IHB : forall ρ0, env_agree (fun x => ~ exp_fresh x ?B) (env_args ?ρ _) ρ0 -> exists _, _ /\ _,
        HA : env_agree (fun x => ~ exp_fresh (?nm + x) ?A) ?ρ ?ρ',
        HBs : forall c n B, In (c, n, B) ?Bs -> env_agree _ ?ρ ?ρ',
        Hvs : dsim_list ?vs ?vs', e : brs_lookup ?Bs ?c = Some (_, ?B),
        Hl : List.length ?vs = (ind_np ?D + List.length ?gs)%nat,
        Hih : ⟦ihs _ of ?gs under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?ihs |- _ =>
          let ihs' := fresh "ihs'" in let Hihs' := fresh "Hihs'" in let Hsi := fresh "Hsi" in
          let r' := fresh "r'" in
          destruct (IHi ρ' (skipn (ind_np D) vs') B HA HBs (dsim_list_skipn _ _ _ Hvs)) as (ihs' & Hihs' & Hsi);
          destruct (IHB (env_args ρ' (skipn (ind_nu D) (firstn (ind_np D) vs') ++ skipn (ind_np D) vs' ++ ihs')))
            as (r' & ? & ?);
            [ eapply env_agree_binders_at;
                [ exact (HBs _ _ _ (brs_lookup_in _ _ _ _ e))
                | apply dsim_list_at_app; [ apply dsim_list_skipn, dsim_list_firstn, Hvs
                                          | apply dsim_list_at_app; [ apply dsim_list_skipn, Hvs | exact Hsi ] ]
                | rewrite (ind_branch_args_length _ _ _ _ Hl), (proj2 (eval_ihs_length _ _ _ _ _ _ _ Hih));
                  first [ reflexivity | lia ] ]
            |];
          exists r'; split;
            [ eapply feval_elim_con; try eassumption; try reflexivity; rewrite <- (dsim_list_length _ _ Hvs); exact Hl
            | assumption ]
      end ].
    (** On a neutral: the motive's instance, and a neutral eliminator over
        environments that agree where the motive and the branches read. *)
    all: try solve [ match goal with
      | IH : forall ρ0, env_agree (fun x => ~ exp_fresh x ?A) (env_args ?ρ _) ρ0 -> exists _, _ /\ _,
        HA : env_agree (fun x => ~ exp_fresh (?nm + x) ?A) ?ρ ?ρ',
        HBs : forall c n B, In (c, n, B) ?Bs -> env_agree _ ?ρ ?ρ',
        Has : dsim_list ?as' ?as'', Hm : dsim_ne ?m ?m',
        Hl : List.length ?as' = ind_np ?D |- exists _, ⟦elimᶠ ⇑ (d_ind ?p ?as'') ?m' under _ _ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          let a' := fresh "a'" in
          destruct (IH (env_args ρ' (skipn (ind_nu D) as'' ++ ⇑ (d_ind p as'') m' :: nil))) as (a' & ? & ?);
            [ eapply env_agree_binders;
                [ exact HA
                | apply dsim_list_app; [ apply dsim_list_skipn, Has | repeat constructor; assumption ]
                | rewrite (ind_motive_args_length _ _ _ Hl); first [ reflexivity | lia ] ]
            |];
          eexists; split;
            [ eapply feval_elim_neut; try eassumption; try reflexivity; rewrite <- (dsim_list_length _ _ Has); exact Hl
            | constructor; [ assumption | constructor; [ exact HA | exact HBs | assumption | assumption ] ] ]
      end ].
    (** The recursive results: each is computed when the branch reads it,
        and skipped when it does not, as the fast rule decides. *)
    all: try solve [ eexists; split; [ constructor | constructor ] ].
    all: try solve [ match goal with
      | IH : forall ρ0 vs0 B0, env_agree _ ?ρ ρ0 -> _ -> dsim_list ?vs vs0 -> exists _, _ /\ _,
        HA : env_agree (fun x => ~ exp_fresh (?nm + x) ?A) ?ρ ?ρ',
        HBs : forall c n B, In (c, n, B) ?Bs -> env_agree _ ?ρ ?ρ', Hvs : dsim_list ?vs ?vs'
        |- exists _, ⟦ihsᶠ _ of ?gs0 under _ _ _ for ?B ⟧ᶠ _ ⍮ _ ⍮ _ ↘ _ /\ _ =>
          let ihs' := fresh "ihs'" in
          destruct (IH ρ' vs' B HA HBs Hvs) as (ihs' & ? & ?);
          first [ exists ihs'; split; [ constructor; eassumption | assumption ]
                | match goal with
                  | IHe : forall ρ0 m0, env_agree _ ?ρ ρ0 -> _ -> dsim ?v m0 -> exists _, _ /\ _, Hv : dsim ?v ?v',
                    Hih : ⟦ihs ?vs of ?gs under _ _ _ ⟧ _ ⍮ _ ⍮ _ ↘ ?ihs |- _ =>
                      let Hf := fresh "Hf" in
                      destruct (exp_freshb (cargs_nrec gs) B) eqn:Hf;
                      [ exists (𝕌ω@0 :: ihs'); split;
                          [ apply feval_ihs_skip; assumption
                          | constructor; [| assumption ];
                            rewrite (proj2 (eval_ihs_length _ _ _ _ _ _ _ Hih));
                            intros Hn; exfalso; exact (Hn (exp_freshb_sound _ _ Hf)) ]
                      | let ih' := fresh "ih'" in
                        destruct (IHe ρ' v' HA HBs Hv) as (ih' & ? & ?);
                        exists (ih' :: ihs'); split;
                          [ eapply feval_ihs_rec; eassumption | constructor; [ intros; assumption | assumption ] ] ]
                  end ]
      end ].
    (** Function shapes.  The recursive result of a function shape and the
        families of its types, applied; the recursive result at a leaf; and
        the types, a [Π] over the family. *)
    all: try solve [ match goal with
      | IH : forall ρ0 m0, env_agree _ ?ρ ρ0 -> _ -> dsim ?fn m0 -> exists _, feval_ih _ _ _ _ _ _ _ _ _ /\ _,
        HA : env_agree (fun x => ~ exp_fresh (_ + x) _) ?ρ ?ρ', HB : forall c n B, In (c, n, B) _ -> forall x, _ -> _,
        Hf : dsim ?fn ?x, Ha : $ᶠ| _ & _ | _ ⍮ _ ↘ ?x |- exists _, $ᶠ| d_ihfn _ _ _ _ _ _ & _ | _ ⍮ _ ↘ _ /\ _ =>
          let r' := fresh "r'" in
          destruct (IH _ _ HA HB Hf) as (r' & ? & ?); exists r'; split; [ econstructor; eassumption | assumption ]
      | IH : forall ups0 ρ0, dsim_list ?ups ups0 -> env_agree _ (?ρ ↦ ?n) ρ0 -> exists _, _ /\ _,
        Hu : dsim_list ?ups ?ups', Hρ : env_agree (fun x => ~ pt_fresh (S x) ?t) ?ρ ?ρ', Hn : dsim ?n ?n'
        |- exists _, $ᶠ| d_shfam _ _ _ _ & _ | _ ⍮ _ ↘ _ /\ _ =>
          let a' := fresh "a'" in
          destruct (IH ups' (ρ' ↦ n') Hu) as (a' & ? & ?);
            [ unfold extend_env; eapply env_agree_cons; [ exact Hρ | constructor; exact Hn | intros y Hy; exact Hy ] |];
          exists a'; split; [ econstructor; eassumption | assumption ]
      | IH : forall ρm0 ρ0 m0, env_agree _ ?ρm ρm0 -> env_agree _ (?ρ ↦ ?n) ρ0 -> dsim ?fn m0 -> exists _, _ /\ _,
        HA : env_agree _ ?ρm ?ρm', Hρ : env_agree (fun x => ~ pt_fresh (S x) ?t) ?ρ ?ρ', Hn : dsim ?n ?n',
        Hf : dsim ?fn ?x, Ha : $ᶠ| _ & _ | _ ⍮ _ ↘ ?x |- exists _, $ᶠ| d_ihfam _ _ _ _ _ & _ | _ ⍮ _ ↘ _ /\ _ =>
          let a' := fresh "a'" in
          destruct (IH ρm' (ρ' ↦ n') x HA) as (a' & ? & ?);
            [ unfold extend_env; eapply env_agree_cons; [ exact Hρ | constructor; exact Hn | intros y Hy; exact Hy ]
            | exact Hf |];
          exists a'; split; [ econstructor; eassumption | assumption ]
      | IH : forall ρ0 m0, env_agree _ ?ρ ρ0 -> _ -> dsim ?v m0 -> exists _, _ /\ _,
        HA : env_agree _ ?ρ ?ρ', HB : forall c n B, In (c, n, B) _ -> env_agree _ ?ρ ?ρ', Hv : dsim ?v ?v'
        |- exists _, feval_ih _ _ _ _ _ _ (pt_self _ _) _ _ /\ _ =>
          let r' := fresh "r'" in
          destruct (IH ρ' v' HA HB Hv) as (r' & ? & ?); exists r'; split; [ constructor; assumption | assumption ]
      | Hu : dsim_list ?ups ?ups', Hρ : env_agree (fun x => ~ pt_fresh x (pt_pi _ _)) _ _,
        He : ⟦ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ ?b', Hb : dsim _ ?b' |- exists _, feval_shty _ _ _ _ _ _ _ /\ _ =>
          eexists; split; [ constructor; exact He | apply dsim_fam_pi; [ exact Hb | constructor; [ exact Hu |] ] ];
          let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
          intros y Hy; apply Hρ; cbn; intros [_ Hf]; exact (Hy Hf)
      | e : ⟦ ?Ps ⟧* _ ⍮ _ ⍮ _ ↘ ?bs, IH : forall ρ0, env_agree _ (env_args ?ρm (?bs ++ ?v :: nil)) ρ0 -> exists _, _ /\ _,
        HA : env_agree _ ?ρm ?ρm', Hbs : dsim_list ?bs ?bs', Hv : dsim ?v ?v' |- exists _, feval_ihty _ _ _ _ _ _ _ _ /\ _ =>
          let Hlb := fresh "Hlb" in
          assert (Hlb : List.length bs = List.length Ps) by (clear - e; induction e; cbn; congruence);
          destruct (IH (env_args ρm' (bs' ++ v' :: nil))) as (? & ? & ?);
            [ eapply env_agree_binders; [ exact HA | apply dsim_list_app; [ exact Hbs | repeat constructor; assumption ] |];
              rewrite length_app, Hlb; cbn; lia |];
          eexists; split; [ econstructor; eassumption | assumption ]
      | HA : env_agree _ ?ρm ?ρm', Hρ : env_agree (fun x => ~ pt_fresh x (pt_pi _ _)) _ _, Hv : dsim _ ?v',
        He : ⟦ _ ⟧ᶠ _ ⍮ _ ⍮ _ ↘ ?b', Hb : dsim _ ?b' |- exists _, feval_ihty _ _ _ _ _ _ ?v' _ /\ _ =>
          eexists; split; [ constructor; exact He | apply dsim_fam_pi; [ exact Hb | constructor; [ exact HA | | exact Hv ] ] ];
          let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
          intros y Hy; apply Hρ; cbn; intros [_ Hf]; exact (Hy Hf)
      end ].
    (** A member of a saturated body: the environment of its parameters,
        then of the body up to it, agree where the body may read. *)
    all: try match goal with
      | Hl : List.length ?args = List.length ?Δ, Hp : gm_prefix_upto ?Φ _ = Some (gm_ext ?Φ' _ _),
        IHb : forall ρ0 (P : nat -> Prop), (forall x, ~ gmod_fresh x ?Φ' -> P x) -> env_agree P (env_args ?ρ ?args) ρ0 -> _,
        Hρ : env_agree (fun x => ~ gunit_fresh x (gu_mk ?Δ (md_body ?Φ))) ?ρ ?ρ', Ha : dsim_list ?args ?args' |- _ =>
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
    (** A name a local open of a saturated body declares: the environment
        of the body before the open, then the target there, then the member
        the item names. *)
    all: try match goal with
      | Hl : List.length ?args = List.length ?Δ, Hi : gm_item_upto ?Φ _ = Some (?Φ0, ?H, _, _),
        IHb : forall ρ0 (P : nat -> Prop), (forall x, ~ gmod_fresh x ?Φ0 -> P x) -> env_agree P (env_args ?ρ ?args) ρ0 -> _,
        Hρ : env_agree (fun x => ~ gunit_fresh x (gu_mk ?Δ (md_body ?Φ))) ?ρ ?ρ', Ha : dsim_list ?args ?args' |- _ =>
          let HA := fresh "HA" in let HP := fresh "HP" in let ρ0' := fresh "ρ0'" in
          let Hb0 := fresh "Hb0" in let Hab := fresh "Hab" in
          assert (HA : env_agree (fun y => ~ gmod_fresh y Φ) (env_args ρ args) (env_args ρ' args'))
            by (eapply env_agree_args; [ exact Hρ | exact Ha |];
                let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                intros y Hy Hf; apply Hy; cbn in Hf; rewrite Hl; tauto);
          assert (HP : forall x, ~ gmod_fresh x Φ0 -> ~ gmod_fresh x Φ)
            by (let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
                intros x Hx Hf; apply Hx; apply (item_upto_fresh _ _ _ _ _ _ _ Hi) in Hf; cbn in Hf; tauto);
          destruct (IHb _ _ HP HA) as (ρ0' & Hb0 & Hab); clear IHb;
          match goal with
          | IHm : forall ρ1, env_agree (fun x => ~ modexp_fresh x H) ?ρ0 ρ1 -> exists _, _ /\ _ |- _ =>
              let Hq := fresh "Hq" in let h' := fresh "h'" in let Hh' := fresh "Hh'" in let Hhh := fresh "Hhh" in
              assert (Hq : env_agree (fun x => ~ modexp_fresh x H) ρ0 ρ0')
                by (eapply env_agree_mono; [ exact Hab | apply above_of ];
                    let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                    intros y Hy Hf; apply Hy; apply (item_upto_fresh _ _ _ _ _ _ _ Hi) in Hf; cbn in Hf; tauto);
              destruct (IHm _ Hq) as (h' & Hh' & Hhh); clear IHm;
              match goal with
              | IHs : forall h0, dmsim ?h h0 -> exists _, _ /\ _ |- _ =>
                  let r' := fresh "r'" in
                  destruct (IHs _ Hhh) as (r' & ? & ?); clear IHs;
                  eexists; split;
                    [ first [ eapply feval_sel_item | eapply feval_selm_item ]; (try len_tac); eassumption | eassumption ]
              end
          end
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
    (** A local open of a body: the body before it, then the entries it
        generates, which the kinds read alike in both environments. *)
    all: try match goal with
      | IH : forall ρ0 (P0 : nat -> Prop), (forall x, ~ gmod_fresh x ?Φ -> P0 x) -> env_agree P0 ?ρ ρ0 -> _,
        HQ : forall x, ~ gmod_fresh x (gm_open ?Φ _ _) -> ?P x, Hρ : env_agree ?P ?ρ ?ρ' |- _ =>
          let HP := fresh "HP" in
          assert (HP : forall x, ~ gmod_fresh x Φ -> P x)
            by (let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
                intros x Hx; apply HQ; intros Hf; apply Hx; cbn in Hf; tauto);
          destruct (IH _ _ HP Hρ) as (? & ? & ?); clear IH
      end.
    all: try match goal with
      | HQ : forall x, ~ gmod_fresh x (gm_open ?Φ ?H ?its) -> ?P x, Hk : kgens _ _ ?ρ1 ?H ?its ?gs,
        IH2 : forall ρ0 (P0 : nat -> Prop), (forall x, ~ gmod_fresh x (gens_append gm_nil 0 ?gs) -> P0 x) -> env_agree P0 ?ρ1 ρ0 -> _,
        Hab : env_agree (above (gm_binders ?Φ) ?P) ?ρ1 ?ρ1' |- _ =>
          let HH := fresh "HH" in let Hk' := fresh "Hk'" in let ρ2' := fresh "ρ2'" in
          let Hb2 := fresh "Hb2" in let Hab2 := fresh "Hab2" in
          assert (HH : forall x, ~ modexp_fresh x H -> above (gm_binders Φ) P x)
            by (apply above_of; let y := fresh "y" in let Hy := fresh "Hy" in let Hf := fresh "Hf" in
                intros y Hy; apply HQ; intros Hf; apply Hy; cbn in Hf; tauto);
          pose proof (proj2 (proj2 (proj2 (proj2 (kind_sim Θ Ξ)))) _ _ _ _ Hk _
                        (env_agree_mono _ _ _ _ Hab HH)) as Hk';
          destruct (IH2 ρ1' (above (gm_binders Φ) P)) as (ρ2' & Hb2 & Hab2);
            [ let x := fresh "x" in let Hx := fresh "Hx" in let Hf := fresh "Hf" in
              intros x Hx; apply HH; intros Hf; apply Hx;
              exact (gens_append_fresh gs gm_nil x I (kgens_entries_fresh _ _ _ _ _ _ Hk _ Hf))
            | exact Hab |];
          clear IH2;
          eexists; split; [ econstructor; eassumption |];
          rewrite gens_append_binders, Nat.add_0_r, (kgens_length _ _ _ _ _ _ Hk) in Hab2;
          cbn [gm_binders]; eapply env_agree_mono; [ exact Hab2 | intros z Hz; apply above_above_inv; exact Hz ]
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
  Proof. exact (proj1 (proj2 (feval_sim Θ Ξ))). Qed.

  (** A closure, at one or two related arguments. *)
  Lemma feval_clo_sim : forall B (ρ ρ' : env) c c' b,
      env_agree (fun x => ~ exp_fresh (S x) B) ρ ρ' -> dsim c c' -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c') ↘ b' /\ dsim b b'.
  Proof.
    intros * Hρ Hc Hb; eapply feval_exp_sim; [ exact Hb |].
    intros [| x] Hx; cbn; [ constructor; exact Hc | apply Hρ, Hx ].
  Qed.

  (** A closure that does not read its argument, at any argument. *)
  Lemma feval_clo_unread : forall B (ρ ρ' : env) c c' b,
      env_agree (fun x => ~ exp_fresh (S x) B) ρ ρ' -> exp_fresh 0 B -> ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c') ↘ b' /\ dsim b b'.
  Proof.
    intros * Hρ H0 Hb; eapply feval_exp_sim; [ exact Hb |].
    intros [| x] Hx; cbn; [ contradiction | apply Hρ, Hx ].
  Qed.

  Lemma feval_clo2_sim : forall B (ρ ρ' : env) c1 c1' c2 c2' b,
      env_agree (fun x => ~ exp_fresh (S (S x)) B) ρ ρ' -> dsim c1 c1' -> dsim c2 c2' ->
      ⟦ B ⟧ Θ ⍮ Ξ ⍮ ρ ↦ c1 ↦ c2 ↘ b ->
      exists b', ⟦ B ⟧ᶠ Θ ⍮ Ξ ⍮ (ρ' ↦ c1' ↦ c2') ↘ b' /\ dsim b b'.
  Proof.
    intros * Hρ Hc1 Hc2 Hb; eapply feval_exp_sim; [ exact Hb |].
    intros [| [| x]] Hx; cbn; [ constructor; exact Hc2 | constructor; exact Hc1 | apply Hρ, Hx ].
  Qed.

  (** The fresh variables of the telescopes of a declaration, from
      environments related everywhere. *)
  Lemma ffresh_tele_sim : forall ρ T s ns, fresh_tele Θ Ξ ρ T s ns ->
      forall ρ', env_agree (fun _ => True) ρ ρ' ->
      exists ns', ffresh_tele Θ Ξ ρ' T s ns' /\ dsim_list ns ns'.
  Proof.
    induction 1; intros ρ' Hρ; [ exists nil; split; constructor |].
    destruct (feval_exp_sim _ _ _ H ρ') as (a' & Ha' & Hsa); [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |].
    destruct (IHfresh_tele (ρ' ↦ ⇑! a' s)) as (ns' & ? & ?);
      [ apply env_agree_all_cons; [ exact Hρ | repeat constructor; assumption ] |].
    exists (⇑! a' s :: ns'); split; constructor; try eassumption; repeat constructor; assumption.
  Qed.

  Lemma feval_shty_sim : forall p ups ρ t a, eval_shty Θ Ξ p ups ρ t a -> forall ups' ρ',
      dsim_list ups ups' -> env_agree (fun x => ~ pt_fresh x t) ρ ρ' ->
      exists a', feval_shty Θ Ξ p ups' ρ' t a' /\ dsim a a'.
  Proof.
    intros * H; destruct (feval_sim Θ Ξ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs & _).
    exact (Hs _ _ _ _ _ H).
  Qed.

  Lemma feval_ihty_sim : forall ρm A ρ t m a, eval_ihty Θ Ξ ρm A ρ t m a -> forall ρm' ρ' m',
      env_agree (fun x => ~ exp_fresh (S (List.length (ptyp_ps t)) + x) A) ρm ρm' ->
      env_agree (fun x => ~ pt_fresh x t) ρ ρ' -> dsim m m' ->
      exists a', feval_ihty Θ Ξ ρm' A ρ' t m' a' /\ dsim a a'.
  Proof.
    intros * H; destruct (feval_sim Θ Ξ) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hy).
    exact (Hy _ _ _ _ _ _ H).
  Qed.

  Lemma ffresh_cargs_sim : forall p ups ρ gs s vs, fresh_cargs Θ Ξ p ups ρ gs s vs ->
      forall ups' ρ', dsim_list ups ups' -> env_agree (fun _ => True) ρ ρ' ->
      exists vs', ffresh_cargs Θ Ξ p ups' ρ' gs s vs' /\ dsim_list vs vs'.
  Proof.
    induction 1; intros ups' ρ' Hu Hρ.
    - exists nil; repeat constructor.
    - destruct (feval_exp_sim _ _ _ H ρ') as (a' & Ha' & Hsa); [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |].
      destruct (IHfresh_cargs ups' (ρ' ↦ ⇑! a' s)) as (vs' & ? & ?);
        [ exact Hu | apply env_agree_all_cons; [ exact Hρ | repeat constructor; assumption ] |].
      exists (⇑! a' s :: vs'); split; [ constructor; assumption | repeat constructor; assumption ].
    - destruct (feval_shty_sim _ _ _ _ _ H ups' ρ' Hu) as (a' & Ha' & Hsa);
        [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |].
      destruct (IHfresh_cargs ups' ρ' Hu Hρ) as (vs' & ? & ?).
      exists (⇑! a' s :: vs'); split; [ constructor; assumption | repeat constructor; assumption ].
  Qed.

  (** The recursive results of a branch [B]: related where [B] reads them,
      the head of [ihs] being the entry [List.length] of its tail. *)
  Lemma ffresh_ihs_sim : forall ρ A ρa gs vs s ihs, fresh_ihs Θ Ξ ρ A ρa gs vs s ihs ->
      forall B nn ρ' ρa' vs', env_agree (fun x => ~ exp_fresh (S nn + x) A) ρ ρ' ->
      env_agree (fun _ => True) ρa ρa' ->
      Forall (fun g => match g with ca_rec t => List.length (ptyp_ps t) = nn | ca_arg _ => True end) gs ->
      dsim_list vs vs' ->
      exists ihs', ffresh_ihs Θ Ξ ρ' A B ρa' gs vs' s ihs' /\ dsim_list_at (fun x => ~ exp_fresh x B) ihs ihs'.
  Proof.
    induction 1; intros B nn ρ' ρa' vs' HA Hρa Hl Hv.
    - inversion Hv; subst; exists nil; split; constructor.
    - inversion Hv; inversion Hl; subst.
      match goal with Hv1 : dsim v ?v1, Hv2 : dsim_list vs ?vs1, Hl2 : Forall _ gs |- _ =>
        destruct (IHfresh_ihs B nn ρ' (ρa' ↦ v1) vs1 HA ltac:(apply env_agree_all_cons; assumption) Hl2 Hv2)
          as (ihs' & ? & ?) end.
      exists ihs'; split; [ constructor; assumption | assumption ].
    - inversion_clear Hl as [| ? ? Hl1 Hl2]; cbn beta iota in Hl1; subst nn.
      inversion Hv; subst.
      pose proof (fresh_ihs_length _ _ _ _ _ _ _ H0) as Hlen.
      match goal with Hv1 : dsim v ?v1, Hv2 : dsim_list vs ?vs1 |- _ =>
        let a' := fresh "a'" in let ihs' := fresh "ihs'" in
        destruct (IHfresh_ihs B _ ρ' ρa' vs1 HA Hρa Hl2 Hv2) as (ihs' & ? & ?);
        destruct (exp_freshb (cargs_nrec gs) B) eqn:Ef;
        [ exists (⇑! 𝕌ω@0 s :: ihs'); split;
            [ apply ffresh_ihs_skip; assumption
            | constructor; [ intros Hr; exfalso; apply Hr; rewrite Hlen; apply exp_freshb_sound; exact Ef | assumption ] ]
        | destruct (feval_ihty_sim _ _ _ _ _ _ H ρ' ρa' v1) as (a' & ? & ?);
            [ exact HA | eapply env_agree_mono; [ exact Hρa | intros; exact I ] | exact Hv1 |];
          exists (⇑! a' s :: ihs'); split; [ apply ffresh_ihs_rec; assumption | constructor; [ intros _; repeat constructor; assumption | assumption ] ] ]
      end.
  Qed.

  (** Readback of related values gives the same normal form. *)
  Theorem fread_sim :
    (forall s n W, Rnf n in Θ ⍮ Ξ ⍮ s ↘ W -> forall n', dsim_nf n n' -> Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s m W, Rne m in Θ ⍮ Ξ ⍮ s ↘ W -> forall m', dsim_ne m m' -> Rneᶠ m' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s a W, Rtyp a in Θ ⍮ Ξ ⍮ s ↘ W -> forall a', dsim a a' -> Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W) /\
    (forall s xs ys, Rla xs in Θ ⍮ Ξ ⍮ s ↘ ys -> forall xs', dsim_la xs xs' -> Rlaᶠ xs' in Θ ⍮ Ξ ⍮ s ↘ ys) /\
    (forall s ρ T vs Ms, Rps vs at T in Θ ⍮ Ξ ⍮ ρ ⍮ s ↘ Ms -> forall ρ' vs',
       env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' -> Rpsᶠ vs' at T in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms) /\
    (forall s p ups ρ gs vs Ms, read_cargs Θ Ξ s p ups ρ gs vs Ms -> forall ups' ρ' vs',
       dsim_list ups ups' -> env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' -> fread_cargs Θ Ξ s p ups' ρ' gs vs' Ms) /\
    (forall s ρ A p D ups cs Bs Bs', read_brs Θ Ξ s ρ A p D ups cs Bs Bs' -> forall ρ' ups',
       env_agree (fun x => ~ exp_fresh (S (ind_nn D) + x) A) ρ ρ' ->
       (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
       dsim_list ups ups' -> fread_brs Θ Ξ s ρ' A p D ups' cs Bs Bs').
  Proof.
    apply (read_mut_ind Θ Ξ
      (fun s n W _ => forall n', dsim_nf n n' -> Rnfᶠ n' in Θ ⍮ Ξ ⍮ s ↘ W)
      (fun s m W _ => forall m', dsim_ne m m' -> Rneᶠ m' in Θ ⍮ Ξ ⍮ s ↘ W)
      (fun s a W _ => forall a', dsim a a' -> Rtypᶠ a' in Θ ⍮ Ξ ⍮ s ↘ W)
      (fun s xs ys _ => forall xs', dsim_la xs xs' -> Rlaᶠ xs' in Θ ⍮ Ξ ⍮ s ↘ ys)
      (fun s ρ T vs Ms _ => forall ρ' vs',
         env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' -> Rpsᶠ vs' at T in Θ ⍮ Ξ ⍮ ρ' ⍮ s ↘ Ms)
      (fun s p ups ρ gs vs Ms _ => forall ups' ρ' vs',
         dsim_list ups ups' -> env_agree (fun _ => True) ρ ρ' -> dsim_list vs vs' -> fread_cargs Θ Ξ s p ups' ρ' gs vs' Ms)
      (fun s ρ A p D ups cs Bs Bs' _ => forall ρ' ups',
         env_agree (fun x => ~ exp_fresh (S (ind_nn D) + x) A) ρ ρ' ->
         (forall c n B, In (c, n, B) Bs -> env_agree (fun x => ~ exp_fresh (n + x) B) ρ ρ') ->
         dsim_list ups ups' -> fread_brs Θ Ξ s ρ' A p D ups' cs Bs Bs'));
      intros;
      repeat match goal with
        | H : dsim_nf _ _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (_ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (_ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_ne (_ _ _ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim_la (_ :: _) _ |- _ => inversion H; subst; clear H
        | H : dsim_la nil _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _) _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim (_ _ _ _) _ |- _ => inversion H; subst; clear H
        | H : dsim ⊤ᵈ _ |- _ => inversion H; subst; clear H
        | H : dsim ⊥ᵈ _ |- _ => inversion H; subst; clear H
        | H : dsim_list (_ :: _) _ |- _ => inversion H; subst; clear H
        | H : dsim_list nil _ |- _ => inversion H; subst; clear H
        end.
    (** Inductive types.  A constructor, a type, and the parameters and
        arguments of each, at their types: the types are evaluated in
        environments related everywhere. *)
    all: try solve [ match goal with
      | IH1 : forall ρ0 vs0, env_agree _ nil ρ0 -> dsim_list ?as' vs0 -> Rpsᶠ vs0 at _ in _ ⍮ _ ⍮ ρ0 ⍮ _ ↘ ?Ps,
        IH2 : forall ups0 ρ0 vs0, dsim_list _ ups0 -> env_agree _ (env_args nil ?as') ρ0 -> dsim_list _ vs0 -> fread_cargs _ _ _ _ ups0 ρ0 _ vs0 ?Args,
        Ha : dsim_list ?as' ?as'', Hv : dsim_list ?vs ?vs' |- Rnfᶠ ⇓ (d_ind _ ?as'') (d_con _ _ ?vs') in _ ⍮ _ ⍮ _ ↘ nf_con _ _ (nfs_app ?Ps ?Args) =>
          econstructor; try eassumption;
            [ rewrite <- (dsim_list_length _ _ Ha); assumption
            | rewrite <- (dsim_list_length _ _ Hv); assumption
            | apply IH1; [ apply env_agree_nil | exact Ha ]
            | apply IH2; [ apply dsim_list_firstn, Ha | apply env_agree_all_args; [ apply env_agree_nil | exact Ha ] | apply dsim_list_skipn, Hv ] ]
      end ].
    all: try solve [ match goal with
      | IH : forall ρ0 vs0, env_agree _ nil ρ0 -> dsim_list ?as' vs0 -> Rpsᶠ vs0 at _ in _ ⍮ _ ⍮ ρ0 ⍮ _ ↘ ?Ps,
        Hps : Rps ?as' at _ in _ ⍮ _ ⍮ _ ⍮ _ ↘ ?Ps,
        Ha : dsim_list ?as' ?as'' |- Rtypᶠ d_ind _ ?as'' in _ ⍮ _ ⍮ _ ↘ nf_indty _ ?Ps =>
          destruct as'' as [| a0 as0];
          [ (** without arguments, by the rule that reads no declaration *)
            inversion Ha; subst; inversion Hps; subst; apply fread_typ_indty_nil
          | eapply fread_typ_indty; [ discriminate | eassumption | |];
            [ rewrite <- (dsim_list_length _ _ Ha); assumption | apply IH; [ apply env_agree_nil | exact Ha ] ] ]
      end ].
    all: try solve [ match goal with
      | e : ⟦ ?A ⟧ Θ ⍮ Ξ ⍮ ?ρ ↘ ?a, Hρ : env_agree (fun _ => True) ?ρ ?ρ',
        IHV : forall n0, dsim_nf (⇓ ?a ?v) n0 -> _, Hv : dsim ?v ?v' |- _ =>
          let a' := fresh "a'" in
          destruct (feval_exp_sim _ _ _ e ρ') as (a' & ? & ?);
            [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |];
          econstructor; [ eassumption | apply IHV; constructor; assumption |];
          match goal with IH : forall ρ0, _ |- _ => eapply IH; eauto with mctt end
      end ].
    all: try solve [ match goal with
      | e : eval_shty Θ Ξ _ ?ups ?ρ ?t ?a, Hρ : env_agree (fun _ => True) ?ρ ?ρ', Hu : dsim_list ?ups ?ups',
        IHV : forall n0, dsim_nf (⇓ ?a ?v) n0 -> _, Hv : dsim ?v ?v' |- _ =>
          let a' := fresh "a'" in
          destruct (feval_shty_sim _ _ _ _ _ e ups' ρ' Hu) as (a' & ? & ?);
            [ eapply env_agree_mono; [ exact Hρ | intros; exact I ] |];
          econstructor; [ eassumption | apply IHV; constructor; assumption |];
          match goal with IH : forall ups0 ρ0, _ |- _ => eapply IH; eauto with mctt end
      end ].
    (** A stuck eliminator: the motive under the fresh non-uniform
        parameters and scrutinee, and the branches. *)
    all: try solve [ match goal with
      | f : fresh_tele _ _ (env_args nil (firstn (ind_nu ?D) ?as')) _ ?s ?ns,
        e2 : ⟦ ?A ⟧ Θ ⍮ Ξ ⍮ env_args ?ρ (?ns ++ ⇑! (d_ind ?p _) _ :: nil) ↘ ?a,
        IHA : forall a0, dsim ?a a0 -> Rtypᶠ a0 in _ ⍮ _ ⍮ _ ↘ ?A',
        IHB : forall ρ0 ups0, _ -> _ -> dsim_list _ ups0 -> fread_brs _ _ _ ρ0 _ _ _ ups0 _ _ ?Bs',
        IHM : forall m0, dsim_ne ?m m0 -> Rneᶠ m0 in _ ⍮ _ ⍮ _ ↘ ?M,
        HA : forall x, ~ exp_fresh (?nm + x) ?A -> desim (env_entry ?ρ x) (env_entry ?ρ' x),
        HBs : forall c n B, In (c, n, B) ?Bs -> forall x, _ -> desim (env_entry ?ρ x) (env_entry ?ρ' x),
        Ha : dsim_list ?as' ?as'', Hm : dsim_ne ?m ?m'
        |- Rneᶠ d_elim ?ρ' ?nm ?A ?Bs ?p ?as'' ?m' in _ ⍮ _ ⍮ ?s ↘ ne_elim ?nm ?A' ?Bs' ?M =>
          let ns' := fresh "ns'" in let Hsn := fresh "Hsn" in let a' := fresh "a'" in let Hlen := fresh "Hlen" in
          pose proof (fresh_tele_length _ _ _ _ f) as Hlen; rewrite ind_nn_tele_length in Hlen;
          destruct (ffresh_tele_sim _ _ _ _ f (env_args nil (firstn (ind_nu D) as''))) as (ns' & ? & Hsn);
            [ apply env_agree_all_args; [ apply env_agree_nil | apply dsim_list_firstn, Ha ] |];
          destruct (feval_exp_sim _ _ _ e2 (env_args ρ' (ns' ++ ⇑! (d_ind p (firstn (ind_nu D) as'' ++ ns')) (s + ind_nn D) :: nil)))
            as (a' & ? & ?);
            [ eapply env_agree_binders;
                [ exact HA
                | apply dsim_list_app; [ exact Hsn | repeat constructor; apply dsim_list_app; [ apply dsim_list_firstn, Ha | exact Hsn ] ]
                | rewrite length_app, Hlen; cbn; lia ]
            |];
          econstructor; try eassumption; try reflexivity;
            [ rewrite <- (dsim_list_length _ _ Ha); assumption
            | apply IHA; assumption
            | apply IHB; [ exact HA | exact HBs | apply dsim_list_firstn, Ha ]
            | apply IHM; assumption ]
      end ].
    (** A branch: under the fresh non-uniform parameters, arguments and
        recursive results. *)
    all: try solve [ match goal with
      | e : ?n = (ind_nn ?D + List.length ?gs + cargs_nrec ?gs)%nat,
        f : fresh_tele _ _ (env_args nil ?ups) _ ?s ?ns,
        f0 : fresh_cargs _ _ ?p ?ups (env_args nil (?ups ++ ?ns)) ?gs _ ?vs,
        Hpl : cargs_plen (ind_nn ?D) ?gs,
        f2 : fresh_ihs _ _ ?ρ ?A _ ?gs ?vs _ ?ihs,
        e0 : ⟦ ?B ⟧ Θ ⍮ Ξ ⍮ env_args ?ρ (?ns ++ ?vs ++ ?ihs) ↘ ?b,
        e1 : ⟦ ?A ⟧ Θ ⍮ Ξ ⍮ env_args ?ρ (?ns ++ d_con ?p ?c _ :: nil) ↘ ?t,
        IHV : forall n0, dsim_nf (⇓ ?t ?b) n0 -> _,
        IHT : forall ρ0 ups0, _ -> _ -> dsim_list ?ups ups0 -> fread_brs _ _ _ ρ0 _ _ _ ups0 _ _ _,
        HA : env_agree (fun x => ~ exp_fresh (S (ind_nn ?D) + x) ?A) ?ρ ?ρ',
        HBs : forall c n B, In (c, n, B) (_ :: _) -> env_agree _ ?ρ ?ρ',
        Hu : dsim_list ?ups ?ups' |- _ =>
          let ns' := fresh "ns'" in let vs' := fresh "vs'" in let ihs' := fresh "ihs'" in
          let Hsn := fresh "Hsn" in let Hsv := fresh "Hsv" in let Hsi := fresh "Hsi" in
          let b' := fresh "b'" in let t' := fresh "t'" in
          let Hl1 := fresh "Hl" in let Hl2 := fresh "Hl" in let Hl3 := fresh "Hl" in
          pose proof (fresh_tele_length _ _ _ _ f) as Hl1; rewrite ind_nn_tele_length in Hl1;
          pose proof (fresh_cargs_length _ _ _ _ _ _ f0) as Hl2;
          pose proof (fresh_ihs_length _ _ _ _ _ _ _ f2) as Hl3;
          destruct (ffresh_tele_sim _ _ _ _ f (env_args nil ups')) as (ns' & ? & Hsn);
            [ apply env_agree_all_args; [ apply env_agree_nil | exact Hu ] |];
          destruct (ffresh_cargs_sim _ _ _ _ _ _ f0 ups' (env_args nil (ups' ++ ns'))) as (vs' & ? & Hsv);
            [ exact Hu | apply env_agree_all_args; [ apply env_agree_nil | apply dsim_list_app; assumption ] |];
          destruct (ffresh_ihs_sim _ _ _ _ _ _ _ f2 B (ind_nn D) ρ' (env_args nil (ups' ++ ns')) vs' HA
                      ltac:(apply env_agree_all_args; [ apply env_agree_nil | apply dsim_list_app; assumption ])
                      (plen_forall _ _ Hpl) Hsv) as (ihs' & ? & Hsi);
          destruct (feval_exp_sim _ _ _ e0 (env_args ρ' (ns' ++ vs' ++ ihs'))) as (b' & ? & ?);
            [ eapply env_agree_binders_at;
                [ exact (HBs _ _ _ (or_introl eq_refl))
                | apply dsim_list_at_app; [ exact Hsn | apply dsim_list_at_app; assumption ]
                | rewrite !length_app, Hl1, Hl2, Hl3; lia ]
            |];
          destruct (feval_exp_sim _ _ _ e1 (env_args ρ' (ns' ++ d_con p c (ups' ++ ns' ++ vs') :: nil))) as (t' & ? & ?);
            [ eapply env_agree_binders;
                [ exact HA
                | apply dsim_list_app; [ exact Hsn | repeat constructor; apply dsim_list_app; [ exact Hu | apply dsim_list_app; assumption ] ]
                | rewrite length_app, Hl1; cbn; lia ]
            |];
          econstructor; try eassumption;
            [ apply IHV; constructor; assumption
            | apply IHT; [ exact HA | intros c1 n1 B1 Hin; exact (HBs c1 n1 B1 (or_intror Hin)) | exact Hu ] ]
      end ].
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
