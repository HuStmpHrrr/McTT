(** * Builtin Bindings

    [builtin natural ≔ X] binds the inductive type [X] as the natural
    numbers.  The binding is a piece of configuration, [builtins], apart
    from the filed units and the stack: no typing judgment reads it.  The
    command semantics threads it through a run ([Core.Syntactic.System.Command]),
    and it holds for the rest of the run, in every unit.

    Where a binding is made, a numeral ([a_nlit]) stands for the chain of
    the bound type's constructors and the token [ℕ] ([a_ntok]) for its type
    former: when a command runs, its literals are generated from the
    binding ([cmd_lits]).  Without a binding a literal is an error.  A
    literal has no typing, evaluation or readback rule. *)

From Stdlib Require Import List String Bool.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Export Inductives Members Command.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** The kind of the binding, as the command names it. *)
Definition nat_kind : string := "natural".

(** The shape of the natural numbers: no parameter, and two constructors,
    one without arguments, [z], and one with a single recursive argument,
    [s], in either order. *)
Definition nat_shape (D : ind_decl) : option (string * string) :=
  match ind_nu D, ind_params D, ind_cons D with
  | 0, nil, (c1, nil) :: (c2, ca_rec (pt_self 0 nil) :: nil) :: nil => Some (c1, c2)
  | 0, nil, (c2, ca_rec (pt_self 0 nil) :: nil) :: (c1, nil) :: nil => Some (c1, c2)
  | _, _, _ => None
  end.

(** The sort the natural numbers are declared in: [Type@0]. *)
Definition nat_sort : typ := a_univ (a_llit (0, 0)).

(** ** The Configuration *)

(** The builtin bindings of a run: the path of the type bound as the
    natural numbers, if one is. *)
Record builtins : Set := mk_builtins { bt_nat : option qname }.

Definition bt_empty : builtins := mk_builtins None.

(** A binding is well formed where its type is an inductive type of the
    shape of the natural numbers, in [Type@0], filed or on the stack.  This
    is a condition on its own, not part of typing. *)
Definition builtins_wf (Θ : gdeps) (Ξ : gstack) (B : builtins) : Prop :=
  forall p, bt_nat B = Some p ->
    exists D z s, ind_lookup Θ Ξ p = Some D /\ nat_shape D = Some (z, s) /\ ind_sort D = nat_sort.

(** What a literal stands for at a state: the bound type and its
    constructors, the one without arguments first. *)
Definition nat_view (Θ : gdeps) (Ξ : gstack) (B : builtins) : option (qname * string * string) :=
  match bt_nat B with
  | Some p =>
      match ind_lookup Θ Ξ p with
      | Some D =>
          match nat_shape D with
          | Some (z, s) => Some (p, z, s)
          | None => None
          end
      | None => None
      end
  | None => None
  end.

(** The numeral [n] as the chain of the constructors [z] and [s] of [p]. *)
Fixpoint nat_chain (p : qname) (z s : string) (n : nat) : exp :=
  match n with
  | 0 => a_con p z
  | S n' => a_app (a_con p s) (nat_chain p z s n')
  end.

(** ** Literals *)

(** Why the literals of a command cannot be generated: a numeral, or the
    token [ℕ], with no natural-number type bound. *)
Inductive lerr : Set :=
| le_num : nat -> lerr
| le_tok : lerr.

Inductive lres (A : Type) : Type :=
| lok : A -> lres A
| lfail : lerr -> lres A.

Arguments lok {A}.
Arguments lfail {A}.

Definition lbind {A B} (m : lres A) (f : A -> lres B) : lres B :=
  match m with
  | lok a => f a
  | lfail e => lfail e
  end.

#[local] Notation "'let%' x ':=' m 'in' f" := (lbind m (fun x => f))
  (at level 200, x name, m at level 100, f at level 200, right associativity).

Definition lopt {A} (f : A -> lres A) (o : option A) : lres (option A) :=
  match o with
  | Some a => let% a' := f a in lok (Some a')
  | None => lok None
  end.

Fixpoint lmap {A B} (f : A -> lres B) (l : list A) : lres (list B) :=
  match l with
  | nil => lok nil
  | a :: l' => let% b := f a in let% bs := lmap f l' in lok (b :: bs)
  end.

Section Literals.
  (** The bound type and its constructors, if any. *)
  Variable nv : option (qname * string * string).

  Fixpoint exp_lits (M : exp) {struct M} : lres exp :=
    match M with
    | a_typ _ | a_level _ | a_llit _ | a_True | a_true | a_False | a_var _ | a_ind _ | a_con _ _ => lok M
    | a_ntok =>
        match nv with
        | Some (p, _, _) => lok (a_ind p)
        | None => lfail le_tok
        end
    | a_nlit n =>
        match nv with
        | Some (p, z, s) => lok (nat_chain p z s n)
        | None => lfail (le_num n)
        end
    | a_univ M => let% M' := exp_lits M in lok (a_univ M')
    | a_succl M => let% M' := exp_lits M in lok (a_succl M')
    | a_maxl M N => let% M' := exp_lits M in let% N' := exp_lits N in lok (a_maxl M' N')
    | a_exfalso A M => let% A' := exp_lits A in let% M' := exp_lits M in lok (a_exfalso A' M')
    | a_elim nm A Bs M =>
        let% A' := exp_lits A in
        let% Bs' := (fix brs_lits (Bs : list (String.string * nat * exp)) : lres (list (String.string * nat * exp)) :=
                       match Bs with
                       | nil => lok nil
                       | b :: Bs0 =>
                           let% B' := exp_lits (snd b) in
                           let% Bs0' := brs_lits Bs0 in
                           lok ((fst b, B') :: Bs0')
                       end) Bs in
        let% M' := exp_lits M in
        lok (a_elim nm A' Bs' M')
    | a_pi A B => let% A' := exp_lits A in let% B' := exp_lits B in lok (a_pi A' B')
    | a_fn A M => let% A' := exp_lits A in let% M' := exp_lits M in lok (a_fn A' M')
    | a_app M N => let% M' := exp_lits M in let% N' := exp_lits N in lok (a_app M' N')
    | a_let b B => let% b' := bnd_lits b in let% B' := exp_lits B in lok (a_let b' B')
    | a_mem H x => let% H' := modexp_lits H in lok (a_mem H' x)
    end
  with modexp_lits (H : modexp) {struct H} : lres modexp :=
    match H with
    | me_unit _ | me_var _ => lok H
    | me_mem H y => let% H' := modexp_lits H in lok (me_mem H' y)
    | me_app H N => let% H' := modexp_lits H in let% N' := exp_lits N in lok (me_app H' N')
    | me_lit U => let% U' := gunit_lits U in lok (me_lit U')
    end
  with bnd_lits (b : bnd) {struct b} : lres bnd :=
    match b with
    | b_def oA M => let% oA' := lopt exp_lits oA in let% M' := exp_lits M in lok (b_def oA' M')
    | b_mod U => let% U' := gunit_lits U in lok (b_mod U')
    end
  with gunit_lits (U : gunit) {struct U} : lres gunit :=
    match U with
    | gu_mk Δ D =>
        let% Δ' := (fix tele_lits (Δ : list centry) : lres ctx :=
                      match Δ with
                      | nil => lok nil
                      | e :: Δ0 => let% e' := centry_lits e in let% Δ0' := tele_lits Δ0 in lok (e' :: Δ0')
                      end) Δ in
        let% D' := moddef_lits D in
        lok (gu_mk Δ' D')
    end
  with moddef_lits (D : moddef) {struct D} : lres moddef :=
    match D with
    | md_body Φ => let% Φ' := gmod_lits Φ in lok (md_body Φ')
    | md_alias E => let% E' := modexp_lits E in lok (md_alias E')
    end
  with gmod_lits (Φ : gmod) {struct Φ} : lres gmod :=
    match Φ with
    | gm_nil => lok gm_nil
    | gm_ext Φ x E => let% Φ' := gmod_lits Φ in let% E' := gentry_lits E in lok (gm_ext Φ' x E')
    | gm_open Φ H its => let% Φ' := gmod_lits Φ in let% H' := modexp_lits H in lok (gm_open Φ' H' its)
    end
  with gentry_lits (E : gentry) {struct E} : lres gentry :=
    match E with
    | ge_def b pv A B => let% A' := exp_lits A in let% B' := lopt exp_lits B in lok (ge_def b pv A' B')
    | ge_mod pv U => let% U' := gunit_lits U in lok (ge_mod pv U')
    | ge_ind _ _ _ | ge_ind_alias _ _ _ _ => lok E
    end
  with centry_lits (e : centry) {struct e} : lres centry :=
    match e with
    | ce_ass A => let% A' := exp_lits A in lok (ce_ass A')
    | ce_def A M => let% A' := exp_lits A in let% M' := exp_lits M in lok (ce_def A' M')
    | ce_mod U => let% U' := gunit_lits U in lok (ce_mod U')
    end.

  Definition tele_lits (Δ : ctx) : lres ctx := lmap centry_lits Δ.

  (** A declaration as written. *)
  Definition decl_lits (R : raw_decl) : lres raw_decl :=
    let% Δ' := tele_lits (rd_params R) in
    let% A' := exp_lits (rd_sort R) in
    let% cs' := lmap (fun cg => let% args := lmap (fun yT => let% T' := exp_lits (snd yT) in lok (fst yT, T')) (snd cg) in
                                lok (fst cg, args)) (rd_cons R) in
    lok (mk_raw (rd_nu R) Δ' A' cs').

  (** A command's own terms: the nested commands of a module get their
      literals when they run. *)
  Definition cmd_lits (c : ccmd) : lres ccmd :=
    match c with
    | cc_def x b pv A M => let% A' := exp_lits A in let% M' := lopt exp_lits M in lok (cc_def x b pv A' M')
    | cc_mod x pv Δ cs => let% Δ' := tele_lits Δ in lok (cc_mod x pv Δ' cs)
    | cc_alias x pv Δ E => let% Δ' := tele_lits Δ in let% E' := modexp_lits E in lok (cc_alias x pv Δ' E')
    | cc_load fp => lok (cc_load fp)
    | cc_open E its => let% E' := modexp_lits E in lok (cc_open E' its)
    | cc_eval M oA => let% M' := exp_lits M in let% oA' := lopt exp_lits oA in lok (cc_eval M' oA')
    | cc_ind x pv D => let% D' := decl_lits D in lok (cc_ind x pv D')
    | cc_builtin k H => let% H' := modexp_lits H in lok (cc_builtin k H')
    | cc_ind_alias x pv Δ H => let% Δ' := tele_lits Δ in let% H' := modexp_lits H in lok (cc_ind_alias x pv Δ' H')
    end.
End Literals.

(** The literals of a command at a state. *)
Definition cmd_lits_ok (Θ : gdeps) (Ξ : gstack) (B : builtins) (c c' : ccmd) : Prop :=
  cmd_lits (nat_view Θ Ξ B) c = lok c'.

Definition tele_lits_ok (Θ : gdeps) (Ξ : gstack) (B : builtins) (Δ Δ' : ctx) : Prop :=
  tele_lits (nat_view Θ Ξ B) Δ = lok Δ'.

(** ** Binding *)

(** The binding a [builtin natural ≔ X] command makes, from the bindings
    before it: [X] names the inductive type [p], with the shape of the
    natural numbers, in [Type@0]; [p] is bound unless another type is. *)
Definition bt_bind_nat (B : builtins) (p : qname) : option builtins :=
  match bt_nat B with
  | None => Some (mk_builtins (Some p))
  | Some p0 => if qname_eq_dec p0 p then Some B else None
  end.

Lemma bt_bind_nat_bound : forall B p B', bt_bind_nat B p = Some B' -> bt_nat B' = Some p.
Proof.
  intros [[p0 |]] p B' H; unfold bt_bind_nat in H; cbn in H; [| injection H as <-; reflexivity ].
  destruct (qname_eq_dec p0 p) as [-> |]; [ injection H as <-; reflexivity | discriminate ].
Qed.

(** ** Bindings Only Grow

    A run makes a binding at most once ([bt_bind_nat] rebinds only the same
    type), so the bindings of any two points of a run agree where both are
    made ([bt_compat]), and those of an earlier point are below those of a
    later one ([bt_le]). *)

Definition bt_compat (B1 B2 : builtins) : Prop :=
  forall p1 p2, bt_nat B1 = Some p1 -> bt_nat B2 = Some p2 -> p1 = p2.

Definition bt_le (B1 B2 : builtins) : Prop := bt_nat B1 = None \/ B1 = B2.

Lemma bt_le_refl : forall B, bt_le B B.
Proof. right; reflexivity. Qed.

Lemma bt_le_trans : forall B1 B2 B3, bt_le B1 B2 -> bt_le B2 B3 -> bt_le B1 B3.
Proof. intros * [H | <-] H2; [ left; exact H | exact H2 ]. Qed.

Lemma bt_le_compat : forall B1 B2 B, bt_le B1 B -> bt_le B2 B -> bt_compat B1 B2.
Proof. intros * [H1 | <-] [H2 | <-] p1 p2 E1 E2; congruence. Qed.

Lemma bt_compat_refl : forall B, bt_compat B B.
Proof. intros B p1 p2 E1 E2; congruence. Qed.

Lemma bt_compat_sym : forall B1 B2, bt_compat B1 B2 -> bt_compat B2 B1.
Proof. intros * H p1 p2 E1 E2; symmetry; exact (H _ _ E2 E1). Qed.

Lemma bt_bind_nat_le : forall B p B', bt_bind_nat B p = Some B' -> bt_le B B'.
Proof.
  intros [[p0 |]] p B' H; unfold bt_bind_nat in H; cbn in H; [| left; reflexivity ].
  destruct (qname_eq_dec p0 p); [ injection H as <-; apply bt_le_refl | discriminate ].
Qed.

Lemma bt_bind_nat_compat : forall B1 B2 p B1' B2',
    bt_bind_nat B1 p = Some B1' -> bt_bind_nat B2 p = Some B2' -> bt_compat B1' B2'.
Proof.
  intros * H1 H2 p1 p2 E1 E2; rewrite (bt_bind_nat_bound _ _ _ H1) in E1; rewrite (bt_bind_nat_bound _ _ _ H2) in E2; congruence.
Qed.

(** The views of compatible bindings at a state: one has no binding, or
    they are the same. *)
Definition nv_compat (nv1 nv2 : option (qname * string * string)) : Prop :=
  nv1 = None \/ nv2 = None \/ nv1 = nv2.

Lemma nat_view_compat : forall Θ Ξ B1 B2, bt_compat B1 B2 -> nv_compat (nat_view Θ Ξ B1) (nat_view Θ Ξ B2).
Proof.
  intros * H; unfold nat_view, nv_compat.
  destruct (bt_nat B1) as [p |] eqn:E1; [| left; reflexivity ].
  destruct (bt_nat B2) as [p2 |] eqn:E2; [| right; left; reflexivity ].
  rewrite (H _ _ E1 E2); right; right; reflexivity.
Qed.

(** ** Literals Without a Binding

    The literals of a term generated with no binding succeed only where
    there is none, and then leave it as it is, whatever the binding. *)

Lemma lbind_lok_inv : forall {A B} (m : lres A) (k : A -> lres B) r, lbind m k = lok r -> exists a, m = lok a /\ k a = lok r.
Proof. intros * H; destruct m; cbn in H; [ eauto | discriminate ]. Qed.

Lemma lits_none_all :
  (forall M M', exp_lits None M = lok M' -> forall nv, exp_lits nv M = lok M') /\
  (forall H H', modexp_lits None H = lok H' -> forall nv, modexp_lits nv H = lok H') /\
  (forall b b', bnd_lits None b = lok b' -> forall nv, bnd_lits nv b = lok b') /\
  (forall U U', gunit_lits None U = lok U' -> forall nv, gunit_lits nv U = lok U') /\
  (forall D D', moddef_lits None D = lok D' -> forall nv, moddef_lits nv D = lok D') /\
  (forall Φ Φ', gmod_lits None Φ = lok Φ' -> forall nv, gmod_lits nv Φ = lok Φ') /\
  (forall E E', gentry_lits None E = lok E' -> forall nv, gentry_lits nv E = lok E') /\
  (forall e e', centry_lits None e = lok e' -> forall nv, centry_lits nv e = lok e').
Proof.
  apply syn_mut_ind; intros; cbn [exp_lits modexp_lits bnd_lits gunit_lits moddef_lits gmod_lits gentry_lits centry_lits] in *;
    try discriminate.
  all: try solve [ injection H as <-; reflexivity ].
  all: repeat match goal with
    | H : lbind _ _ = lok _ |- _ =>
        let E := fresh "E" in let a := fresh "a" in apply lbind_lok_inv in H as (a & E & H)
    end.
  all: repeat match goal with
    | E : ?f None ?x = lok ?y, IH : forall _, ?f None ?x = lok _ -> forall _, ?f _ ?x = lok _ |- _ =>
        rewrite (IH _ E); cbn [lbind]; clear E
    end.
  all: try (match goal with H : lok _ = lok _ |- _ => injection H as <- end; reflexivity).
  - (* the branches of an eliminator *)
    enough (HB : forall Bs', (fix brs_lits (Bs0 : list (string * nat * typ)) : lres (list (string * nat * typ)) :=
        match Bs0 with
        | nil => lok nil
        | b :: Bs1 => lbind (exp_lits None (snd b)) (fun B' => lbind (brs_lits Bs1) (fun Bs0' => lok ((fst b, B') :: Bs0')))
        end) Bs = lok Bs' ->
      (fix brs_lits (Bs0 : list (string * nat * typ)) : lres (list (string * nat * typ)) :=
        match Bs0 with
        | nil => lok nil
        | b :: Bs1 => lbind (exp_lits nv (snd b)) (fun B' => lbind (brs_lits Bs1) (fun Bs0' => lok ((fst b, B') :: Bs0')))
        end) Bs = lok Bs')
      by (rewrite (HB _ E0); cbn [lbind]; exact H2).
    clear - H0; induction H0 as [| b Bs Hb HF IH]; intros Bs' E; cbn in E |- *; [ exact E |].
    apply lbind_lok_inv in E as (B' & E1 & E); apply lbind_lok_inv in E as (Bs1 & E2 & E).
    rewrite (Hb _ E1); cbn [lbind]; rewrite (IH _ E2); exact E.
  - (* a definition binding: its type, if annotated *)
    destruct oA as [A |]; cbn [lopt] in E |- *; [| injection E as <-; exact H1 ].
    apply lbind_lok_inv in E as (A' & E1 & E); rewrite (H A eq_refl _ E1); cbn [lbind]; injection E as <-; exact H1.
  - (* a unit: its telescope *)
    enough (HT : forall Δ', (fix tele_lits (Δ0 : ctx) : lres ctx :=
        match Δ0 with
        | nil => lok ⋅
        | e :: Δ1 => lbind (centry_lits None e) (fun e' => lbind (tele_lits Δ1) (fun Δ0' => lok (e' :: Δ0')))
        end) Δ = lok Δ' ->
      (fix tele_lits (Δ0 : ctx) : lres ctx :=
        match Δ0 with
        | nil => lok ⋅
        | e :: Δ1 => lbind (centry_lits nv e) (fun e' => lbind (tele_lits Δ1) (fun Δ0' => lok (e' :: Δ0')))
        end) Δ = lok Δ')
      by (rewrite (HT _ E); cbn [lbind]; exact H1).
    clear - H; induction H as [| e Δ He HF IH]; intros Δ' E; cbn in E |- *; [ exact E |].
    apply lbind_lok_inv in E as (e' & E1 & E); apply lbind_lok_inv in E as (Δ1 & E2 & E).
    rewrite (He _ E1); cbn [lbind]; rewrite (IH _ E2); exact E.
  - (* an entry: its body, if any *)
    destruct B as [M |]; cbn [lopt] in E0 |- *; [| injection E0 as <-; exact H1 ].
    apply lbind_lok_inv in E0 as (M' & E1 & E0); rewrite (H0 M eq_refl _ E1); cbn [lbind]; injection E0 as <-; exact H1.
Qed.

Lemma lmap_mono : forall {A B} (f g : A -> lres B),
    (forall a b, f a = lok b -> g a = lok b) ->
    forall l l', lmap f l = lok l' -> lmap g l = lok l'.
Proof.
  intros A B f g Hf; induction l as [| a l IH]; intros l' E; cbn in E |- *; [ exact E |].
  apply lbind_lok_inv in E as (b & E1 & E); apply lbind_lok_inv in E as (l1 & E2 & E).
  rewrite (Hf _ _ E1); cbn [lbind]; rewrite (IH _ E2); exact E.
Qed.

Lemma lopt_mono : forall {A} (f g : A -> lres A),
    (forall a b, f a = lok b -> g a = lok b) ->
    forall o o', lopt f o = lok o' -> lopt g o = lok o'.
Proof.
  intros A f g Hf [a |] o' E; cbn in E |- *; [| exact E ].
  apply lbind_lok_inv in E as (b & E1 & E); rewrite (Hf _ _ E1); exact E.
Qed.

Lemma tele_lits_none : forall Δ Δ', tele_lits None Δ = lok Δ' -> forall nv, tele_lits nv Δ = lok Δ'.
Proof.
  intros Δ Δ' E nv; refine (lmap_mono _ _ _ _ _ E).
  intros; eapply lits_none_all; eassumption.
Qed.

Lemma cmd_lits_none : forall c c', cmd_lits None c = lok c' -> forall nv, cmd_lits nv c = lok c'.
Proof.
  pose proof lits_none_all as (He & Hm & _).
  intros c c' Ec nv; destruct c; cbn [cmd_lits] in *; unfold decl_lits in *;
    repeat match goal with
      | H : lbind _ _ = lok _ |- _ =>
          let E := fresh "E" in let a := fresh "a" in apply lbind_lok_inv in H as (a & E & H)
      end;
    repeat match goal with
      | E : exp_lits None ?x = lok _ |- _ => rewrite (He _ _ E); cbn [lbind]; clear E
      | E : modexp_lits None ?x = lok _ |- _ => rewrite (Hm _ _ E); cbn [lbind]; clear E
      | E : lopt (exp_lits None) ?x = lok _ |- _ =>
          rewrite (lopt_mono _ (exp_lits nv) (fun a b H => He a b H nv) _ _ E); cbn [lbind]; clear E
      | E : tele_lits None ?x = lok _ |- _ => rewrite (tele_lits_none _ _ E); cbn [lbind]; clear E
      end; try exact Ec.
  (* the constructors of a declaration *)
  injection E as <-.
  lazymatch goal with E2 : lmap ?f ?l = lok ?l' |- context [lmap ?g ?l] =>
    assert (Hc : lmap g l = lok l') by (refine (lmap_mono f g _ _ _ E2); clear E2;
      intros cg cg' E; apply lbind_lok_inv in E as (args & E1 & E);
      match goal with E1 : lmap ?f1 ?l1 = lok ?l1' |- context [lmap ?g1 ?l1] =>
        rewrite (lmap_mono f1 g1 (fun yT yT' E2 => ltac:(apply lbind_lok_inv in E2 as (T' & E3 & E2);
                                                          rewrite (He _ _ E3); exact E2)) _ _ E1); exact E end)
  end.
  rewrite Hc; exact Ec.
Qed.

(** So the literals generated at compatible views are the same. *)
Lemma cmd_lits_agree : forall nv1 nv2 c c1 c2, nv_compat nv1 nv2 ->
    cmd_lits nv1 c = lok c1 -> cmd_lits nv2 c = lok c2 -> c1 = c2.
Proof.
  intros * [-> | [-> | ->]] E1 E2.
  - rewrite (cmd_lits_none _ _ E1) in E2; congruence.
  - rewrite (cmd_lits_none _ _ E2) in E1; congruence.
  - congruence.
Qed.

Lemma tele_lits_agree : forall nv1 nv2 Δ Δ1 Δ2, nv_compat nv1 nv2 ->
    tele_lits nv1 Δ = lok Δ1 -> tele_lits nv2 Δ = lok Δ2 -> Δ1 = Δ2.
Proof.
  intros * [-> | [-> | ->]] E1 E2.
  - rewrite (tele_lits_none _ _ E1) in E2; congruence.
  - rewrite (tele_lits_none _ _ E2) in E1; congruence.
  - congruence.
Qed.

(** ** Literals and Bindings at Larger Bindings

    A command whose literals were generated with some bindings has the same
    literals with larger ones, and a binding made that ends below some
    bindings is made by them as well. *)

Lemma nat_view_none : forall Θ Ξ B, bt_nat B = None -> nat_view Θ Ξ B = None.
Proof. intros * H; unfold nat_view; rewrite H; reflexivity. Qed.

Lemma cmd_lits_ok_le : forall Θ Ξ B1 B c c1, bt_le B1 B -> cmd_lits_ok Θ Ξ B1 c c1 -> cmd_lits_ok Θ Ξ B c c1.
Proof.
  intros * [Hn | <-] H; [| exact H ]; unfold cmd_lits_ok in *.
  rewrite (nat_view_none _ _ _ Hn) in H; exact (cmd_lits_none _ _ H _).
Qed.

Lemma tele_lits_ok_le : forall Θ Ξ B1 B Δ Δ1, bt_le B1 B -> tele_lits_ok Θ Ξ B1 Δ Δ1 -> tele_lits_ok Θ Ξ B Δ Δ1.
Proof.
  intros * [Hn | <-] H; [| exact H ]; unfold tele_lits_ok in *.
  rewrite (nat_view_none _ _ _ Hn) in H; exact (tele_lits_none _ _ H _).
Qed.

Lemma bt_bind_nat_up : forall B1 p B1' B, bt_bind_nat B1 p = Some B1' -> bt_le B1' B -> bt_bind_nat B p = Some B.
Proof.
  intros * Hb [Hn | <-].
  - rewrite (bt_bind_nat_bound _ _ _ Hb) in Hn; discriminate.
  - pose proof (bt_bind_nat_bound _ _ _ Hb) as Hp; unfold bt_bind_nat; rewrite Hp.
    destruct (qname_eq_dec p p) as [_ | Hne]; [ reflexivity | contradiction ].
Qed.

(** Whether a sort is [nat_sort]. *)
Definition is_nat_sort (A : exp) : bool :=
  match A with
  | a_univ (a_llit (0, 0)) => true
  | _ => false
  end.

Lemma is_nat_sort_spec : forall A, is_nat_sort A = true <-> A = nat_sort.
Proof.
  intros A; split; [| intros ->; reflexivity ].
  destruct A; try discriminate; cbn.
  destruct A; try discriminate.
  destruct o as [[| a] [| b]]; try discriminate; reflexivity.
Qed.
