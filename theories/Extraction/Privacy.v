(** * Checking Privacy

    [refs_check] decides [acc_ok]: every table is computed, so a reference is
    checked by reading the entry it names, and a failure names the module
    that declares the private member and the member. *)

From Stdlib Require Import List String.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.System Require Import Definitions Privacy.
Import Syntax_Notations.
#[local] Open Scope list_scope.

(** A private member out of reach: declared in the module of a unit, or
    an entry of a local body, at the chain of submodules [ch] from the local
    module. *)
Inductive priv_err : Set :=
| pe_global : qname -> string -> priv_err
| pe_local : list string -> string -> priv_err.

Definition bn_err (nm : bname) (x : string) : priv_err :=
  match nm with
  | bn_glob p => pe_global p x
  | bn_local ch => pe_local ch x
  end.

Definition tab_check (t : ptab) (x : string) : { e : priv_err | ~ tab_ok t x } + { tab_ok t x }.
Proof.
  destruct t as [| fp ch | nm es | t]; cbn; try (right; exact I).
  destruct (option_map fst (tab_find x es)) as [[|] |] eqn:E.
  - left; exists (bn_err nm x); intros Hn; apply Hn; reflexivity.
  - right; discriminate.
  - right; discriminate.
Defined.

Section PrivacyImpl.
  Variables (Θ : gctx).

  Definition ref_check (r : (ptab * string)%type) :
      { e : priv_err | ~ ref_ok Θ r } + { ref_ok Θ r }.
  Proof.
    destruct r as [t x]; unfold ref_ok; cbn [fst snd].
    destruct t as [| fp ch | nm es | t]; try exact (tab_check _ x).
    destruct (gtab Θ fp ch) as [t |]; [ exact (tab_check t x) | right; exact I ].
  Defined.

  Definition refs_check : forall (l : list (ptab * string)%type),
      { e : priv_err | ~ acc_ok Θ l } + { acc_ok Θ l }.
  Proof.
    induction l as [| r l IH]; [ right; constructor |].
    destruct (ref_check r) as [[e Hr] | Hr]; [ left; exists e; intros Hall; inversion Hall; contradiction |].
    destruct IH as [[e Hl] | Hl]; [ left; exists e; intros Hall; inversion Hall; contradiction | right; constructor; assumption ].
  Defined.
End PrivacyImpl.
