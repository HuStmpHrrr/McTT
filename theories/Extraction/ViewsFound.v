(** * Finding the Views of a Group Declaration

    The search of [ViewsSearch] instantiated with the data the declaration
    asks of each view ([view_siblings], [view_classify], [view_nparams], decided by
    [IndDecl]), and its termination: the views reachable from the
    declaration's own instances are finitely many, up to proofs
    ([views_reach_finite]), by [ViewsSearch.reach_finite_of_clusters] on
    the clusters of [ViewsCluster] and the order [view_lt].

    The invariant is [view_good]: a key typed and normal over the
    declaration's context.  A key's meets are bounded by the instances the
    normal forms of its constructors' arguments meet ([key_nf_meet]),
    whichever way it classifies them: as written, an argument meets
    nothing.  These are finitely many, decided at the fast context
    ([key_nf_meet_list]), and the same at keys equal up to proofs
    ([key_nf_meet_transfer]). *)

From Stdlib Require Import Lia List PeanoNat String.
From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic Require Import Fresh.
From Mctt.Core.Syntactic.Inductives Require Import Group.
From Mctt.Core.Syntactic.System Require Import Command.
From Mctt.Core.Syntactic.System.Global Require Import Presup MemberLemmas.
From Mctt.Core.Syntactic.System.Inductives Require Import Views.
From Mctt.Core.Syntactic.System.Records Require Import Syntax Typing.
From Mctt.Core.Consequences Require Import FiledConstructorTypes.
From Mctt.Extraction Require Import Lookup LookupTwins NbE GlobalCheck IndDecl ViewsSearch ViewsReach ViewsCluster.
From Mctt.Extraction Require Command.
#[local] Open Scope list_scope.

(** The data a view has: its siblings, its classified constructors and
    its filed non-uniform parameters. *)
Record view_data : Type := mk_view_data
  { (** The siblings *)
    data_siblings : list view_key
    (** The constructors, classified *)
  ; data_cons : list (string * list classified_carg)
    (** The non-uniform parameters, filed *)
  ; data_nparams : ctx }.

(** [a] is the data of the view [x] of the declaration [R]. *)
Record view_data_ok (Θ : gdeps) (Ξ : gstack) (R : raw_decl) (x : view_key) (a : view_data) : Prop := mk_view_data_ok
  { (** Its siblings *)
    data_ok_siblings : view_siblings Θ Ξ R x (data_siblings a)
    (** Its constructors *)
  ; data_ok_cons : view_classify Θ Ξ R x (data_cons a)
    (** Its non-uniform parameters *)
  ; data_ok_nparams : view_nparams Θ Ξ R x (data_nparams a) }.

(** The instances a view's constructors meet. *)
Definition data_meets (a : view_data) : list view_key := classified_cons_views (data_cons a).

Lemma view_data_functional : forall Θ Ξ R x a a', view_data_ok Θ Ξ R x a -> view_data_ok Θ Ξ R x a' -> a = a'.
Proof.
  intros * [Hs Hc Hn] [Hs' Hc' Hn']; destruct a, a'; cbn in *.
  rewrite (view_siblings_functional _ _ _ _ _ _ Hs Hs'), (view_classify_functional _ _ _ _ _ _ Hc Hc'),
    (view_nparams_functional _ _ _ _ _ _ Hn Hn'); reflexivity.
Qed.

(** The data of a view, or why it has none: its siblings first, then its
    constructors, then its parameters, looked up at the fast context
    [F]. *)
Definition view_data_dec (lvd : Command.levels_abstractable_decider) (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F)
    (R : raw_decl) (x : view_key) :
    ({a | view_data_ok (fc_deps F) (fc_stack F) R x a} + {e : view_why | forall a, ~ view_data_ok (fc_deps F) (fc_stack F) R x a})%type.
Proof.
  destruct (view_siblings_dec F (lvd _ _) HΞ R x) as [[ss Hs] | [e He]];
    [| right; exists e; intros a Ha; exact (He _ (data_ok_siblings _ _ _ _ _ Ha)) ].
  destruct (view_classify_dec F (lvd _ _) HΞ R x) as [[cs Hc] | [e He]];
    [| right; exists e; intros a Ha; exact (He _ (data_ok_cons _ _ _ _ _ Ha)) ].
  destruct (view_nparams_dec F (lvd _ _) HΞ R x) as [[Nv Hn] | [e He]];
    [| right; exists e; intros a Ha; exact (He _ (data_ok_nparams _ _ _ _ _ Ha)) ].
  left; exists (mk_view_data ss cs Nv); constructor; assumption.
Defined.

(** ** Finite Lists *)

(** The ways to split a list at an element: before it, it, after it. *)
Fixpoint splits {A : Type} (l : list A) : list (list A * A * list A) :=
  match l with
  | nil => nil
  | a :: l' => (nil, a, l') :: List.map (fun s => match s with (p, b, q0) => (a :: p, b, q0) end) (splits l')
  end.

Lemma in_splits : forall {A : Type} (l pre post : list A) a, In (pre, a, post) (splits l) <-> l = pre ++ a :: post.
Proof.
  induction l as [| b l IH]; intros pre post a; cbn [splits].
  - split; [ intros [] | intros H; destruct pre; discriminate ].
  - split.
    + intros [H | H]; [ injection H as <- <- <-; reflexivity |].
      apply List.in_map_iff in H as ([[p c] s] & E & Hin); injection E as <- <- <-.
      apply IH in Hin; rewrite Hin; reflexivity.
    + intros H; destruct pre as [| c pre]; cbn in H; injection H as <- H'.
      * left; rewrite H'; reflexivity.
      * right; apply List.in_map_iff; exists (pre, a, post); split; [ reflexivity | apply IH; exact H' ].
Qed.

(** The lists of bits of a length. *)
Fixpoint bool_lists (k : nat) : list (list bool) :=
  match k with
  | 0 => nil :: nil
  | S k' => List.map (cons true) (bool_lists k') ++ List.map (cons false) (bool_lists k')
  end.

Lemma in_bool_lists : forall k pat, In pat (bool_lists k) <-> List.length pat = k.
Proof.
  induction k as [| k IH]; intros [| b pat]; cbn [bool_lists List.length].
  - split; [ intros _; reflexivity | intros _; left; reflexivity ].
  - split; [ intros [H | []]; discriminate | intros H; discriminate ].
  - split; [ intros H; apply List.in_app_or in H as [H | H]; apply List.in_map_iff in H as (x & E & _); discriminate | discriminate ].
  - split.
    + intros H; apply List.in_app_or in H as [H | H]; apply List.in_map_iff in H as (x & E & Hx);
        injection E as <- <-; apply IH in Hx; lia.
    + intros H; injection H as H; apply List.in_or_app; destruct b; [ left | right ]; apply List.in_map, IH; exact H.
Qed.

(** A finite family of finite sets, each given by a list exactly, has a
    finite union. *)
Lemma ex_list_union : forall {A B : Type} (l : list A) (P : A -> B -> Prop),
    (forall a, In a l -> exists L, forall b, P a b <-> In b L) ->
    exists L, forall b, (exists a, In a l /\ P a b) <-> In b L.
Proof.
  induction l as [| a l IH]; intros P H.
  - exists nil; intros b; split; [ intros (a & [] & _) | intros [] ].
  - destruct (H a (or_introl eq_refl)) as [La HLa].
    destruct (IH P (fun a' Ha' => H a' (or_intror Ha'))) as [Ll HLl].
    exists (La ++ Ll); intros b; rewrite List.in_app_iff, <- HLa, <- HLl; split.
    + intros (a' & [<- | Ha'] & Hb); [ left; exact Hb | right; exists a'; split; assumption ].
    + intros [Hb | (a' & Ha' & Hb)]; [ exists a; split; [ left; reflexivity | exact Hb ] | exists a'; split; [ right; exact Ha' | exact Hb ] ].
Qed.

(** The elements of a list each of one of two kinds: the second kind are
    those of a list. *)
Lemma prop_filter : forall {B : Type} (Q P : B -> Prop) (L : list B), (forall b, In b L -> Q b \/ P b) ->
    exists M, (forall b, In b L -> Q b \/ In b M) /\ (forall b, In b M -> P b).
Proof.
  induction L as [| b L IH]; intros H.
  - exists nil; split; [ intros _ [] | intros _ [] ].
  - destruct IH as (M & HM1 & HM2); [ intros; apply H; right; assumption |].
    destruct (H b (or_introl eq_refl)) as [Hq | Hp].
    + exists M; split; [ intros b' [<- | Hb']; [ left; exact Hq | exact (HM1 _ Hb') ] | exact HM2 ].
    + exists (b :: M); split.
      * intros b' [<- | Hb']; [ right; left; reflexivity | destruct (HM1 _ Hb') as [Hq | Hm]; [ left; exact Hq | right; right; exact Hm ] ].
      * intros b' [<- | Hb']; [ exact Hp | exact (HM2 _ Hb') ].
Qed.

(** The positions of the arguments of constructors: the arguments before,
    the argument's type, and bits for those before. *)
Definition arg_positions (rcs : list (string * list (string * abs_kind * exp))) :
    list (list (string * abs_kind * exp) * exp * list bool) :=
  List.flat_map (fun rc => List.flat_map (fun s => match s with (pre, (_, _, T), _) =>
                                             List.map (fun pat => (pre, T, pat)) (bool_lists (List.length pre)) end)
                             (splits (snd rc))) rcs.

Lemma in_arg_positions : forall rcs pre T pat, In (pre, T, pat) (arg_positions rcs) <->
    exists rc y κ post, In rc rcs /\ snd rc = pre ++ (y, κ, T) :: post /\ List.length pat = List.length pre.
Proof.
  intros; unfold arg_positions; rewrite List.in_flat_map; split.
  - intros (rc & Hrc & H); apply List.in_flat_map in H as ([[pre' [[y κ] T']] post] & Hs & H).
    apply List.in_map_iff in H as (pat' & E & Hp); injection E as <- <- <-.
    exists rc, y, κ, post; split; [ exact Hrc | split; [ apply in_splits; exact Hs | apply in_bool_lists; exact Hp ] ].
  - intros (rc & y & κ & post & Hrc & Hs & Hl); exists rc; split; [ exact Hrc |].
    apply List.in_flat_map; exists (pre, (y, κ, T), post); split; [ apply in_splits; exact Hs |].
    apply List.in_map_iff; exists pat; split; [ reflexivity | apply in_bool_lists; exact Hl ].
Qed.

(** ** The Clusters *)

Section Clusters.
  (** The decision of [levels_abstractable] the checker is given *)
  Variable lvd : Command.levels_abstractable_decider.
  (** The fast context the views' data are looked up in; the judgments
      are at the Core context it stands for. *)
  Variable F : FCtx.
  #[local] Abbreviation Θ := (fc_deps F).
  #[local] Abbreviation Ξ := (fc_stack F).
  Hypothesis HΞ : ⊢ᵍ Θ ⍮ Ξ.
  Variable R : raw_decl.
  #[local] Abbreviation Γu := (raw_decl_uniform_ctx Ξ R).
  #[local] Abbreviation nu := (raw_decl_nu R).
  #[local] Abbreviation nm := (raw_decl_nmembers R).

  (** The views whose data the PER model reads: keys typed and normal over
      the declaration's context. *)
  Definition view_good (x : view_key) : Prop := key_inv Θ Ξ Γu x /\ key_normal Θ Ξ Γu x.

  (** The instances the normal forms of a key's constructors' arguments
      meet. *)
  Definition key_nf_meet (x z : view_key) : Prop :=
    match x with
    | vk_ind qc k W => exists D Mk, ind_lookup Θ Ξ qc = Some D /\ ind_member D k = Some Mk /\
        nf_meet_in Θ Ξ (tele_sub (im_nparams Mk) (sb_of_list sb_id (List.map nf_to_exp W)) ++ Γu) nu (im_nn Mk + nu) nm
          (member_rcs qc D Mk W) z
    | vk_record qr W => exists Rr, record_lookup Θ Ξ qr = Some Rr /\ nf_meet_in Θ Ξ Γu nu nu nm (record_rcs Rr W) z
    end.

  (** A view's meets are met by the normal forms of its constructors'
      arguments. *)
  Lemma data_key_nf_meet : forall x a z, view_data_ok Θ Ξ R x a -> In z (data_meets a) -> key_nf_meet x z.
  Proof.
    intros * [_ Hc _] Hz; unfold data_meets in Hz.
    inversion Hc as [qc k Cs D' Mk' cs' Hl HMk Hcls | qr Is Rr cs' Hl Hcls]; subst; cbn [key_nf_meet].
    - exists D', Mk'; split; [ exact Hl | split; [ exact HMk | exact (classify_cons_in_nf_meet _ _ _ _ _ _ _ _ _ Hcls Hz) ] ].
    - exists Rr; split; [ exact Hl | exact (classify_cons_in_nf_meet _ _ _ _ _ _ _ _ _ Hcls Hz) ].
  Qed.

  (** They are good. *)
  Lemma key_nf_meet_good : forall x z, key_nf_meet x z -> view_good z.
  Proof.
    intros [qc k W | qr W] z Hm; cbn [key_nf_meet] in Hm.
    - destruct Hm as (D & Mk & _ & _ & [rc _ pre y κ T post _ pat Hlp Hm]).
      rewrite List.app_assoc in Hm.
      assert (Hl : List.length (raw_args_tele pre ++ tele_sub (im_nparams Mk) (sb_of_list sb_id (List.map nf_to_exp W)))
                   = List.length pat + (im_nn Mk + nu - nu))
        by (rewrite List.length_app, length_raw_args_tele, length_tele_sub; change (List.length (im_nparams Mk)) with (im_nn Mk); lia).
      exact (@nf_meet_at_good (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ Hl Hm).
    - destruct Hm as (Rr & _ & [rc _ pre y κ T post _ pat Hlp Hm]).
      assert (Hl : List.length (raw_args_tele pre) = List.length pat + (nu - nu)) by (rewrite length_raw_args_tele; lia).
      exact (@nf_meet_at_good (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ Hl Hm).
  Qed.

  (** The instances any view meets are good. *)
  Lemma views_meets_good : forall x ax z, view_data_ok Θ Ξ R x ax -> In z (data_meets ax) -> view_good z.
  Proof. intros * Hx Hz; exact (key_nf_meet_good _ _ (data_key_nf_meet _ _ _ Hx Hz)). Qed.

  (** The instances a type's normal form meets, decided: as many as the
      instances its classification finds, keyed. *)
  Lemma nf_meet_at_list : forall Γ nup np n pat T, exists L, forall z, nf_meet_at Θ Ξ Γ nup np n pat T z <-> In z L.
  Proof.
    intros *.
    destruct (typ_least_dec F (lvd _ _) HΞ Γ T) as [[i [HT _]] | HnT].
    2:{ exists nil; intros z; split; [ intros [i HT _ _ _ _ _ _ _ _]; exact (HnT _ HT) | intros [] ]. }
    destruct (nbe_ty_impl F Γ T (typ_nbe_ty_order F _ _ _ HT)) as [W HW].
    destruct (nf_proof_freeb W) eqn:Hpf.
    2:{ exists nil; intros z; split; [| intros [] ].
        intros [i' HT' W' HW' Hpf' _ _ _ _ _]; pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-.
        apply (proj1 nf_proof_freeb_iff) in Hpf'; congruence. }
    apply (proj1 nf_proof_freeb_iff) in Hpf.
    destruct (classify_arg (grp_info_f F) (rec_info_f F) nup np n pat (nf_to_exp W)) as [gw |] eqn:Hn;
      rewrite (classify_arg_rec_ext _ _ _ (rec_info_f_ok F)), (classify_arg_ext _ _ _ _ _ _ _ (grp_info_f_ok F)) in Hn.
    2:{ exists nil; intros z; split; [| intros [] ].
        intros [i' HT' W' HW' _ gw' Hn' _ _ _]; pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-; congruence. }
    destruct (written_carg_key_dec F (lvd _ _) HΞ (List.skipn (List.length pat + (np - nup)) Γ) gw) as [[g Hg] | Hng].
    2:{ exists nil; intros z; split; [| intros [] ].
        intros [i' HT' W' HW' _ gw' Hn' g' Hk _]; pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-.
        rewrite Hn in Hn'; injection Hn' as <-; exact (Hng _ Hk). }
    exists (classified_carg_view g); intros z; split.
    - intros [i' HT' W' HW' _ gw' Hn' g' Hk Hz]; pose proof (functional_nbe_ty _ _ _ _ HW HW') as <-.
      rewrite Hn in Hn'; injection Hn' as <-; rewrite (written_carg_key_functional _ _ _ _ _ _ Hg Hk); exact Hz.
    - intros Hz; exact (mk_nf_meet_at _ _ _ _ _ _ _ _ _ i HT W HW Hpf gw Hn g Hg Hz).
  Qed.

  (** The instances the normal forms of constructors' arguments meet,
      decided. *)
  Lemma nf_meet_in_list : forall Γp nup np n rcs, exists L, forall z, nf_meet_in Θ Ξ Γp nup np n rcs z <-> In z L.
  Proof.
    intros *.
    destruct (ex_list_union (arg_positions rcs)
                (fun p z => nf_meet_at Θ Ξ (raw_args_tele (fst (fst p)) ++ Γp) nup np n (snd p) (snd (fst p)) z)
                (fun p _ => nf_meet_at_list _ _ _ _ _ _)) as [L HL].
    exists L; intros z; rewrite <- HL; split.
    - intros [rc Hrc pre y κ T post Hs pat Hlp Hm]; exists (pre, T, pat); split; [| exact Hm ].
      apply in_arg_positions; exists rc, y, κ, post; auto.
    - intros ([[pre T] pat] & Hp & Hm); cbn [fst snd] in Hm.
      apply in_arg_positions in Hp as (rc & y & κ & post & Hrc & Hs & Hl).
      exact (mk_nf_meet_in _ _ _ _ _ _ _ _ rc Hrc pre y κ T post Hs pat Hl Hm).
  Qed.

  (** A key's normal-form meets, decided. *)
  Lemma key_nf_meet_list : forall x, exists L, forall z, key_nf_meet x z <-> In z L.
  Proof.
    intros [qc k W | qr W]; cbn [key_nf_meet].
    - destruct (ind_lookup_f F qc) as [[D |] HlD].
      2:{ exists nil; intros z; split; [ intros (D & Mk & Hl & _); congruence | intros [] ]. }
      destruct (ind_member D k) as [Mk |] eqn:HMk.
      2:{ exists nil; intros z; split; [ intros (D' & Mk & Hl & HMk' & _); rewrite <- HlD in Hl; injection Hl as <-; congruence
                                      | intros [] ]. }
      destruct (nf_meet_in_list (tele_sub (im_nparams Mk) (sb_of_list sb_id (List.map nf_to_exp W)) ++ Γu) nu (im_nn Mk + nu) nm
                  (member_rcs qc D Mk W)) as [L HL].
      exists L; intros z; rewrite <- HL; split.
      + intros (D' & Mk' & Hl & HMk' & Hm); rewrite <- HlD in Hl; injection Hl as <-; rewrite HMk in HMk'; injection HMk' as <-; exact Hm.
      + intros Hm; exists D, Mk; auto.
    - destruct (record_lookup_f F qr) as [[Rr |] HlR].
      2:{ exists nil; intros z; split; [ intros (Rr & Hl & _); congruence | intros [] ]. }
      destruct (nf_meet_in_list Γu nu nu nm (record_rcs Rr W)) as [L HL].
      exists L; intros z; rewrite <- HL; split.
      + intros (Rr' & Hl & Hm); rewrite <- HlR in Hl; injection Hl as <-; exact Hm.
      + intros Hm; exists Rr; auto.
  Qed.

  (** Keys equal up to proofs have the same normal-form meets. *)
  Lemma key_nf_meet_transfer : forall y l z, view_good y -> view_good l -> view_key_eq y l -> key_nf_meet y z -> key_nf_meet l z.
  Proof.
    intros y l z [Hy Hky] [_ Hkl] Hyl Hm.
    destruct (view_key_eq_parts _ _ Hyl) as (Hh & Hr & HWW).
    destruct y as [qc k W1 | qr W1], l as [qc' k' W2 | qr' W2]; cbn in Hh, Hr, HWW; try discriminate.
    - injection Hh as <- <-; cbn [key_nf_meet] in Hm |- *.
      destruct Hm as (D & Mk & Hl & HMk & Hm); exists D, Mk; split; [ exact Hl | split; [ exact HMk |] ].
      destruct Hy as [D' Hl' _ HWl _ HΓu]; rewrite Hl in Hl'; injection Hl' as <-.
      destruct (decl_of_lookup _ _ _ _ _ HΓu Hl) as [Hdt Hc].
      assert (HWl' : List.length W1 = ind_nu D) by (rewrite List.length_map in HWl; exact HWl).
      pose proof (@key_sub_eq_ind (gc_mk Θ Ξ) _ _ _ _ _ _ _ HΓu Hl Hdt Hc HWl' Hky Hkl HWW) as Hσ.
      exact (@member_meets_transfer (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HMk (wf_sub_eq_sym _ _ _ _ _ _ Hσ) Hm).
    - injection Hh as <-; cbn [key_nf_meet] in Hm |- *.
      destruct Hm as (Rr & Hl & Hm); exists Rr; split; [ exact Hl |].
      destruct Hy as [Rr' Hl' HWl _ HΓu]; rewrite Hl in Hl'; injection Hl' as <-.
      assert (HWl' : List.length W1 = List.length (record_params Rr)) by (rewrite List.length_map in HWl; exact HWl).
      pose proof (@key_sub_eq_record (gc_mk Θ Ξ) _ _ _ _ _ HΓu Hl HWl' Hky Hkl HWW) as Hσ.
      exact (@record_meets_transfer (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ HΓu Hl (wf_sub_eq_sym _ _ _ _ _ _ Hσ) Hm).
  Qed.

  (** The data of a record view: itself its only sibling. *)
  Lemma record_view_siblings : forall qx Wx a, view_data_ok Θ Ξ R (vk_record qx Wx) a -> data_siblings a = vk_record qx Wx :: nil.
  Proof. intros * [Hs _ _]; inversion Hs; subst; reflexivity. Qed.

  (** The siblings of a good view of a group are good. *)
  Lemma siblings_from_good : forall qx kx Wx D ss, view_good (vk_ind qx kx Wx) -> ind_lookup Θ Ξ qx = Some D ->
      siblings_from Θ Ξ Γu qx Wx 0 (ind_members D) ss -> forall y, In y ss -> view_good y.
  Proof.
    intros * [[D' Hl' Hk HCl HCt HΓu] Hkn] Hl Hss y Hy.
    rewrite Hl in Hl'; injection Hl' as <-.
    destruct (decl_of_glookup _ _ _ _ HΞ Hl) as [Hdt _].
    destruct (siblings_from_in _ _ _ _ _ _ _ _ Hss _ Hy) as (j & M & HM & _ & Hse); cbn [Nat.add] in Hse.
    change (ind_member D j = Some M) in HM.
    inversion Hse as [? ? pm Hh | ? ? qv kv Iv vmv Dv Wv Hh Hlv Hnv | ? ? qr Ir fl Rr Wr Hh Hlr Hnr]; subst.
    - assert (Hd : im_is_decl M = true) by (unfold im_is_decl; rewrite Hh; reflexivity).
      apply (decl_typed_order _ _ _ Hdt _ _ HM) in Hd.
      split; [ exact (mk_view_typed _ _ _ _ _ _ D Hl Hd HCl HCt HΓu) |].
      destruct Hkn as [v Hv]; inversion Hv as [? ? C D2 ? Hl2 HC |]; subst.
      exists (vi_ind qx j C); econstructor; eassumption.
    - split; [ exact (@sibling_view_inv (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HM Hh Hlv Hnv) |].
      destruct (decl_of_glookup _ _ _ _ HΞ Hlv) as [_ Hcv].
      rewrite (tele_insts_sub (ind_uparams Dv) 0 Id Id _ Iv (decl_closed_ass _ Hcv) (decl_closed_uparams _ Hcv) ltac:(intros; lia)) in Hnv.
      exists (vi_ind qv kv (List.map (fun I => I[sb_of_list Id (List.map nf_to_exp Wx)]) Iv)); econstructor; eassumption.
    - split; [ exact (@sibling_record_inv (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HM Hh Hlr Hnr) |].
      pose proof (gctx_closed_record _ _ _ _ (wf_gstack_closed _ _ HΞ) Hlr) as HcR.
      rewrite (record_params_insts_sub Rr Ir _ HcR) in Hnr.
      exists (vi_record qr (List.map (fun I => I[sb_of_list Id (List.map nf_to_exp Wx)]) Ir)); econstructor; eassumption.
  Qed.

  (** The siblings of a good view are good. *)
  Lemma views_siblings_good : forall x ax y, view_good x -> view_data_ok Θ Ξ R x ax -> In y (data_siblings ax) -> view_good y.
  Proof.
    intros x ax y Hx Hax Hy.
    destruct x as [qx kx Wx | qx Wx].
    2:{ rewrite (record_view_siblings _ _ _ Hax) in Hy; destruct Hy as [<- | []]; exact Hx. }
    pose proof (data_ok_siblings _ _ _ _ _ Hax) as Hs.
    inversion Hs as [? ? ? D ss Hl Hss |]; subst.
    exact (siblings_from_good _ _ _ _ _ Hx Hl Hss _ Hy).
  Qed.

  (** Good views are accessible for the nesting order. *)
  Lemma views_lt_acc : forall x, view_good x -> Acc (view_lt Θ Ξ Γu) x.
  Proof. intros x [Hx _]; exact (key_inv_acc _ _ _ _ HΞ Hx). Qed.

  (** The meets of the members of the group at a good view's arguments are
      siblings up to proofs, or good and below the view. *)
  Lemma ind_cluster_meets : forall qx kx Wx D ss, view_good (vk_ind qx kx Wx) -> ind_lookup Θ Ξ qx = Some D ->
      siblings_from Θ Ξ Γu qx Wx 0 (ind_members D) ss ->
      forall l z, In l (ss ++ vk_ind qx kx Wx :: nil) -> key_nf_meet l z ->
        key_in z ss \/ (view_good z /\ view_lt Θ Ξ Γu z (vk_ind qx kx Wx)).
  Proof.
    intros * Hx Hl Hss l z Hl0 Hm.
    pose proof (key_nf_meet_good _ _ Hm) as Hz.
    destruct Hx as [[D' Hl' Hk HCl HCt HΓu] Hkn]; rewrite Hl in Hl'; injection Hl' as <-.
    assert (HWl : List.length Wx = ind_nu D) by (rewrite List.length_map in HCl; exact HCl).
    assert (Hor : forall P, P \/ view_lt Θ Ξ Γu z (vk_ind qx kx Wx) -> P \/ (view_good z /\ view_lt Θ Ξ Γu z (vk_ind qx kx Wx)))
      by (intros P [HP | Hlt]; [ left; exact HP | right; split; assumption ]).
    apply Hor.
    apply List.in_app_or in Hl0 as [Hl0 | [<- | []]].
    2:{ cbn [key_nf_meet] in Hm; destruct Hm as (D' & Mk & Hl2 & HMk & Hm); rewrite Hl in Hl2; injection Hl2 as <-.
        exact (@member_meets (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HWl HCt Hkn Hss HMk Hm). }
    destruct (siblings_from_in _ _ _ _ _ _ _ _ Hss _ Hl0) as (j & M & HM & _ & Hse); cbn [Nat.add] in Hse.
    change (ind_member D j = Some M) in HM.
    inversion Hse as [? ? pm Hh | ? ? qv kv Iv vmv Dv Wv Hh Hlv Hnv | ? ? qr Ir fl Rr Wr Hh Hlr Hnr]; subst; cbn [key_nf_meet] in Hm.
    - destruct Hm as (D' & Mk & Hl2 & HMk & Hm); rewrite Hl in Hl2; injection Hl2 as <-.
      exact (@member_meets (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HWl HCt Hkn Hss HMk Hm).
    - destruct Hm as (Dv' & My & Hl2 & HMy & Hm); rewrite Hlv in Hl2; injection Hl2 as <-.
      exact (@view_sibling_meets (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HWl HCt Hkn Hss HM Hh Hlv Hnv HMy Hm).
    - destruct Hm as (Rr' & Hl2 & Hm); rewrite Hlr in Hl2; injection Hl2 as <-.
      exact (@record_sibling_meets (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HWl HCt Hkn Hss HM Hh Hlr Hnr Hm).
  Qed.

  (** Keys composed up to proofs. *)
  Lemma key_in_compose : forall w L1 L2, key_in w L1 -> (forall e, In e L1 -> key_in e L2) -> key_in w L2.
  Proof.
    intros w L1 L2 (e & He & Hwe) H; destruct (H _ He) as (e' & He' & Hee'); exists e'; split; [ exact He' |].
    etransitivity; eassumption.
  Qed.

  (** The siblings of a good view equal up to proofs to one of the cluster
      of a good view of a group are of it. *)
  Lemma ind_cluster_closed : forall qx kx Wx D ss, view_good (vk_ind qx kx Wx) -> ind_lookup Θ Ξ qx = Some D ->
      siblings_from Θ Ξ Γu qx Wx 0 (ind_members D) ss ->
      forall y ay w, view_good y -> key_in y (ss ++ vk_ind qx kx Wx :: nil) -> view_data_ok Θ Ξ R y ay -> In w (data_siblings ay) ->
        key_in w (ss ++ vk_ind qx kx Wx :: nil).
  Proof.
    intros * Hx Hl Hss y ay w Hy HyL Hay Hw.
    destruct y as [qy ky Wy | qy Wy].
    2:{ rewrite (record_view_siblings _ _ _ Hay) in Hw; destruct Hw as [<- | []]; exact HyL. }
    pose proof (data_ok_siblings _ _ _ _ _ Hay) as Hsy; inversion Hsy as [? ? ? Dy ssy Hly Hssy |]; subst.
    destruct HyL as (l & HlL & Hyl).
    destruct (view_key_eq_parts _ _ Hyl) as (Hh & Hr & HWW).
    pose proof Hx as [[D' Hl' Hk HCl HCt HΓu] Hkn]; rewrite Hl in Hl'; injection Hl' as <-.
    assert (HWl : List.length Wx = ind_nu D) by (rewrite List.length_map in HCl; exact HCl).
    destruct (decl_of_glookup _ _ _ _ HΞ Hl) as [Hdt Hc].
    pose proof Hy as [[Dy' Hly' _ HWyl _ _] Hky]; rewrite Hly in Hly'; injection Hly' as <-.
    assert (HWyl' : List.length Wy = ind_nu Dy) by (rewrite List.length_map in HWyl; exact HWyl).
    destruct (decl_of_glookup _ _ _ _ HΞ Hly) as [Hdty Hcy].
    (** the siblings of the group at the key's arguments, against those at
        an argument list equal up to proofs *)
    assert (Hcase : forall W2 k2 ss2, siblings_from Θ Ξ Γu qy W2 0 (ind_members Dy) ss2 -> key_normal Θ Ξ Γu (vk_ind qy k2 W2) ->
                      nfs_eq_upto_proofs Wy W2 -> key_in w ss2).
    { intros W2 k2 ss2 Hss2 Hk2 HW2.
      pose proof (@key_sub_eq_ind (gc_mk Θ Ξ) _ _ _ _ _ _ _ HΓu Hly Hdty Hcy HWyl' Hky Hk2 HW2) as Hσ.
      exact (@siblings_from_upto (gc_mk Θ Ξ) _ _ _ _ _ _ _ HΞ HΓu Hly HW2 Hσ Hssy Hss2 _ Hw). }
    apply List.in_app_or in HlL as [HlL | [<- | []]].
    2:{ cbn in Hh, HWW; injection Hh as <- <-; rewrite Hl in Hly; injection Hly as <-.
        apply key_in_app_l; exact (Hcase _ _ _ Hss Hkn HWW). }
    destruct (siblings_from_in _ _ _ _ _ _ _ _ Hss _ HlL) as (j & M & HM & _ & Hse); cbn [Nat.add] in Hse.
    change (ind_member D j = Some M) in HM.
    inversion Hse as [? ? pm Hh0 | ? ? qv kv Iv vmv Dv Wv Hh0 Hlv Hnv | ? ? qr Ir fl Rr Wr Hh0 Hlr Hnr]; subst; cbn in Hh, Hr, HWW;
      try discriminate.
    - injection Hh as <- <-; rewrite Hl in Hly; injection Hly as <-.
      destruct Hkn as [v Hv]; inversion Hv as [? ? C D2 ? Hl2 HC |]; subst.
      apply key_in_app_l; apply (Hcase _ j _ Hss); [ exists (vi_ind qx j C); econstructor; eassumption | exact HWW ].
    - injection Hh as <- <-; rewrite Hlv in Hly; injection Hly as <-.
      (** a view sibling: its own siblings are the group's at the view's
          arguments, which are siblings of the group at [Wx] *)
      pose proof (@sibling_view_inv (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HM Hh0 Hlv Hnv) as [Dv' Hlv' _ HWvl HWvt _].
      rewrite Hlv in Hlv'; injection Hlv' as <-.
      assert (HWvl' : List.length Wv = ind_nu Dv) by (rewrite List.length_map in HWvl; exact HWvl).
      destruct (@siblings_from_exists (gc_mk Θ Ξ) _ _ _ _ HΞ HΓu Hlv HWvl' HWvt) as [ssv Hssv].
      assert (Hkv : key_normal Θ Ξ Γu (vk_ind qv kv Wv)).
      { pose proof Hnv as Hnv'; destruct (decl_of_glookup _ _ _ _ HΞ Hlv) as [_ Hcv].
        rewrite (tele_insts_sub (ind_uparams Dv) 0 Id Id _ Iv (decl_closed_ass _ Hcv) (decl_closed_uparams _ Hcv) ltac:(intros; lia)) in Hnv'.
        exists (vi_ind qv kv (List.map (fun I => I[sb_of_list Id (List.map nf_to_exp Wx)]) Iv)); econstructor; eassumption. }
      pose proof (Hcase _ _ _ Hssv Hkv HWW) as Hwv.
      apply key_in_app_l; apply (key_in_compose _ _ _ Hwv).
      exact (@view_entry_siblings (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ _ _ _ _ _ _ HΞ HΓu Hl HCl HCt HM Hh0 Hlv Hnv Hss Hssv).
  Qed.

  (** A good view has a cluster: its siblings and itself, up to proofs,
      and below it, the instances their normal-form meets leave it for. *)
  Theorem views_cluster : forall x, view_good x ->
      exists L M, cluster_of view_data (view_data_ok Θ Ξ R) data_siblings data_meets view_good (view_lt Θ Ξ Γu) x L M.
  Proof.
    intros x Hx.
    destruct x as [qx kx Wx | qx Wx].
    2:{ (** a record view: itself alone, whose meets are below it *)
        destruct (key_nf_meet_list (vk_record qx Wx)) as [ML HML].
        exists (vk_record qx Wx :: nil), ML; constructor.
        - left; reflexivity.
        - intros y ay w _ HyL Hay Hw.
          destruct HyL as (l & [<- | []] & Hyl); destruct (view_key_eq_parts _ _ Hyl) as (_ & Hr & _).
          destruct y as [qy ky Wy | qy Wy]; cbn in Hr; [ discriminate |].
          rewrite (record_view_siblings _ _ _ Hay) in Hw; destruct Hw as [<- | []].
          exists (vk_record qx Wx); split; [ left; reflexivity | exact Hyl ].
        - intros y ay z Hy HyL Hay Hz; right.
          destruct HyL as (l & [<- | []] & Hyl).
          apply key_in_of_in, HML, (key_nf_meet_transfer _ _ _ Hy Hx Hyl), (data_key_nf_meet _ _ _ Hay Hz).
        - intros z Hz; apply HML in Hz.
          split; [ exact (key_nf_meet_good _ _ Hz) |].
          destruct Hz as (Rr & Hlr & Hm); destruct Hx as [Hx _].
          exact (@record_view_meets_below (gc_mk Θ Ξ) _ _ _ _ _ _ _ HΞ Hx Hlr Hm). }
    pose proof Hx as [[D Hl Hk HCl HCt HΓu] Hkn].
    assert (HWl : List.length Wx = ind_nu D) by (rewrite List.length_map in HCl; exact HCl).
    destruct (@siblings_from_exists (gc_mk Θ Ξ) _ _ _ _ HΞ HΓu Hl HWl HCt) as [ss Hss].
    set (L := ss ++ vk_ind qx kx Wx :: nil).
    destruct (ex_list_union L key_nf_meet (fun l _ => key_nf_meet_list l)) as [ML HML].
    destruct (prop_filter (fun z => key_in z ss) (fun z => view_good z /\ view_lt Θ Ξ Γu z (vk_ind qx kx Wx)) ML)
      as (M & HM1 & HM2).
    { intros z Hz; apply HML in Hz as (l & HlL & Hm); exact (ind_cluster_meets _ _ _ _ _ Hx Hl Hss _ _ HlL Hm). }
    (** the views of the cluster are good *)
    assert (HLg : forall l, In l L -> view_good l)
      by (intros l Hl0; apply List.in_app_or in Hl0 as [Hl0 | [<- | []]]; [ exact (siblings_from_good _ _ _ _ _ Hx Hl Hss _ Hl0) | exact Hx ]).
    exists L, M; constructor.
    - apply List.in_or_app; right; left; reflexivity.
    - exact (ind_cluster_closed _ _ _ _ _ Hx Hl Hss).
    - intros y ay z Hy HyL Hay Hz.
      destruct HyL as (l & HlL & Hyl).
      assert (HzM : In z ML)
        by (apply HML; exists l; split; [ exact HlL | exact (key_nf_meet_transfer _ _ _ Hy (HLg _ HlL) Hyl (data_key_nf_meet _ _ _ Hay Hz)) ]).
      destruct (HM1 _ HzM) as [Hzs | HzM']; [ left; apply key_in_app_l; exact Hzs | right; apply key_in_of_in; exact HzM' ].
    - exact HM2.
  Qed.

  (** The declared members' context is the declaration's past their
      non-uniform parameters. *)
  Lemma raw_member_args_ctx_split : forall Mr, exists X, raw_member_args_ctx Ξ R Mr = X ++ Γu /\
      List.length X = List.length (raw_member_nparams Mr).
  Proof.
    intros Mr; unfold raw_member_args_ctx, raw_decl_uniform_ctx; rewrite tele_wk_app, <- List.app_assoc.
    eexists; split; [ reflexivity | apply length_tele_wk ].
  Qed.

  (** The instances the declared members' constructors meet are good. *)
  Lemma init_good : forall csD, Forall2 (raw_member_classify Θ Ξ R) (raw_decl_members R) csD ->
      forall z, In z (List.concat (List.map classified_cons_views csD)) -> view_good z.
  Proof.
    intros csD Hcls z Hz.
    apply List.in_concat in Hz as (zs & Hzs & Hz); apply List.in_map_iff in Hzs as (cs & <- & Hcs).
    destruct (Forall2_in_r _ _ _ _ Hcls Hcs) as (Mr & _ & HMr).
    unfold raw_member_classify in HMr.
    destruct (classify_cons_in_nf_meet _ _ _ _ _ _ _ _ _ HMr Hz) as [rc _ pre y κ T post _ pat Hlp Hm].
    destruct (raw_member_args_ctx_split Mr) as (X & EX & HlX); rewrite EX, List.app_assoc in Hm.
    assert (Hl : List.length (raw_args_tele pre ++ X) = List.length pat + (List.length (raw_member_nparams Mr) + nu - nu))
      by (rewrite List.length_app, length_raw_args_tele; lia).
    exact (@nf_meet_at_good (gc_mk Θ Ξ) _ _ _ _ _ _ _ _ Hl Hm).
  Qed.

  (** ** Termination

      From the instances the declared members' constructors meet, the
      search reaches finitely many views, up to proofs.

      Informally, a declaration has a nesting budget.  Each container [C]
      gets a measure [m_C], computed in filing order, so the containers a
      group nests through are measured before it:
      - an occurrence of the group's own members counts nothing;
      - an occurrence of a parameter costs what the parameter does: a
        parameter of a type is the identity;
      - a parameter of a function type gets a function measure, and
        applying it composes;
      - an occurrence of a container [C'] at arguments costs one more than
        [m_C'] at the arguments' measures.
      The views a declaration finds are at most its budget's levels.  For
      instance, with
      - [E (G) | mkE (y : G ℕ)],
      - [D (F) | mkD (x : E (λY. F (F Y)))],
      - [T | t (d : D (λX. Pair X T))],
      the occurrence of [D] in [T] costs [m_D(f) = 1 + m_E(f∘f)], with
      [f] the measure of [λX. Pair X T] (one more than its argument,
      [T] itself counting nothing): [1 + (1 + f(f(0))) = 4] levels, and
      [T] has the 4 views [D] at [λX. Pair X T], [E] at
      [λY. Pair (Pair Y T) T], [Pair] at [Pair ℕ T] and [T], and [Pair]
      at [ℕ] and [T].

      The proof does not compute this budget: it uses the semantic
      measure the budget explains, the derivations of the PER model.  A
      good view's type is one of the model ([view_inv_acc], through
      [per_univ_nest_acc]); the views reachable from it within its group
      at its arguments are its cluster, its siblings, up to proofs
      ([views_cluster]); every instance the cluster meets outside it is a
      nesting step below it ([view_lt], by [nonrec_meet_below]); and
      nesting steps are well founded on the types of the model
      ([NestAcc.per_univ_nest_acc]).  Every instance met is good
      ([views_meets_good]), and so is every sibling of a good view
      ([views_siblings_good]) and every instance the declared members'
      constructors meet ([init_good]). *)
  Theorem views_reach_finite : forall csD, Forall2 (raw_member_classify Θ Ξ R) (raw_decl_members R) csD -> exists L,
      forall y, reach view_data (view_data_ok Θ Ξ R) data_siblings data_meets (List.concat (List.map classified_cons_views csD)) y ->
        key_in y L.
  Proof.
    intros csD Hcls.
    exact (reach_finite_of_clusters view_data (view_data_ok Θ Ξ R) data_siblings data_meets _ view_good (view_lt Θ Ξ Γu)
             views_lt_acc views_cluster views_meets_good views_siblings_good (init_good csD Hcls)).
  Qed.

  (** The search from the instances the declared members' constructors
      [csD] meet. *)
  Definition views_search_run (csD : list (list (string * list classified_carg)))
      (Hcls : Forall2 (raw_member_classify Θ Ξ R) (raw_decl_members R) csD) :
      result view_data (view_data_ok Θ Ξ R) data_siblings data_meets view_why nil (List.concat (List.map classified_cons_views csD)) :=
    views_search_from view_data (view_data_ok Θ Ξ R) data_siblings data_meets (view_data_functional Θ Ξ R) view_why
      (view_data_dec lvd F HΞ R) _ view_why_shadowed (views_reach_finite csD Hcls).
End Clusters.

(** ** The Views Found, as the Checker Asks *)

(** A run of the search is one with any tables equal pointwise. *)
Lemma views_dfs_ext : forall sibs sibs' meets meets' acc tr Vs, (forall x, sibs x = sibs' x) -> (forall x, meets x = meets' x) ->
    views_dfs sibs meets acc tr Vs -> views_dfs sibs' meets' acc tr Vs.
Proof.
  intros * Hs Hm H; induction H as [acc | acc x tr Vs _ IH]; [ constructor |].
  assert (E : views_met sibs acc x = views_met sibs' acc x) by (unfold views_met; rewrite Hs; reflexivity).
  constructor; rewrite <- E, <- (List.map_ext _ _ Hm); exact IH.
Qed.

Lemma Forall2_map_impl : forall {X Y Z} (P : X -> Y -> Prop) (Q : X -> Z -> Prop) (f : Y -> Z) xs ys,
    Forall2 P xs ys -> (forall x y, P x y -> Q x (f y)) -> Forall2 Q xs (List.map f ys).
Proof. intros * H Hf; induction H; constructor; auto. Qed.

(** The name a rejected view is reported under: the declaration's first
    member's. *)
Definition raw_decl_first_name (R : raw_decl) : string :=
  match raw_decl_members R with Mr :: _ => raw_member_name Mr | nil => ""%string end.

(** A run of the search, as the checker asks of the views. *)
Lemma views_found_ok : forall Θ Ξ R csD Vf Af, key_nodup Vf -> Forall2 (view_data_ok Θ Ξ R) Vf Af ->
    views_dfs (siblings_table Vf (List.map data_siblings Af)) (met_table Vf (List.map data_meets Af)) nil (List.concat (List.map classified_cons_views csD)) Vf ->
    Command.views_ok Θ Ξ R csD Vf (List.map data_siblings Af) (List.map data_cons Af) (List.map data_nparams Af).
Proof.
  intros * _ HF Hb; constructor.
  - exact (Forall2_map_impl _ _ _ _ _ HF (fun x a H => data_ok_siblings _ _ _ _ _ H)).
  - exact (Forall2_map_impl _ _ _ _ _ HF (fun x a H => data_ok_cons _ _ _ _ _ H)).
  - exact (Forall2_map_impl _ _ _ _ _ HF (fun x a H => data_ok_nparams _ _ _ _ _ H)).
  - eapply views_dfs_ext; [ intros; reflexivity | | exact Hb ].
    intros x; rewrite meets_table_met_table, List.map_map; reflexivity.
Defined.

(** The views of a group declaration, found: the views of the search, or
    the first view it meets that has no data, with why. *)
Definition views_search (lvd : Command.levels_abstractable_decider) (F : FCtx) (HΞ : ⊢ᵍ fc_deps F ⍮ fc_stack F) (R : raw_decl)
    (csD : list (list (string * list classified_carg)))
    (Hcls : Forall2 (raw_member_classify (fc_deps F) (fc_stack F) R) (raw_decl_members R) csD) :
    Command.run_result (Command.views_found (fc_deps F) (fc_stack F) R csD) :=
  match views_search_run lvd F HΞ R csD Hcls with
  | inl (exist _ (Vf, Af) (conj Hd (conj HF Hb))) =>
      Command.run_success (existT _ Vf (existT _ (List.map data_siblings Af) (existT _ (List.map data_cons Af)
        (exist _ (List.map data_nparams Af) (views_found_ok (fc_deps F) (fc_stack F) R csD Vf Af Hd HF Hb)))))
  | inr (exist _ (x, e) _) => Command.run_failure (Command.run_error_view (raw_decl_first_name R) x e)
  end.

(** The search finds the views whenever there are some. *)
Theorem views_search_complete : forall lvd F HΞ R csD Hcls Vs Ss csV Nvs,
    Command.views_ok (fc_deps F) (fc_stack F) R csD Vs Ss csV Nvs -> exists v, views_search lvd F HΞ R csD Hcls = Command.run_success v.
Proof.
  intros * [Hs Hc Hn Hb]; unfold views_search.
  destruct (views_search_run lvd F HΞ R csD Hcls) as [[[Vf Af] (Hd & HF & Hbf)] | [[x e] Hf]]; [ eexists; reflexivity |].
  exfalso; apply (Hf (siblings_table Vs Ss) (meets_table Vs csV) Vs Hb).
  - intros y a Hy Ha.
    destruct (view_key_pos_in_some _ _ Hy) as [v Hv]; unfold siblings_table, meets_table, data_meets; rewrite Hv; split.
    + exact (view_siblings_functional _ _ _ _ _ _ (Forall2_index _ _ _ _ _ _ Hs Hv) (data_ok_siblings _ _ _ _ _ Ha)).
    + f_equal; exact (view_classify_functional _ _ _ _ _ _ (Forall2_index _ _ _ _ _ _ Hc Hv) (data_ok_cons _ _ _ _ _ Ha)).
  - exact (siblings_table_absent _ _).
  - intros y Hy; destruct (view_key_pos_in_some _ _ Hy) as [v Hv].
    exists (mk_view_data (List.nth v Ss nil) (List.nth v csV nil) (List.nth v Nvs nil)); constructor; cbn.
    + exact (Forall2_index _ _ _ _ _ _ Hs Hv).
    + exact (Forall2_index _ _ _ _ _ _ Hc Hv).
    + exact (Forall2_index _ _ _ _ _ _ Hn Hv).
Qed.
