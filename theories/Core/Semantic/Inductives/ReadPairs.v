(** * Two Stuck Eliminators Read Alike

    A stuck eliminator is read as the eliminator of the group its member is
    at (E1′: its own group's, or the container's at a view), block by block
    over that group's members, branch by branch over their constructors.
    Two stuck eliminators read as the eliminator of the same group read
    back alike when their motives read alike block by block, and their
    branches at the motives' instances branch by branch.  The two need not
    be of the same group: a container's eliminator against the eliminator
    of a group with a view of it.  Only the readback is used here: what is
    read alike comes in as [per_top_typ] and [per_top] facts. *)

From Stdlib Require Import Lia List PeanoNat Relation_Definitions RelationClasses.

From Mctt Require Import LibTactics.
From Mctt.Core Require Import Base.
From Mctt.Core.Syntactic.Inductives Require Import Inductives.
From Mctt.Core.Semantic Require Import PER Realizability.
From Mctt.Core.Semantic.Inductives Require Import IndElim.
Import Domain_Notations Fixed_Notations.
#[local] Open Scope list_scope.

Section Fixed_GCtx.
  Context {GC : GCtx}.

  (** The two eliminators: of the group [Da] at [pa], its blocks [Bksa] in
      [ρa] at the uniform parameters [ua], and of [Db] at [pb], [Bksb] in
      [ρb] at [ub]. *)
  Section ReadPairs.
    Variables (pa : qname) (Da : ind_decl) (ua : list domain) (Bksa : list eblock) (ρa : env).
    Variables (pb : qname) (Db : ind_decl) (ub : list domain) (Bksb : list eblock) (ρb : env).
    Hypotheses (Hla : ind_lookup gc_deps gc_stack pa = Some Da) (Hlb : ind_lookup gc_deps gc_stack pb = Some Db).

    (** What the two readbacks need of a branch: the constructor [c] of the
        member [Mi] of the group read (kinds [gs']), at the member [Mva] of
        [Da] and [Mvb] of [Db] the blocks are of, under their fresh
        non-uniform parameters [nsa] and [nsb]: the fresh arguments and
        recursive results on each side, the branches' values there and
        their types, the motives [Aa] and [Ab] at the constructor, read
        alike.  [Dc] is the group read. *)
    #[warnings="-cannot-define-projection"]
    Record branch_read_pair (s : nat) (Dc : ind_decl) (Mi : imember) (hd : qname) (k : nat) (prea preb : list domain)
        (Mva Mvb : imember) (Aa Ab : exp) (nsa nsb : list domain) (c : String.string) (gs' : list carg)
        (na nb : nat) (Ba Bb : exp) : Prop := mk_branch_read_pair
      { (** The constructor's argument kinds at [Mva] *)
        branch_read_pair_gsa : list carg
        (** The constructor's argument kinds at [Mvb] *)
      ; branch_read_pair_gsb : list carg
        (** The fresh arguments, left *)
      ; branch_read_pair_vsa : list domain
        (** The fresh arguments, right *)
      ; branch_read_pair_vsb : list domain
        (** The fresh recursive results, left *)
      ; branch_read_pair_ihsa : list domain
        (** The fresh recursive results, right *)
      ; branch_read_pair_ihsb : list domain
        (** The recursive results the branch is read under, left *)
      ; branch_read_pair_wa : list domain
        (** The recursive results the branch is read under, right *)
      ; branch_read_pair_wb : list domain
        (** The left branch's value *)
      ; branch_read_pair_ra : domain
        (** The right branch's value *)
      ; branch_read_pair_rb : domain
        (** The left motive at the constructor *)
      ; branch_read_pair_ta : domain
        (** The right motive at the constructor *)
      ; branch_read_pair_tb : domain
        (** [c] is a constructor of [Mva] *)
      ; branch_read_pair_con_a : ind_con Mva c = Some branch_read_pair_gsa
        (** [c] is a constructor of [Mvb] *)
      ; branch_read_pair_con_b : ind_con Mvb c = Some branch_read_pair_gsb
        (** The left branch binds what it should *)
      ; branch_read_pair_arity_a : na = (im_nn Mi + List.length gs' + cargs_nrec Da branch_read_pair_gsa)%nat
        (** The right branch binds what it should *)
      ; branch_read_pair_arity_b : nb = (im_nn Mi + List.length gs' + cargs_nrec Db branch_read_pair_gsb)%nat
        (** The left recursive arguments' parameter counts *)
      ; branch_read_pair_plen_a : cargs_plen Da branch_read_pair_gsa
        (** The right recursive arguments' parameter counts *)
      ; branch_read_pair_plen_b : cargs_plen Db branch_read_pair_gsb
        (** The left fresh recursive results are as many as the branch
            read binds *)
      ; branch_read_pair_count_a : cargs_nin Da Dc gs' branch_read_pair_gsa = cargs_nrec Dc gs'
        (** The right ones too *)
      ; branch_read_pair_count_b : cargs_nin Db Dc gs' branch_read_pair_gsb = cargs_nrec Dc gs'
        (** The left arguments are fresh at [ua] *)
      ; branch_read_pair_args_a : Fcargs branch_read_pair_gsa of pa ua in gc_deps ⍮ gc_stack ⍮ env_args nil (ua ++ nsa) ⍮ (s + im_nn Mi)%nat ↘ branch_read_pair_vsa
        (** The right arguments are fresh at [ub] *)
      ; branch_read_pair_args_b : Fcargs branch_read_pair_gsb of pb ub in gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ nsb) ⍮ (s + im_nn Mi)%nat ↘ branch_read_pair_vsb
        (** The left fresh recursive results *)
      ; branch_read_pair_ihs_a : Fihs branch_read_pair_vsa at gs' branch_read_pair_gsa of Dc under ρa (blocks_motives Bksa) at pa ua
          in gc_deps ⍮ gc_stack ⍮ env_args nil (ua ++ nsa) ⍮ (s + im_nn Mi + List.length gs')%nat ↘ branch_read_pair_ihsa
        (** The right fresh recursive results *)
      ; branch_read_pair_ihs_b : Fihs branch_read_pair_vsb at gs' branch_read_pair_gsb of Dc under ρb (blocks_motives Bksb) at pb ub
          in gc_deps ⍮ gc_stack ⍮ env_args nil (ub ++ nsb) ⍮ (s + im_nn Mi + List.length gs')%nat ↘ branch_read_pair_ihsb
        (** The left results, the nested-through ones by the eliminator *)
      ; branch_read_pair_wrap_a : ⟦wihs branch_read_pair_vsa of gs' branch_read_pair_gsa of Dc with branch_read_pair_ihsa under pa ua Bksa ⟧
          gc_deps ⍮ gc_stack ⍮ ρa ↘ branch_read_pair_wa
        (** The right results, likewise *)
      ; branch_read_pair_wrap_b : ⟦wihs branch_read_pair_vsb of gs' branch_read_pair_gsb of Dc with branch_read_pair_ihsb under pb ub Bksb ⟧
          gc_deps ⍮ gc_stack ⍮ ρb ↘ branch_read_pair_wb
        (** The left branch evaluated there *)
      ; branch_read_pair_branch_a : ⟦ Ba ⟧ env_args ρa (nsa ++ branch_read_pair_vsa ++ branch_read_pair_wa) ↘ branch_read_pair_ra
        (** The right branch evaluated there *)
      ; branch_read_pair_branch_b : ⟦ Bb ⟧ env_args ρb (nsb ++ branch_read_pair_vsb ++ branch_read_pair_wb) ↘ branch_read_pair_rb
        (** The left motive at the constructor *)
      ; branch_read_pair_type_a : ⟦ Aa ⟧ env_args ρa (nsa ++ d_con hd k c (prea ++ nsa ++ branch_read_pair_vsa) :: nil) ↘ branch_read_pair_ta
        (** The right motive at the constructor *)
      ; branch_read_pair_type_b : ⟦ Ab ⟧ env_args ρb (nsb ++ d_con hd k c (preb ++ nsb ++ branch_read_pair_vsb) :: nil) ↘ branch_read_pair_tb
        (** The two branches read back alike at their types *)
      ; branch_read_pair_read : per_top (⇓ branch_read_pair_ta branch_read_pair_ra) (⇓ branch_read_pair_tb branch_read_pair_rb) }.

    Lemma read_brs_pair : forall s Dc Mi hd k prea preb Mva Mvb Aa Ab nsa nsb,
        Ftele List.rev (im_nparams Mva) in gc_deps ⍮ gc_stack ⍮ env_args nil ua ⍮ s ↘ nsa ->
        Ftele List.rev (im_nparams Mvb) in gc_deps ⍮ gc_stack ⍮ env_args nil ub ⍮ s ↘ nsb ->
        forall cs Bs1 Bs2,
        (forall c gs' na Ba nb Bb, In (c, gs') cs -> In (c, na, Ba) Bs1 -> In (c, nb, Bb) Bs2 ->
           branch_read_pair s Dc Mi hd k prea preb Mva Mvb Aa Ab nsa nsb c gs' na nb Ba Bb) ->
        brs_names cs Bs1 -> brs_names cs Bs2 ->
        exists Bs', Rbrs Bs1 at cs of Mi (hd, k, prea) of Dc from pa ua Bksa Mva Aa in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ Bs' /\
          Rbrs Bs2 at cs of Mi (hd, k, preb) of Dc from pb ub Bksb Mvb Ab in gc_deps ⍮ gc_stack ⍮ ρb ⍮ s ↘ Bs'.
    Proof.
      intros s Dc Mi hd k prea preb Mva Mvb Aa Ab nsa nsb Fa Fb.
      induction cs as [| [c gs'] cs IH]; intros [| [[c1 n1] B1] Bs1] [| [[c2 n2] B2] Bs2] Hcs Hn1 Hn2;
        cbn in Hn1, Hn2; try discriminate.
      - exists nil; split; constructor.
      - injection Hn1 as <- Hn1; injection Hn2 as <- Hn2.
        destruct (Hcs c gs' n1 B1 n2 B2 ltac:(left; reflexivity) ltac:(left; reflexivity) ltac:(left; reflexivity))
          as [gsa gsb vsa vsb ihsa ihsb wa wb ra rb ta tb Ca Cb Ara Arb Pa Pb Na Nb Ga Gb Ia Ib Wa Wb Ea Eb Ta Tb Hrd].
        destruct (Hrd (s + (im_nn Mi + List.length gs' + cargs_nrec Dc gs'))) as (B' & RB1 & RB2).
        destruct (IH Bs1 Bs2) as (Bs' & RBs1 & RBs2).
        { intros c' g' na Ba nb Bb Hin H1 H2; apply Hcs; right; assumption. }
        { exact Hn1. }
        { exact Hn2. }
        exists (cons (mk_normal_branch c (im_nn Mi + List.length gs' + cargs_nrec Dc gs') B') Bs'); split.
        + eapply read_brs_cons; [ exact Ca | exact Hla | exact Ara | reflexivity | exact Na | exact Pa | exact Fa | exact Ga
                                | exact Ia | exact Wa | exact Ea | exact Ta | exact RB1 | exact RBs1 ].
        + eapply read_brs_cons; [ exact Cb | exact Hlb | exact Arb | reflexivity | exact Nb | exact Pb | exact Fb | exact Gb
                                | exact Ib | exact Wb | exact Eb | exact Tb | exact RB2 | exact RBs2 ].
    Qed.

    (** What the two readbacks need of a block: the one of the member [Mi]
        of the group read, the blocks of the members of [Da] and [Db] the
        selections [sela] and [selb] give, the references the scrutinee's
        type is read at, the fresh non-uniform parameters on each side, the
        motives there read alike, and each branch. *)
    #[warnings="-cannot-define-projection"]
    Record block_read_pair (s : nat) (Dc : ind_decl) (sela selb : option (list nat)) (i : nat) (Mi : imember) : Prop :=
      mk_block_read_pair
      { (** The left block's member of [Da] *)
        block_read_pair_Mva : imember
        (** The right block's member of [Db] *)
      ; block_read_pair_Mvb : imember
        (** The left block *)
      ; block_read_pair_ba : eblock
        (** The right block *)
      ; block_read_pair_bb : eblock
        (** The group of the scrutinee type's declared member *)
      ; block_read_pair_hd : qname
        (** That declared member *)
      ; block_read_pair_k : nat
        (** The scrutinee type's uniform parameters, left *)
      ; block_read_pair_prea : list domain
        (** The scrutinee type's uniform parameters, right *)
      ; block_read_pair_preb : list domain
        (** The fresh non-uniform parameters, left *)
      ; block_read_pair_nsa : list domain
        (** The fresh non-uniform parameters, right *)
      ; block_read_pair_nsb : list domain
        (** The left motive's value *)
      ; block_read_pair_aa : domain
        (** The right motive's value *)
      ; block_read_pair_ab : domain
        (** The left member is [sela]'s choice *)
      ; block_read_pair_member_a : ind_member Da (elim_src sela i) = Some block_read_pair_Mva
        (** The right member is [selb]'s choice *)
      ; block_read_pair_member_b : ind_member Db (elim_src selb i) = Some block_read_pair_Mvb
        (** The left block is that member's *)
      ; block_read_pair_block_a : List.nth_error Bksa (elim_src sela i) = Some block_read_pair_ba
        (** The right block is that member's *)
      ; block_read_pair_block_b : List.nth_error Bksb (elim_src selb i) = Some block_read_pair_bb
        (** The left motive binds [Mi]'s parameters and the scrutinee *)
      ; block_read_pair_nm_a : eb_nm block_read_pair_ba = S (im_nn Mi)
        (** So does the right one *)
      ; block_read_pair_nm_b : eb_nm block_read_pair_bb = S (im_nn Mi)
        (** The left member's type at [ua] *)
      ; block_read_pair_ref_a : ⟦mref elim_src sela i of pa ua ⟧ gc_deps ⍮ gc_stack ↘ (block_read_pair_hd, block_read_pair_k, block_read_pair_prea)
        (** The right member's type at [ub] *)
      ; block_read_pair_ref_b : ⟦mref elim_src selb i of pb ub ⟧ gc_deps ⍮ gc_stack ↘ (block_read_pair_hd, block_read_pair_k, block_read_pair_preb)
        (** The left fresh non-uniform parameters *)
      ; block_read_pair_params_a : Ftele List.rev (im_nparams block_read_pair_Mva) in gc_deps ⍮ gc_stack ⍮ env_args nil ua ⍮ s ↘ block_read_pair_nsa
        (** The right fresh non-uniform parameters *)
      ; block_read_pair_params_b : Ftele List.rev (im_nparams block_read_pair_Mvb) in gc_deps ⍮ gc_stack ⍮ env_args nil ub ⍮ s ↘ block_read_pair_nsb
        (** The left motive at a fresh scrutinee *)
      ; block_read_pair_motive_a : ⟦ eb_motive block_read_pair_ba ⟧
          env_args ρa (block_read_pair_nsa ++ ⇑! (d_ind block_read_pair_hd block_read_pair_k (block_read_pair_prea ++ block_read_pair_nsa)) ((s + im_nn Mi)%nat) :: nil) ↘ block_read_pair_aa
        (** The right motive at a fresh scrutinee *)
      ; block_read_pair_motive_b : ⟦ eb_motive block_read_pair_bb ⟧
          env_args ρb (block_read_pair_nsb ++ ⇑! (d_ind block_read_pair_hd block_read_pair_k (block_read_pair_preb ++ block_read_pair_nsb)) ((s + im_nn Mi)%nat) :: nil) ↘ block_read_pair_ab
        (** The two motives read back alike *)
      ; block_read_pair_motive_read : per_top_typ block_read_pair_aa block_read_pair_ab
        (** The left block has one branch per constructor of [Mi] *)
      ; block_read_pair_names_a : brs_names (im_cons Mi) (eb_brs block_read_pair_ba)
        (** So has the right one *)
      ; block_read_pair_names_b : brs_names (im_cons Mi) (eb_brs block_read_pair_bb)
        (** Each pair of branches is a [branch_read_pair] *)
      ; block_read_pair_branches : forall c gs' na Ba nb Bb, In (c, gs') (im_cons Mi) ->
          In (c, na, Ba) (eb_brs block_read_pair_ba) -> In (c, nb, Bb) (eb_brs block_read_pair_bb) ->
          branch_read_pair s Dc Mi block_read_pair_hd block_read_pair_k block_read_pair_prea block_read_pair_preb block_read_pair_Mva block_read_pair_Mvb (eb_motive block_read_pair_ba) (eb_motive block_read_pair_bb)
            block_read_pair_nsa block_read_pair_nsb c gs' na nb Ba Bb }.

    Lemma read_blocks_pair : forall s Dc sela selb Ms i,
        (forall n Mi, List.nth_error Ms n = Some Mi -> block_read_pair s Dc sela selb (i + n) Mi) ->
        exists NBks, Rblks i Ms of Dc from pa ua Bksa sela in gc_deps ⍮ gc_stack ⍮ ρa ⍮ s ↘ NBks /\
          Rblks i Ms of Dc from pb ub Bksb selb in gc_deps ⍮ gc_stack ⍮ ρb ⍮ s ↘ NBks.
    Proof.
      intros s Dc sela selb Ms; induction Ms as [| Mi Ms IH]; intros i0 HMs.
      - exists nil; split; constructor.
      - destruct (HMs 0 Mi eq_refl) as [Mva Mvb ba bb hd k prea preb nsa nsb aa ab HMa HMb Hba Hbb Hnma Hnmb Ra Rb Fa Fb Ea Eb
                                        Hrd Hna Hnb Hbrs].
        rewrite Nat.add_0_r in *.
        destruct (Hrd (S (s + im_nn Mi))) as (A' & RA1 & RA2).
        destruct (read_brs_pair s Dc Mi hd k prea preb Mva Mvb (eb_motive ba) (eb_motive bb) nsa nsb Fa Fb
                    (im_cons Mi) (eb_brs ba) (eb_brs bb) Hbrs Hna Hnb) as (Bs' & RB1 & RB2).
        destruct (IH (S i0)) as (NBks & RN1 & RN2).
        { intros n Mi' Hn; replace (S i0 + n) with (i0 + S n) by lia; exact (HMs (S n) Mi' Hn). }
        exists (cons (mk_normal_block (S (im_nn Mi)) A' Bs') NBks); split.
        + eapply read_blocks_cons; [ exact Hla | exact HMa | exact Hba | exact Hnma | exact Ra | exact Fa | exact Ea
                                   | exact RA1 | exact RB1 | exact RN1 ].
        + eapply read_blocks_cons; [ exact Hlb | exact HMb | exact Hbb | exact Hnmb | exact Rb | exact Fb | exact Eb
                                   | exact RA2 | exact RB2 | exact RN2 ].
    Qed.

    (** Two stuck eliminators read as the eliminator of the member [k] of
        the group [Dq] at [pc]: alike, when its uniform parameters as each
        carries them read alike, the scrutinees read alike, and the blocks
        read alike block by block, under fresh variables from any level. *)
    Lemma per_bot_elim_pair : forall ja Mja jb Mjb pc k Dq Mk asa asb ea eb prea preb,
        ind_member Da ja = Some Mja -> ind_member Db jb = Some Mjb ->
        im_ref pa ja Mja = (pc, k) -> im_ref pb jb Mjb = (pc, k) ->
        ind_lookup gc_deps gc_stack pc = Some Dq -> ind_member Dq k = Some Mk ->
        List.length asa = im_np Dq Mk -> List.length asb = im_np Dq Mk ->
        blocks_nm_at Da None Bksa -> blocks_nm_at Db None Bksb ->
        rview_leaf_arity Da -> rview_leaf_arity Db ->
        ⟦mref ja of pa ua ⟧ gc_deps ⍮ gc_stack ↘ (pc, k, prea) -> ⟦mref jb of pb ub ⟧ gc_deps ⍮ gc_stack ↘ (pc, k, preb) ->
        per_top_ps (List.rev (ind_uparams Dq)) prea preb ->
        Dom ea ≈ eb ∈ per_bot ->
        (forall s n Mn, List.nth_error (ind_bmembers Dq) n = Some Mn -> block_read_pair s Dq (im_sel Mja) (im_sel Mjb) n Mn) ->
        Dom d_elim ρa Bksa pa ua ja asa ea ≈ d_elim ρb Bksb pb ub jb asb eb ∈ per_bot.
    Proof.
      intros * HMa HMb Hra Hrb Hq HMk La Lb Hnma Hnmb Hara Harb Ra Rb Hps He Hblk s.
      destruct (He s) as (M & RM1 & RM2).
      destruct (Hps s) as (Us & RU1 & RU2).
      destruct (read_blocks_pair s Dq (im_sel Mja) (im_sel Mjb) (ind_bmembers Dq) 0) as (NBks & RB1 & RB2).
      { intros n Mn Hn; exact (Hblk s (0 + n) Mn Hn). }
      exists (ne_elim pc Us k NBks M); split.
      - eapply read_ne_elim; [ exact Hla | exact HMa | exact Hra | exact Hq | exact HMk | exact La | exact Hnma | exact Hara
                             | exact Ra | exact RU1 | exact RB1 | exact RM1 ].
      - eapply read_ne_elim; [ exact Hlb | exact HMb | exact Hrb | exact Hq | exact HMk | exact Lb | exact Hnmb | exact Harb
                             | exact Rb | exact RU2 | exact RB2 | exact RM2 ].
    Qed.
  End ReadPairs.
End Fixed_GCtx.
