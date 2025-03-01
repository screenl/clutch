From Coq Require Import Reals Psatz.
From iris.base_logic.lib Require Import invariants.
From clutch.prob_lang Require Import lang tactics notation.
From clutch.caliper Require Import weakestpre primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.
From clutch.caliper.examples Require Import biased martingale_rule.
From Coquelicot Require Export Hierarchy.

#[local] Open Scope R.

(* Markov Chain *)

Definition inv2 (n : nat): R := n / (2 * n + 1 : nat).

Lemma inv2P (n : nat): 0 <= inv2 n <= 1.
Proof.
  rewrite /inv2.
  split.
  - simpl. apply Rcomplements.Rdiv_le_0_compat; real_solver.
  - simpl. assert (0 < (2 * n + 1 : nat)). {
      simpl.
      real_solver.
    }
    apply (Rcomplements.Rdiv_le_1 _ (2 * n + 1 : nat) H).
    real_solver.
Qed.

Definition nrw_step (n : nat) :=
  match n with
    | 0 => dzero
    | S m => biased_conv_comb (inv2 n) (inv2P n) (dret m) (dret (S (S m)))
  end.

Lemma inv2s (n : nat): S n ≤ S (2 * S n).
Proof. lia. Qed.


Definition nrw_to_final (n : nat) : option nat :=
  match n with
    | 0 => Some 0%nat
    | S m => None
  end.

Definition fil_random_walk_mixin : MarkovMixin nrw_step nrw_to_final.
Proof. constructor. by intros [] [] []; simplify_eq=>/=. Qed.

Canonical Structure fil_random_walk : markov := Markov _ _ fil_random_walk_mixin.


Lemma n_step_rcoupl (n : nat) :
  Rcoupl (qfrac_flip (S n) (2 * S n) (inv2s n)) (step (S n)) (λ b a, if b then a = n else a = S(S n)).
Proof.
  intros.
  rewrite /qfrac_flip.
  replace (step (S n)) with (biased_coin (inv2 (S n)) (inv2P (S n)) ≫= λ b : bool, if b then dret n else dret (S (S n))). 2: {
    simpl. rewrite /biased_conv_comb. auto.
  }
  rewrite <- (dret_id_right (biased_coin _ _)).
  eapply Rcoupl_dbind.
  Unshelve. 3 : apply eq.
  { simpl. intros. destruct b; apply Rcoupl_dret; subst a; auto. }
  rewrite /inv2. 
  specialize (distr_ext (biased_coin (S n / S (2 * S n)) (qfrac_pos (S n) (2 * S n) (inv2s n))) (biased_coin (S n / (2 * S n + 1)%nat) (inv2P (S n)))) as ->.
  2 : { 
    Opaque INR.
    simpl. intros. rewrite /pmf. simpl.
    f_equal. f_equal. rewrite Nat.add_0_r.
    f_equal. f_equal. lia.
    Transparent INR.
  }
  apply Rcoupl_eq.
Qed.

Section Supermartingale.
  (* Supermartingale : the harmonic numbers *)

  Definition harmonic : nat -> R := sum_n_m (λ x, /INR x) 1.

  Lemma harmonic_pos (n:nat): 0 <= harmonic n.
  Proof.
    rewrite /harmonic.
    induction n.
    - rewrite sum_n_m_zero; try done. lia.
    - rewrite sum_n_Sm; last lia.
      replace (plus _ _) with (sum_n_m (λ x, /INR x) 1 n + /(S n))by done.
      apply Rplus_le_le_0_compat; try done.
      rewrite -Rdiv_1_l. apply Rcomplements.Rdiv_le_0_compat; try lra.
      apply pos_INR_S.
  Qed.

  Lemma harmonic_S (n:nat): harmonic (S n) = (harmonic n + / (S n)).
  Proof.
    rewrite {1}/harmonic. rewrite sum_n_Sm; last lia.
    apply Rplus_eq_compat_l. done.
  Qed.

  Lemma zero_harmonic: harmonic (0:nat) = 0.
  Proof.
    real_solver.
  Qed.

  Lemma harmonic_0 n : harmonic n = 0 -> n = 0%nat.
  Proof.
    intros.
    destruct n; auto.
    rewrite harmonic_S in H.
    assert (/(S n) > 0). { apply Rinv_pos. real_solver. }
    specialize (harmonic_pos n) as H'.
    lra.
  Qed.

  Lemma harmonic_term a : harmonic a = 0 -> is_final a.
  Proof.
    intro. apply harmonic_0 in H.
    subst a. rewrite /is_final; auto.
  Qed.

  Lemma harmonic_mono_l (n m : nat) : (m < n)%nat -> harmonic m < harmonic n.
  Proof.
    intro.
    induction n; inversion H.
    - subst m. rewrite harmonic_S. 
      rewrite <- Rplus_0_r at 1.
      apply Rplus_lt_compat_l.
      apply Rinv_pos. real_solver.
    - rewrite harmonic_S.
      etrans. { apply IHn. real_solver. }
      rewrite <- Rplus_0_r at 1.
      apply Rplus_lt_compat_l.
      apply Rinv_pos. real_solver.
  Qed.

  Lemma harmonic_mono_r (n m : nat) : harmonic m < harmonic n -> (m < n)%nat.
  Proof.
    intro.
    destruct (Nat.lt_decidable m n); auto.
    apply not_lt in H0.
    inversion H0.
    - subst n. apply Rlt_irrefl in H. tauto.
    - assert (n < m)%nat. { lia. }
      apply harmonic_mono_l in H3. apply Rlt_asym in H. tauto.
  Qed.

  Lemma harmonic_mono (n m : nat) : (m < n)%nat ↔ harmonic m < harmonic n.
  Proof.
    split.
    - apply harmonic_mono_l.
    - apply harmonic_mono_r.
  Qed.

  Lemma harmonic_nondec (n m : nat) : (m <= n)%nat ↔ harmonic m <= harmonic n.
  Proof.
    split.
    - intros. inversion H; try done.
      apply Rlt_le. apply harmonic_mono_l; lia.
    - intros.
      apply not_gt. assert ((m > n)%nat ↔ (n < m)%nat). { split; auto. }
      rewrite H0.
      rewrite harmonic_mono. lra.
  Qed.

  Lemma sum_n_m_le' (a b : nat -> R) (n m : nat):
    (forall k, (n ≤ k)%nat -> (k ≤ m)%nat-> a k <= b k)
    -> sum_n_m a n m <= sum_n_m b n m.
  Proof.
    intros H.
    case: (le_dec n m) => Hnm.
    - elim: m n a b Hnm H => /= [ | m IH] n a b Hnm H.
      + apply Nat.le_0_r in Hnm ; rewrite -Hnm.
        rewrite !sum_n_n. apply H; lia.
      + destruct n.
        --rewrite !sum_n_Sm ; try by apply Nat.le_0_l.
          apply Rplus_le_compat.
          ++ apply IH => //; auto; try lia.
          ++ apply H; lia.
        --rewrite -!sum_n_m_S.
          apply IH => //; auto; try lia.
          intros. apply H; try lia.
    - apply not_le in Hnm.
      rewrite !sum_n_m_zero //.
  Qed.

  Lemma harmonic_lb (n : nat) : 1 + n/2 <= harmonic (Nat.pow 2 n).
  Proof.
    induction n.
    - simpl. rewrite harmonic_S. rewrite zero_harmonic. 
      simpl. lra.
    - trans (harmonic (2 ^ n) + 1 / 2).
      + replace (1 + S n / 2) with (1 + n / 2 + 1 / 2). 2 : {
          rewrite S_INR. field. 
        }
        lra.
      + apply (Rplus_le_reg_l (- harmonic (2 ^ n))).
        field_simplify. rewrite Rplus_comm. field_simplify.
        unfold harmonic. 
        replace (sum_n_m (λ x : nat, / x) 1 (2 ^ S n) - sum_n_m (λ x : nat, / x) 1 (2 ^ n)) with (minus (sum_n (λ x : nat, / x) (2 ^ S n)) (sum_n (λ x : nat, / x) (2 ^ n))). 
        2 : { 
          f_equal. 
          - rewrite sum_n_m_sum_n; try real_solver. rewrite sum_O. rewrite Rinv_0. real_solver.
          - rewrite sum_n_m_sum_n; try real_solver. rewrite sum_O. rewrite Rinv_0. real_solver.
        }
        rewrite <- (sum_n_m_sum_n (λ x : nat, / x)). 2: {simpl. real_solver. }
        trans (sum_n_m (λ _, 1 / (2 ^ (S n))%nat) (S (2 ^ n)) (2 ^ S n)).
        --rewrite sum_n_m_const. simpl. 
          rewrite Nat.add_sub' Nat.add_0_r. 
          replace (INR (2 ^ n + 2 ^ n)) with (2 * (2 ^ n)%nat). 
          2 : { rewrite <- Rplus_diag. real_solver. }
          field_simplify; try real_solver. 
          apply not_0_INR.
          apply (Nat.pow_nonzero); auto.
        --apply sum_n_m_le'.
          intros. rewrite Rdiv_1_l.
          apply Rcomplements.Rinv_le_contravar; try real_solver.
  Qed.

  Lemma harmonic_step_total (a : mstate fil_random_walk) : ¬ is_final a → SeriesC (step a) = 1.
  Proof.
    intros. 
    destruct a.
    - assert False. { apply H. rewrite /is_final; auto. } tauto.
    - simpl. rewrite /biased_conv_comb. 
      rewrite biased_coin_dbind_mass. 
      rewrite !dret_mass.
      lra.
  Qed.

  Lemma harmonic_int (a : mstate fil_random_walk) : ¬ is_final a → ex_expval (step a) harmonic.
  Proof.
    intros.
    destruct a.
    - assert False. { apply H. rewrite /is_final; auto. } tauto.
    - apply ex_expval_biased_coin_dbind. 
      destruct b; apply ex_expval_dret.
  Qed.

  Lemma harmonic_dec (a : mstate fil_random_walk) : ¬ is_final a → Expval (step a) harmonic <= harmonic a.
  Proof.
    intros.
    destruct a.
    - assert False. { apply H. rewrite /is_final; auto. } tauto.
    - apply Req_le_sym. 
      rewrite Expval_dbind. 
      2 : { apply harmonic_pos. }
      2 : { apply (harmonic_int (S a) H). }
      rewrite Expval_biased_coin.
      rewrite !Expval_dret.
      rewrite !harmonic_S.
      unfold inv2. 
      do 2 rewrite Rmult_plus_distr_l.
      rewrite Rplus_assoc. rewrite <- Rplus_assoc.
      rewrite <- Rmult_plus_distr_r. rewrite Rplus_minus.
      rewrite Rmult_1_l.
      f_equal. 
      field_simplify_eq. 2: {split; real_solver. }
      rewrite Rplus_comm. rewrite <- Rplus_0_r at 1.
      f_equal. do 3 rewrite S_INR. rewrite plus_INR.
      rewrite INR_1. rewrite mult_INR.  
      rewrite !S_INR. simpl. ring.
  Qed.


  Instance fil_sm : sm harmonic := 
    Sm _ harmonic 
    harmonic_pos 
    harmonic_step_total 
    harmonic_term
    harmonic_int
    harmonic_dec.


  (* variant : identity *)
  Definition idN (n : nat) : nat := n.

  Lemma idN_term (a : mstate fil_random_walk) : is_final a -> idN a = 0%nat.
  Proof.
    intros.
    destruct a.
    - auto.
    - inversion H. inversion H0.
  Qed.

  Lemma idN_bound: ∀ r, ∃ u, ∀ a, harmonic a <= r → (idN a <= u)%nat.
  Proof.
    intros.
    destruct (INR_unbounded (2 * r - 1)) as [u H].
    exists (Nat.pow 2 u)%nat.
    intros. specialize (harmonic_lb u) as Haux.
    rewrite /idN. 
    apply <- harmonic_nondec.
    trans r; lra.
  Qed.

  Lemma n2fin (a m: nat) (H : (a < m)%nat) (n : fin m) : (Fin.of_nat_lt H = n)%fin ↔ a = n.
  Proof.
    split.
    - intros.
      rewrite <- (fin_to_nat_to_fin a m H).
      f_equal. auto.
    - intros.
      apply fin_to_nat_inj.
      rewrite (fin_to_nat_to_fin a m H).
      auto.    
  Qed.


  Lemma idN_dec: ∀ r, ∃ ε, ∀ a, ¬ is_final a -> harmonic a <= r → 
    0 < ε ∧ 
      SeriesC (λ b, if bool_decide (idN b < idN a)%nat then step a b else 0) > ε.
  Proof.
    intros.
    destruct (idN_bound r) as [u H].
    exists (1 / (2 * S u + 2)%nat).
    intros. apply H in H1.
    rewrite /idN. rewrite /idN in H0.
    split.
    { rewrite Rdiv_1_l. apply Rinv_0_lt_compat. real_solver. }
    destruct a. 
    + assert False. { apply H0. rewrite /is_final; auto. } tauto.
    + rewrite <- (SeriesC_ext (λ b : nat, if bool_decide (b ≤ a) then step (S a) b else 0)(λ b : nat, if bool_decide (b < S a)%nat then step (S a) b else 0)).
      2 : { intros. case_bool_decide; case_bool_decide; try lra; try lia.  }
      rewrite SeriesC_nat_bounded_fin.
      rewrite /biased_conv_comb.  
      assert (a < S a)%nat. { lia. }
      set af: fin (S a) := Fin.of_nat_lt H2.
      rewrite (SeriesC_ext _ (λ n: fin (S a), if bool_decide (n=af)%fin then (inv2 (S a)) else 0)).
      2: {
        intros. rewrite biased_conv_comb_pmf. 
        subst af.
        specialize (fin_to_nat_to_fin a (S a) H2) as Hf.
        case_bool_decide.
        - symmetry in H3. rewrite (n2fin _ _ H2) in H3.
          rewrite dret_1_1. 2: { auto. }
          rewrite dret_0. 2: { lia. }
          real_solver.
        - assert (nat_to_fin H2 ≠ n). {auto. } rewrite (n2fin _ _ H2) in H4.
          rewrite dret_0. 2: { lia. }
          rewrite dret_0. 2: { 
            specialize (fin_to_nat_lt n) as Hn.
            assert (n < S (S a))%nat; lia.
          }
          real_solver.
      }
      rewrite (SeriesC_singleton af).
      rewrite /idN in H1.
      unfold inv2.
      rewrite /gt.
      apply (Rge_gt_trans _ (1 / (2 * S a + 1)%nat)); rewrite !Rdiv_def.
      - apply Rmult_ge_compat; try real_solver. 
        { apply Rgt_ge. apply Rinv_pos. real_solver. } 
        assert (1 <= S a)%nat. {lia. } apply le_INR in H3. simpl in H3. real_solver. 
      - rewrite !Rmult_1_l. 
        apply Rinv_0_lt_contravar; try real_solver.
  Qed.

  Instance fil_variant : variant harmonic idN fil_sm := 
    Var _ _ _ _ idN_term idN_bound idN_dec.

  Theorem fil_AST (n : nat) :
    SeriesC (lim_exec n) = 1.
  Proof.
    apply (sm_term_limexec _ _ _ _ fil_variant).
  Qed.
End Supermartingale.


Definition fil_flip: val :=
  rec: "f" "x" := (rand (#2 * "x") < "x").

Lemma rwp_fil_flip `{!caliperG fil_random_walk Σ} E n: 
    {{{ specF (S n) }}} fil_flip #(S n) @ E {{{ (b : bool) a, RET #b; specF a ∗ ⌜if b then a = n else a = S (S n)⌝ }}}.
Proof.
  iIntros "% hs hf".
  rewrite /fil_flip.
  wp_pures.
  wp_apply (rwp_couple with "hs"). {
    apply mass_pos_reducible. simpl. rewrite biased_conv_comb_mass. 
    rewrite !dret_mass. lra.
  }
  { 
    eapply Rcoupl_refRcoupl, Rcoupl_swap, Rcoupl_biased_coin_dunifP. 
    erewrite (distr_ext (qfrac_flip (S n) _ _) (qfrac_flip (S n) (2 * S n) (inv2s n))) .
    2 : {
      Opaque INR.
      rewrite /qfrac_flip. rewrite /pmf. simpl. intros. 
      do 5 f_equal. lia.
    }
    apply n_step_rcoupl.
  }
  iIntros "%% (hs & %)".
  simpl in H.
  wp_pures. case_bool_decide; case_bool_decide; try lia.
  - iApply "hf". iFrame. auto.
  - iApply "hf". iFrame. auto.
  Unshelve.
  lia.
Qed.

Definition fil_prog : val :=
  rec: "f" "x" := 
    if: "x" = #0 then #() else
    if: (fil_flip "x") 
      then "f" ("x" - #1) else "f" ("x" + #1).

Lemma wp_fil_rw `{!caliperG fil_random_walk Σ} (n : nat) : 
  ⟨⟨⟨ specF n ⟩⟩⟩
    fil_prog #n
  ⟨⟨⟨ m, RET #(); specF m ⟩⟩⟩.
Proof.
  iIntros "% hs hf".
  iLöb as "IH" forall (n).
  unfold fil_prog.
  wp_pures.
  destruct n. { wp_pures. by iApply "hf". }
  wp_pures. 
  wp_apply (rwp_fil_flip with "hs").
  iIntros "%% (hs & %H)".
  destruct b; do 2 wp_pure.
  - replace #(S n - 1) with #(n). 2: { do 2 f_equal. lia. }
    subst a. wp_apply ("IH" with "[hs] [hf]"); iFrame.
  - replace #(S n + 1) with #(S (S n)). 2: { do 2 f_equal. lia. }
    subst a. wp_apply ("IH" with "[hs] [hf]"); iFrame.
Qed.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}.
Notation almost_surely_terminates ρ := (SeriesC (lim_exec ρ) = 1%R).

Theorem nat_rw_rec_ast (n: nat): almost_surely_terminates ((fil_prog #n)%E, σ₀).
Proof.
  eapply Rle_antisym; [done|].
  transitivity (SeriesC (lim_exec n)).
  { by rewrite fil_AST. }
  eapply (rwp_soundness_mass (tprΣ fil_random_walk)).
  iIntros (?) "h".
  wp_apply (wp_fil_rw with "h"); eauto.
Qed.