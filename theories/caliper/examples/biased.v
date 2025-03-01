From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang tactics notation.
From clutch.prob Require Import distribution markov couplings.
From Coquelicot Require Export Hierarchy.

#[local] Open Scope R.

Lemma biased_coin_mass r (P : 0 <= r <= 1) :
  SeriesC (biased_coin r P) = 1.
Proof.
  rewrite SeriesC_bool.
  rewrite /pmf /= /fair_coin /=. lra.
Qed.

Lemma biased_coin_pmf_t r (P : 0 <= r <= 1):
  biased_coin r P true = r.
Proof. done. Qed.

Lemma biased_coin_pmf_f r (P : 0 <= r <= 1):
  biased_coin r P false = 1-r.
Proof. done. Qed.

Lemma ex_expval_biased_coin_dbind `{Countable A} r (P : 0 <= r <= 1)  (f : bool → distr A) h :
  (∀ b, ex_expval (f b) h) →
  ex_expval (biased_coin r P ≫= f) h.
Proof.
  intros Hf.
  rewrite /ex_expval.
  rewrite /pmf /= /dbind_pmf /=.
  setoid_rewrite SeriesC_bool.
  rewrite biased_coin_pmf_t biased_coin_pmf_f.
  setoid_rewrite Rmult_plus_distr_r.
  eapply ex_seriesC_plus.
  - setoid_rewrite Rmult_assoc.
    eapply ex_seriesC_scal_l.
    eapply Hf.
  - setoid_rewrite Rmult_assoc.
    eapply ex_seriesC_scal_l.
    eapply Hf.
Qed.

Lemma biased_coin_dbind_mass `{Countable A} (f : bool → distr A) r (P : 0 <= r <= 1):
  SeriesC (biased_coin r P ≫= f) = r * SeriesC (f true) + (1 - r) * SeriesC (f false).
Proof.
  rewrite {1}/pmf /= /dbind_pmf.
  rewrite (fubini_pos_seriesC (λ '(a, b), biased_coin r P a * f a b)).
  - rewrite SeriesC_bool.
    rewrite 2!SeriesC_scal_l.
    rewrite {1 3}/pmf /=. lra.
  - real_solver.
  - intros b. by apply ex_seriesC_scal_l.
  - eapply ex_seriesC_finite.
Qed.
  
Definition biased_conv_comb `{Countable A} r (P : 0 <= r <= 1)  (μ1 μ2 : distr A)
  := dbind (λ b, if b then μ1 else μ2) (biased_coin r P). 

Lemma biased_conv_comb_pmf `{Countable D} r (P : 0 <= r <= 1) (μ1 μ2 : distr D) (a : D) :
    biased_conv_comb r P μ1 μ2 a = r * (μ1 a) + (1 - r) * (μ2 a).
Proof.
  rewrite {1}/pmf /= /dbind_pmf.
  rewrite (SeriesC_ext _ (λ b, (if bool_decide (b = true) then r * μ1 a else 0) +
                                  if bool_decide (b = false) then (1-r) * μ2 a else 0)).
  2: { intros []; rewrite /= /pmf /=; lra. }                                
  erewrite SeriesC_plus; [|eapply ex_seriesC_singleton.. ].
  rewrite 2!SeriesC_singleton /=. lra.
Qed.

Lemma biased_conv_comb_mass `{Countable A} r (P : 0 <= r <= 1) (μ1 μ2 : distr A):
  SeriesC (biased_conv_comb r P μ1 μ2 ) = r * SeriesC μ1 + (1 - r) * SeriesC μ2.
Proof.
  rewrite -!SeriesC_scal_l.
  rewrite -SeriesC_plus; 
  try apply ex_seriesC_scal_l; auto.
  apply SeriesC_ext => a.
  rewrite biased_conv_comb_pmf.
  lra.
Qed.

Lemma Expval_biased_coin r P f :
  Expval (biased_coin r P) f = r * f (true) + (1 - r) * f (false).
Proof.
  rewrite /Expval/pmf. 
  simpl. unfold biased_coin_pmf.
  apply SeriesC_bool.
Qed.

Lemma natnle (n m : nat) : (n < m)%nat -> ¬ (m ≤ n)%nat.
Proof.
  intros.
  lia.
Qed.

Lemma natlen (n m : nat) :  ¬(n < m)%nat -> (m ≤ n)%nat.
Proof.
  intros.
  lia.
Qed.

Lemma sum_n_low' (n m: nat) (a : R) (H: (m < n)%nat): sum_n (λ x, if bool_decide (x < m)%nat then a else 0) n = a * m.
Proof.
  revert H. revert m.
  induction n.
  - lia.
  - intros. rewrite sum_Sn.
    case_bool_decide; try lia.
    rewrite plus_zero_r.
    destruct (Nat.eq_dec n m).
    + subst n. clear IHn H0 H. 
      destruct m.
      --rewrite sum_O. simpl. lra.
      --rewrite sum_Sn. case_bool_decide; try lia.
        rewrite plus_zero_r.
        rewrite (sum_n_ext_loc _ (λ _, a)). 2: {
          intros. case_bool_decide; try lia; auto.
        }
        rewrite sum_n_const. real_solver.
    + assert (m < n)%nat. {lia. }
      rewrite IHn; auto.
Qed.

Lemma sum_n_low (n m: nat) (a : R) (H: (m <= n)%nat): sum_n (λ x, if bool_decide (x < m)%nat then a else 0) n = a * m.
Proof.
  destruct (Nat.eq_dec n m).
  2: { assert (m < n)%nat; try lia. apply sum_n_low'. auto. }
  subst n.
  destruct m. 
  - rewrite sum_O. simpl. real_solver.
  - rewrite sum_Sn. rewrite (sum_n_ext_loc _ (λ _, a)). 2: {
      intros. case_bool_decide; try lia; auto.
    }
    rewrite sum_n_const. case_bool_decide; try lia.
    rewrite plus_zero_r.
    real_solver.
Qed.
    
Lemma sum_n_high' (n m: nat) (a : R) (H: (m < n)%nat): sum_n (λ x, if bool_decide (m ≤ x)%nat then a else 0) n = a * (S n - m)%nat.
Proof.
  induction n.
  - lia.
  - intros. rewrite sum_Sn.
    case_bool_decide; try lia.
    destruct (Nat.eq_dec n m).
    + subst n. clear IHn H0 H.  replace (S (S m) - m)%nat with (2)%nat. 2: {lia. }
      destruct m.
      -- rewrite sum_O. simpl. rewrite /plus. simpl. real_solver.
      -- rewrite sum_Sn. simpl. rewrite /plus. simpl. case_bool_decide; try lia.
         rewrite (sum_n_ext_loc _ (λ _, 0)). 2: {
           intros. case_bool_decide; try lia; auto.
         }
         rewrite sum_n_const.
         lra.
    + assert (m < n)%nat. {lia. }
      rewrite IHn; auto. rewrite /plus. simpl. replace (S (S n) - m)%nat with (S n - m + 1)%nat. 2:{
        lia.
      }
      rewrite plus_INR. simpl. field_simplify. real_solver.
Qed.

Lemma sum_n_high (n m: nat) (a : R) (H: (m <= n)%nat): sum_n (λ x, if bool_decide (m ≤ x)%nat then a else 0) n = a * (S n - m)%nat.
Proof.
  destruct (Nat.eq_dec n m).
  2: { assert (m < n)%nat; try lia. apply sum_n_high'. auto. }
  subst n.
  replace (S m - m)%nat with 1%nat. 2: {
    lia.
  }
  simpl.
  rewrite Rmult_1_r.
  induction m.
  - rewrite sum_O. auto.
  - rewrite sum_Sn. 
    rewrite (sum_n_ext_loc _ (λ _, 0)). 2: {
      intros. case_bool_decide; try lia; auto.
    } 
    rewrite sum_n_const. case_bool_decide; try lia.
    rewrite Rmult_0_r.
    rewrite plus_zero_l.
    auto.
Qed.

Section Qfrac. 

Lemma qfrac_pos (p q : nat) (h: (p <= S q)%nat): 0 <= p / (S q)%nat <= 1.
Proof.
  split.
  - simpl. apply Rcomplements.Rdiv_le_0_compat; real_solver.
  - simpl. assert (0 < (S q: nat)). {
      simpl.
      real_solver.
    }
    apply (Rcomplements.Rdiv_le_1 _ (S q : nat) H).
    real_solver.
Qed.

Context {A: Type} `{Countable A}.

Definition qfrac_flip (p q : nat) h:= 
  biased_coin (p / (S q)) (qfrac_pos p q h). 

Definition qfrac_ber (p q : nat) h (m n : A) := 
  biased_conv_comb (p / (S q)) (qfrac_pos p q h) (dret m) (dret n). 

Definition drcp_l_pmf p q (h : (p <= S q)%nat) : fin (S q) -> R :=
  fun n => 
    if bool_decide (n < p)%nat then 1 / p else 0.

Lemma drcp_l_mass p q h (hp : (p ≠ 0)%nat): SeriesC (drcp_l_pmf p q h) = 1.
Proof.
  intros. rewrite /drcp_l_pmf.
  rewrite SeriesC_fin_sum.
  rewrite (sum_n_ext _ (λ n : nat, if bool_decide (n < p)%nat then 1 / p else 0)).
  2: {
    intros. rewrite /extend_fin_to_R. case_bool_decide; destruct (le_lt_dec (S q) n); auto; try lia.
    - case_bool_decide; auto. rewrite (fin_to_nat_to_fin _ ) in H1. lia.
    - case_bool_decide; auto. rewrite (fin_to_nat_to_fin _ ) in H1. lia.
  }
  destruct (Nat.eq_dec p (S q)).
  { subst p. rewrite (sum_n_ext_loc _ (λ n, 1 / (S q))). {
      rewrite sum_n_const. field_simplify; try real_solver.
    } 
    intros. case_bool_decide; auto; try lia.
  }
  rewrite sum_n_low; try lia.
  field_simplify; try real_solver.
Qed.

Program Definition drcp_l p q (h : (p <= S q)%nat) := MkDistr (drcp_l_pmf p q h) _ _ _.
Next Obligation.
  intros. rewrite /drcp_l_pmf. case_bool_decide; real_solver.
Qed.
Next Obligation.
  intros. rewrite /drcp_l_pmf. apply ex_seriesC_finite.
Qed.
Next Obligation.
  intros. rewrite /drcp_l_pmf.
  rewrite SeriesC_fin_sum.
  rewrite (sum_n_ext _ (λ n : nat, if bool_decide (n < p)%nat then 1 / p else 0)).
  2: {
    intros. rewrite /extend_fin_to_R. case_bool_decide; destruct (le_lt_dec (S q) n); auto; try lia.
    - case_bool_decide; auto. rewrite (fin_to_nat_to_fin _ ) in H1. lia.
    - case_bool_decide; auto. rewrite (fin_to_nat_to_fin _ ) in H1. lia.
  }
  destruct (Nat.eq_dec p (S q)).
  { subst p. rewrite (sum_n_ext_loc _ (λ n, 1 / (S q))). {
      rewrite sum_n_const. field_simplify; try real_solver.
    } 
    intros. case_bool_decide; auto; try lia.
  }
  rewrite sum_n_low; try lia.
  destruct p; simpl; try lra.
  field_simplify; real_solver.
Qed.
  

Definition drcp_r_pmf p q (h : (p <= S q)%nat) : fin (S q) -> R :=
  fun n => 
    if bool_decide (p <= n)%nat then 1 / (S q - p)%nat else 0.

Lemma drcp_r_mass p q h (hpq : ((S q - p) ≠ 0)%nat) : SeriesC (drcp_r_pmf p q h) = 1.
Proof.
  intros. rewrite /drcp_r_pmf.
  rewrite SeriesC_fin_sum.
  rewrite (sum_n_ext_loc _ (λ n : nat, if bool_decide (p <= n)%nat then 1 / (S q - p)%nat else 0)).
  2: {
    intros. rewrite /extend_fin_to_R. case_bool_decide; destruct (le_lt_dec (S q) n); auto; try lia.
    - case_bool_decide; auto. rewrite (fin_to_nat_to_fin _ ) in H2. lia.
    - case_bool_decide; auto. rewrite (fin_to_nat_to_fin _ ) in H2. lia.
  }
  destruct (Nat.eq_dec p (S q)).
  { subst p. rewrite (sum_n_ext_loc _ (λ n, 0)). {
      rewrite sum_n_const. field_simplify; try real_solver.
    } 
    intros. case_bool_decide; auto; try lia.
  }
  rewrite sum_n_high; try lia.
  field_simplify; real_solver.
Qed.

Program Definition drcp_r p q (h : (p <= S q)%nat) := MkDistr (drcp_r_pmf p q h) _ _ _.
Next Obligation.
  intros. rewrite /drcp_r_pmf. case_bool_decide; real_solver.
Qed.
Next Obligation.
  intros. rewrite /drcp_r_pmf. apply ex_seriesC_finite.
Qed.
Next Obligation.
  intros. rewrite /drcp_r_pmf.
  rewrite SeriesC_fin_sum.
  rewrite (sum_n_ext_loc _ (λ n : nat, if bool_decide (p <= n)%nat then 1 / (S q - p)%nat else 0)).
  2: {
    intros. rewrite /extend_fin_to_R. case_bool_decide; destruct (le_lt_dec (S q) n); auto; try lia.
    - case_bool_decide; auto. rewrite (fin_to_nat_to_fin _ ) in H2. lia.
    - case_bool_decide; auto. rewrite (fin_to_nat_to_fin _ ) in H2. lia.
  }
  destruct (Nat.eq_dec p (S q)).
  { subst p. rewrite (sum_n_ext_loc _ (λ n, 0)). {
      rewrite sum_n_const. field_simplify; try real_solver.
    } 
    intros. case_bool_decide; auto; try lia.
  }
  rewrite sum_n_high; try lia.
  destruct (S q - p)%nat.
  - simpl. lra.
  - field_simplify; real_solver.
Qed.

Lemma drcp_l_pos p q (h : (p <= S q)%nat) n : drcp_l p q h n > 0 -> (n < p)%nat.
Proof.
  intros.
  rewrite /pmf in H0. simpl in H0. 
  rewrite /drcp_l_pmf in H0. simpl in H0. 
  case_bool_decide in H0; auto; lra.
Qed.

Lemma drcp_r_pos p q (h : (p <= S q)%nat) n : drcp_r p q h n > 0 -> p ≤ n.
Proof.
  intros.
  rewrite /pmf in H0. simpl in H0. 
  rewrite /drcp_r_pmf in H0. simpl in H0. 
  case_bool_decide in H0; auto; lra.
Qed.

Definition rcp_bu_dist p q (h : (p <= S q)%nat) b:= 
  if b 
  then drcp_l p q h
  else drcp_r p q h.

Lemma Rcoupl_biased_coin_dunifP_pre0 q h (μ : distr A) R :
  Rcoupl (qfrac_flip (S q) q h) μ R →
  Rcoupl (dunifP q) μ (λ n a, R (bool_decide (n < S q)%nat) a).
Proof.
  intros Hcpl.
  remember Hcpl as Hcpl'. clear HeqHcpl'.
  destruct Hcpl as [η [[He0 He1] He2]].
  assert (SeriesC (λ b : A, η (false, b)) = 0). {
    rewrite <- lmarg_pmf.
    rewrite He0. rewrite /qfrac_flip. rewrite /pmf.
    simpl. field_simplify; real_solver. 
  }
  assert (∀ a, 0 <= (λ b : A, η (false, b)) a ). {
    intros. real_solver.
  }
  apply SeriesC_correct' in H0. 2 : {
    apply ex_seriesC_lmarg; real_solver.
  }
  specialize (SeriesC_const0 _ H1 H0) as H'.
  simpl in H'.
  assert (∀ a, μ a = η (true, a)). {
    intros.
    rewrite <- He1.
    rewrite rmarg_pmf.
    rewrite SeriesC_bool. 
    rewrite H'. real_solver.
  }
  
  exists (dprod (dunifP q) μ).
  split; try split.
  - rewrite lmarg_dprod; auto. 
    rewrite <- (Rcoupl_mass_eq _ _ _ Hcpl').
    rewrite /qfrac_flip. apply biased_coin_mass. 
  - rewrite rmarg_dprod; auto. apply dunifP_mass.
  - intros. destruct p. simpl. 
    specialize (fin_to_nat_lt t) as ht.
    case_bool_decide; try lia. rewrite dprod_pos in H3.
    destruct H3. rewrite H2 in H5. apply He2 in H5.
    by simpl in H5.
Qed.


Lemma Rcoupl_biased_coin_dunifP_pre1 q h (μ : distr A) R :
  Rcoupl (qfrac_flip 0 q h) μ R →
  Rcoupl (dunifP q) μ (λ n a, R (bool_decide (n < 0)%nat) a).
Proof.
  intros Hcpl.
  remember Hcpl as Hcpl'. clear HeqHcpl'.
  destruct Hcpl as [η [[He0 He1] He2]].
  assert (SeriesC (λ b : A, η (true, b)) = 0). {
    rewrite <- lmarg_pmf.
    rewrite He0. rewrite /qfrac_flip. rewrite /pmf.
    simpl. field_simplify; real_solver. 
  }
  assert (∀ a, 0 <= (λ b : A, η (true, b)) a ). {
    intros. real_solver.
  }
  apply SeriesC_correct' in H0. 2 : {
    apply ex_seriesC_lmarg; real_solver.
  }
  specialize (SeriesC_const0 _ H1 H0) as H'.
  simpl in H'.
  assert (∀ a, μ a = η (false, a)). {
    intros.
    rewrite <- He1.
    rewrite rmarg_pmf.
    rewrite SeriesC_bool. 
    rewrite H'. real_solver.
  }
  
  exists (dprod (dunifP q) μ).
  split; try split.
  - rewrite lmarg_dprod; auto. 
    rewrite <- (Rcoupl_mass_eq _ _ _ Hcpl').
    rewrite /qfrac_flip. apply biased_coin_mass. 
  - rewrite rmarg_dprod; auto. apply dunifP_mass.
  - intros. destruct p. simpl. 
    rewrite dprod_pos in H3.
    destruct H3. rewrite H2 in H4. apply He2 in H4.
    by simpl in H4.
Qed.

Lemma Rcoupl_biased_coin_dunifP p q h (μ : distr A) R :
  Rcoupl (qfrac_flip p q h) μ R →
  Rcoupl (dunifP q) μ (λ n a, R (bool_decide (n < p)%nat) a).
Proof.
  destruct (Nat.eq_dec p (S q)) as [Hpsq|Hpsq].
  { subst p. apply Rcoupl_biased_coin_dunifP_pre0. }
  destruct (Nat.eq_dec p 0%nat) as [Hp|Hp].
  { subst p. apply Rcoupl_biased_coin_dunifP_pre1. }
  intros Hcpl.
  rewrite <- (dret_id_right μ).
  replace (dunifP q) with ((qfrac_flip p q h) ≫= (rcp_bu_dist p q h)).
  {
    eapply Rcoupl_dbind.
    Unshelve. 2:{ apply Hcpl. }
    intros b a. 
    exists (dprod (rcp_bu_dist p q h b) (dret a)).
    split; try split.
    - apply distr_ext_pmf. apply functional_extensionality. intros.
      rewrite lmarg_dprod_pmf. rewrite dret_mass. real_solver.
    - apply distr_ext_pmf. apply functional_extensionality. intros. 
      rewrite rmarg_dprod_pmf. rewrite <- Rmult_1_r.
      apply Rmult_eq_compat_l.
      destruct b.
      + apply drcp_l_mass; auto.
      + simpl. apply drcp_r_mass; lia.
    - intros. destruct p0 as (n, a'). simpl.
      case_bool_decide; rewrite dprod_pos in H1; 
      destruct H1; apply dret_pos in H3; subst a'.
      + destruct b. { apply H0. }
        simpl in H1. apply drcp_r_pos in H1.
        real_solver.
      + destruct b. 2: { apply H0. }
        simpl in H1. apply drcp_l_pos in H1. 
        contradiction.
  }
  apply distr_ext_pmf. apply functional_extensionality.
  intros. 
  rewrite /pmf.
  simpl. rewrite /dbind_pmf.
  rewrite SeriesC_bool. simpl. rewrite /pmf. 
  simpl. rewrite /drcp_l_pmf. rewrite /drcp_r_pmf.
  case_bool_decide; case_bool_decide; try lia.
  - destruct p.
    { simpl. real_solver. }
    field_simplify; auto; try real_solver.
  - replace (match q with | 0%nat => 1 | S _ => q + 1 end) with (INR (S q)%nat). 2 :{auto. }
    assert (INR ((S q - p)%nat) ≠ 0).
    {
      rewrite <- INR_0.
      apply not_INR.
      lia.
    }
    field_simplify; auto; try real_solver.
    replace (-p + S q) with (INR (S q - p)%nat).
    2 : { 
      rewrite Rplus_comm.
      rewrite <- Rminus_def.
      apply minus_INR; lia.
    }
    field_simplify; real_solver.
Qed.

End Qfrac.
From clutch.caliper Require Import weakestpre primitive_laws derived_laws proofmode.

Section Coupl.

  Context `{!caliperG δ Σ}.

  Definition biased_flip (p q : nat) (h : p ≤ S q) : expr :=
    (rand #(q) < #(p)).

  Lemma rwp_couple_biased_flip p q h E R a1 :
    Rcoupl (qfrac_flip p q h) (step a1) R →
    {{{ specF a1 }}} biased_flip p q h @ E {{{ (b : bool) a2, RET #b; specF a2 ∗ ⌜R b a2⌝  }}}.
  Proof.
    iIntros (? Φ) "Ha HΦ". rewrite /biased_flip.
    wp_pures.
    wp_apply (rwp_couple with "Ha").
    { eapply Rcoupl_mass_eq in H. rewrite biased_coin_mass in H.
      eapply mass_pos_reducible. lra. }
    { eapply Rcoupl_refRcoupl, Rcoupl_swap, Rcoupl_biased_coin_dunifP. apply H. }      
    iIntros (n a2) "[Ha %HR]". 
    wp_pures. simpl in HR. 
    case_bool_decide. 
    - iApply "HΦ". iModIntro. iFrame. case_bool_decide; auto; lia. 
    - iApply "HΦ". iModIntro. iFrame. case_bool_decide; auto; lia. 
  Qed. 

  Lemma rwp_biased_flip p q h E :
    ⟨⟨⟨ True ⟩⟩⟩ biased_flip p q h @ E ⟨⟨⟨ (b : bool), RET #(LitBool b); True ⟩⟩⟩.
  Proof.
    iIntros (Φ) "_ HΦ". rewrite /biased_flip.
    wp_bind (rand(_) _)%E.
    wp_apply (rwp_rand q with "[//]").
    iIntros (?) "_ /=".
    wp_pures.
    case_bool_decide.
    - iApply "HΦ". iFrame. inv_fin n; eauto.
    - iApply ("HΦ"). iFrame. inv_fin n; eauto.
  Qed.

End Coupl.