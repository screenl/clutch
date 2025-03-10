From clutch.eris Require Export eris error_rules. 
From clutch.eris Require Export examples.approximate_samplers.approx_higherorder_rejection_sampler.
From clutch.caliper.examples Require Import nat_random_walk. 

Context `{!erisGS Σ}.

Local Open Scope R.

Definition urw : val :=
    (rec: "f" "n" :=
       if: "n" < #1
         then #()
         else let: "x" := (rand #1) in
                if: ("x" < #1)
                then "f" ("n" + #1)
                else "f" ("n" - #1)).

Definition pterm {δ : markov} (n : nat) (a : mstate δ) := SeriesC (exec n a).

Lemma nrw_pt_rec (m : mstate nat_random_walk) n: pterm n m + pterm n (S (S m))  = 2 * pterm (S n) (S m).
Proof.
  rewrite /pterm.
  rewrite -SeriesC_plus // -SeriesC_scal_l.
  apply SeriesC_ext => x.
  rewrite /exec.
  rewrite fair_conv_comb_dbind.
  rewrite 2!dret_id_left'.
  rewrite fair_conv_comb_pmf /=.
  real_solver.
Qed.

Lemma nrw_pt_0 (m : mstate nat_random_walk): pterm 0 m = 1 -> m = 0%nat.
Proof.
  rewrite /pterm. 
  simpl.
  destruct m; simpl; auto.
  rewrite dzero_mass. 
  lra.
Qed.

Lemma pmf_SeriesC_c: ∀ {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (d : distr A),
  0 <= 1 - SeriesC d.
Proof.
  intros.
  specialize (pmf_SeriesC d).
  lra.
Qed.

Lemma AST_pt_lim {δ : markov} (m : mstate δ) ε : 
  (∀ s : mstate δ, SeriesC (lim_exec s) = 1) ->
  ε < 1 -> ∃ n, ε < pterm n m.
Proof.
  intros Hst?.
  specialize (Hst m).
  rewrite lim_exec_Sup_seq in Hst. intros.
  assert (Lim_seq.is_sup_seq (λ n : nat, Rbar.Finite (SeriesC (exec n m))) (Rbar.Finite 1)). {
    rewrite <- Hst. rewrite rbar_finite_real_eq. 2: {
      apply is_finite_Sup_seq_SeriesC_exec.
    }
    apply Lim_seq.Sup_seq_correct.
  }
  unfold Lim_seq.is_sup_seq in H0.
  assert (0 < 1 - ε). { lra. }
  specialize H0 with (mkposreal (1 - ε) H1).
  simpl in H0. destruct H0 as [H0 [n H2]].
  exists n. rewrite /pterm. field_simplify in H2. apply H2.
Qed.

Lemma nat_rw_pre (m : mstate nat_random_walk) n E: 
  ↯ (1 - pterm n m) -∗
      WP urw #m @ E [{ v, True }].
Proof.
  iIntros "He".
  iInduction n as [|n] "IH" forall (m).
  - destruct m; wp_rec; wp_pures; auto.
    iApply ((twp_ec_spend _ _ _ 1%NNR) with "[He]"); simpl; auto; try real_solver. 
    replace (1 - pterm 0 (S m)) with 1. 2 : {
      rewrite /pterm /exec. simpl.
      rewrite dzero_mass. real_solver.
    } 
    iFrame.
  - wp_rec. destruct m; wp_pures; auto.
    case_bool_decide; try lia.
    wp_pures.
    set f11 := mknonnegreal (1 - pterm (S n) (S m)) (pmf_SeriesC_c _).
    set f00 := mknonnegreal (1 - pterm n m) (pmf_SeriesC_c _).
    set f20 := mknonnegreal (1 - pterm n (S (S m))) (pmf_SeriesC_c _).
    wp_apply 
      (flip_amplification f11 f00 f20 with "[He]"); simpl.
    + field_simplify. f_equal. 
      specialize (nrw_pt_rec m n) as h. real_solver.
    + iFrame.
    + iIntros "% (%hv & He)". 
      rewrite /scale_flip. rewrite /flip_is_1.
      destruct hv.
      --subst v. simpl. wp_pures. replace #(S m + 1) with #(S (S m)). 2 : { do 2 f_equal. lia. }
        wp_apply ("IH" with "He"). 
      --subst v. simpl. wp_pures. replace #(S m - 1) with #(m). 2 : { do 2 f_equal. lia. }
        wp_apply ("IH" with "He"). 
Qed.

Lemma nat_rw_twp ε (m : nat) E : 0 < ε -> 
  ↯ ε -∗
    WP urw #m @ E [{ v, True }].
Proof.
  iIntros "% He".
  assert (0 <= ε). { lra. }
  destruct (Rlt_le_dec ε 1).
  2 : {
    set e := mknonnegreal ε H0.
    wp_apply (twp_ec_spend _ _ _ e); simpl; auto; try lra. 
  }
  assert (1 - ε < 1). { lra. }
  specialize (AST_pt_lim m (1 - ε) nrw_AST H1) as [].
  assert (1 - pterm x m < ε). { lra. }
  iPoseProof ((ec_weaken _ (1 - pterm x m)) with "He") as "He".
  - split; try lra. apply pmf_SeriesC_c.
  - wp_apply nat_rw_pre; iFrame.
Qed.

Lemma ec_ast_amplify_pre {δ : markov} (σ : mstate δ) n (P : mstate δ -> iProp Σ) :  
  □ (∀ (ρ : mstate δ) m, (∀ σ': mstate δ, ↯(1 - pterm m σ') -∗ ⌜is_final σ'⌝ ∨ P σ') ∗ ↯(1 - pterm (S m) ρ) -∗ P ρ) ∗ 
  □ (∀ (ρ : mstate δ), ⌜is_final ρ⌝ -∗ P ρ)
      ⊢ (↯(1 - pterm n σ) -∗ P σ).
Proof.
  iIntros "[#Hnf #Hf] Herr".
  iInduction n as [|n] "IH" forall (σ).
  - destruct (is_final_dec σ).
    { iApply "Hf"; auto. }
    replace (1 - pterm 0 σ) with 1.
    2 : { 
      rewrite /pterm exec_O_not_final; auto.  
      rewrite dzero_mass. lra.
    }
    iExFalso.
    by iApply ec_contradict. 
  - iApply "Hnf". iFrame. iIntros "% Herr".
    iRight. by iApply "IH".
Qed.


Lemma ec_ast_amplify {δ : markov} (σ : mstate δ) ε (H : 0 < ε) (P : mstate δ -> iProp Σ) :  
  (∀ a : mstate δ , SeriesC (lim_exec a) = 1) ->
  □ (∀ (ρ : mstate δ) m, (∀ σ': mstate δ, ↯(1 - pterm m σ') -∗ ⌜is_final σ'⌝ ∨ P σ') ∗ ↯(1 - pterm (S m) ρ) -∗ P ρ) ∗ 
  □ (∀ (ρ : mstate δ), ⌜is_final ρ⌝ -∗ P ρ)
    ⊢ (↯ε -∗ P σ).
Proof.
  iIntros "% [#Hnf #Hf] Herr".
  apply (AST_pt_lim σ (1-ε)) in H0 as [n H0]; auto; try lra.
  iPoseProof ((ec_weaken ε (1 - pterm n σ)) with "[Herr]") as "Herr"; try iFrame.
  - pose proof (pmf_SeriesC (exec n σ)). 
    split; try lra. 
    rewrite /pterm. lra.
  - iApply ec_ast_amplify_pre; auto.
Qed.

Example nat_rw_twp' ε (m : nat) E : 0 < ε -> 
  ↯ ε -∗
    WP urw #m @ E [{ v, True }].
Proof.
  intros. iApply (ec_ast_amplify m ε H (λ n, WP urw #n @ E [{ _, True }])%I nrw_AST).
  iSplit; iModIntro.
  - iIntros "%n %t [Hind Herr]".
    destruct n.
    { wp_rec. wp_pures. auto. }
    wp_rec. wp_pures. case_bool_decide; try lia.
    wp_pures. 
    set f11 := mknonnegreal (1 - pterm (S t) (S n)) (pmf_SeriesC_c _).
    set f00 := mknonnegreal (1 - pterm t n) (pmf_SeriesC_c _).
    set f20 := mknonnegreal (1 - pterm t (S (S n))) (pmf_SeriesC_c _).
    wp_apply (flip_amplification f11 f00 f20 with "[Herr]"); simpl.
    + field_simplify. f_equal. 
      specialize (nrw_pt_rec n t) as h. real_solver.
    + iFrame.
    + iIntros "% [[%Hv | %Hv] Herr]"; subst v; 
      rewrite /scale_flip; rewrite /flip_is_1; wp_pures; simpl;
      iPoseProof ("Hind" with "Herr") as "[%IF|h]"; auto; 
      try destruct IF; try inversion H1.
      { replace #(S n + 1) with #(S (S n)). 
        2 : { do 4 f_equal. lia. }
        auto. } 
      { replace #(S n - 1) with #(n). 
        2 : { do 4 f_equal. lia. }
        destruct n.
        { wp_rec. wp_pures. auto. }
        { destruct H3. inversion H1. }}
      { replace #(S n - 1) with #(n). 
        2 : { do 4 f_equal. lia. }
        auto. }
  - iIntros. 
    destruct ρ.
    + wp_rec. wp_pures. auto.
    + destruct H0. inversion H0.
Qed.
    

    
