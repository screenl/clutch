From Coq Require Import Reals Psatz.
From clutch.prob_lang Require Import lang tactics notation.
From clutch.prob Require Import distribution markov.
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
