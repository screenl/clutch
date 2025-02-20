From Coq Require Import Reals Psatz.
From iris.base_logic.lib Require Import invariants.
From clutch.prob_lang Require Import lang tactics notation.
From clutch.caliper Require Import weakestpre primitive_laws proofmode adequacy.
From clutch.prob Require Import distribution markov.

#[local] Open Scope R.

Class sm {δ} (h : mstate δ → R) := Sm {
  sm_nneg a : 0 <= h a;
  sm_step_total (a : mstate δ) : ¬ is_final a → SeriesC (step a) = 1;
  sm_term a : h a = 0 → is_final a;
  sm_int a : ¬ is_final a → ex_expval (step a) h;
  sm_dec a : ¬ is_final a → Expval (step a) h <= h a;
}.

Class variant {δ} (h : mstate δ -> R) (g: mstate δ -> nat) 
  (s: sm h):= Var {
    var_term a: is_final a → g a = 0%nat;
    var_bound: ∀ r, ∃ u, ∀ a, h a <= r → (g a <= u)%nat;
    var_dec: ∀ r, ∃ ε, ∀ a, ¬ is_final a -> h a <= r → 
      0 < ε ∧ 
        SeriesC (λ b, if bool_decide (g b < g a)%nat then step a b else 0) > ε
}.

Lemma sm_term_limexec {δ} (a : mstate δ) (h : mstate δ → R) (g : mstate δ → nat)
  (s: sm h)
  (v: variant h g s):
    SeriesC (lim_exec a) = 1.
Admitted.

