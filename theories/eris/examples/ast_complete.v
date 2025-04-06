(* From clutch.eris Require Export eris error_rules. 

Local Open Scope R.

Section Term.

Context `{!erisWpGS Λ Σ}.

Implicit Types ρ : language.cfg Λ.

Definition pterm (n : nat) ρ := SeriesC (exec n ρ).

Definition pterm_nnr (n : nat) ρ := mknonnegreal (pterm n ρ) (pmf_SeriesC_ge_0 _).

Lemma pterm_le1 (n : nat) ρ : (0 <= 1 - pterm n ρ)%R. 
Proof.
specialize (pmf_SeriesC (exec n ρ)) as he.
rewrite /pterm. apply -> Rcomplements.Rminus_le_0. auto.
Qed.

Definition pterm_comp (n : nat) ρ := mknonnegreal (1 - pterm n ρ) (pterm_le1 _ _).

Lemma pterm_rec (n : nat) ρ : 
  language.to_val ρ.1 = None ->
  pterm (S n) ρ = Expval (step ρ) (pterm n).
Proof.
  intros.
  rewrite /pterm exec_Sn dbind_mass /Expval.
  apply SeriesC_ext. intros.
  rewrite /step_or_final.
  rewrite /to_final. simpl. rewrite H. 
  auto.
Qed.

Lemma AST_pt_lim m ε : 
  SeriesC (lim_exec m) = 1 ->
  ε < 1 -> ∃ n, ε < pterm n m.
Proof.
  intros Hst?.
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

Lemma pterm_reducible (n : nat) ρ : 
  language.to_val ρ.1 = None ->
  0 < pterm n ρ ->
  reducible ρ.
Proof.
  rewrite /pterm.
  intros. apply SeriesC_gtz_ex in H0.
  2: apply pmf_pos.
  induction n.
  - destruct H0. rewrite /exec /to_final in H0. simpl in H0.
    rewrite H in H0.
    rewrite dzero_0 in H0. lra.
  - apply mass_pos_reducible.
    destruct H0.
    simpl in H0.
    rewrite H in H0.
    apply dbind_pos in H0.
    destruct H0 as [ρ' [H0 H1]].
    simpl.
    apply (SeriesC_pos _ ρ').
    + apply pmf_pos.
    + apply pmf_ex_seriesC.
    + apply H1.
Qed.




End Term.

Section Complete.

Context `{!erisGS Σ}.

Notation σ₀ := {| heap := ∅; tapes := ∅ |}.
Notation almost_surely_terminates ρ := (SeriesC (lim_exec ρ) = 1%R).
(* Maybe Provable? *)
Lemma state_incl_pterm_le n (σ1 σ2 : state) (e : expr):
  σ1.(tapes) ⊆ σ2.(tapes) -> σ1.(heap) ⊆ σ2.(heap) ->
    pterm n (e, σ1) <= pterm n (e, σ2).
Proof.
Admitted.

Definition state_decomp (σ : state) : iProp Σ := 
  ([∗ map] l ↦ p ∈ (σ.(heap)), l ↦ p)  ∗ 
  ([∗ map] l ↦ p ∈ (σ.(tapes)), l ↪ p) .

(* How?? *)
Lemma state_update_step_pos {e e' : expr} {σ σ1 σ' : state} :
  0 < step (e, σ) (e', σ') -> 
    state_interp σ1 ∗ state_decomp σ ==∗ state_interp σ' ∗ state_decomp σ'.
Proof.
Admitted.

Lemma dret_expos {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (a: A) : ∃ b, dret a b > 0.
Proof.
  exists a.
  rewrite dret_1_1; auto. lra.
Qed.

Lemma dmap_expos n σ2: ∃ ρ0 : expr * state,
  dmap (λ n0 : fin (S (Z.to_nat n)), ((#n0) : expr, σ2)) (dunifP (Z.to_nat n)) ρ0 > 0.
Proof.
  intros.
  exists (#0 : expr, σ2).
  eapply dmap_pos.
  exists 0%fin. split; auto.
  rewrite dunif_pmf. apply Rinv_pos. real_solver.
Qed.

Lemma gmap_contras {K V: Type} `{Countable K} {m1 m2 : gmap K V} k v : 
  m1 ⊆ m2 -> 
  m1 !! k = Some v -> 
  m2 !! k = None -> False.
Proof.
  intros.
  epose proof (lookup_weaken_is_Some m1 m2 k _ H0). 
  destruct H3. rewrite H3 in H2. inversion H2.
  Unshelve.
  by exists v.
Qed.

Lemma state_incl_head_reducible (σ1 σ2 : state) (e : expr):
  σ1.(tapes) ⊆ σ2.(tapes) -> σ1.(heap) ⊆ σ2.(heap) ->
    head_reducible e σ1 -> head_reducible e σ2.
Proof.
  rewrite /head_reducible. intros. 
  destruct e; inv_head_step; auto; 
  try apply dret_expos; 
  try apply dmap_expos; 
  exfalso; try apply (gmap_contras _ _ H H8 H12). 
  apply (gmap_contras _ _ H H8 H11). 
Qed.

(* Definition state_incl_transform σ1 σ2 e :=
  match e with
  | Val (LitV (LitLbl x)) => 
    if (bool_decide (x = fresh_loc (heap σ1))) 
    then #(fresh_loc (heap σ2)) : expr 
    else (if (bool_decide (x = fresh_loc (tapes σ1))) 
    then #(fresh_loc (tapes σ2)) : expr 
    else e)
  | _ => e
end. *)

(* Print expr.

Print subst'.
 *)

(* Lemma state_incl_reducible' (σ1 σ2 σ' : state) (e e' : expr):
  σ1.(tapes) ⊆ σ2.(tapes) -> σ1.(heap) ⊆ σ2.(heap) ->
    head_step e σ1 (e', σ') > 0 -> ∃ σ, head_step e σ2 (state_incl_transform e' σ1 σ2, σ) > 0.
Proof. 
  intros.
  destruct e; inv_head_step;
  try (exists σ2; rewrite dret_1_1; auto; lra); 
  try (exfalso; by eapply (gmap_contras _ _ H)).
  -  *)
(* Lemma state_incl_head_reducible' (σ1 σ2 σ' : state) (e e' : expr):
  σ1.(tapes) ⊆ σ2.(tapes) -> σ1.(heap) ⊆ σ2.(heap) ->
    head_step e σ1 (e', σ') > 0 -> ∃ σ, head_step e σ2 (e', σ) > 0.
Proof. 
  intros.
  destruct e; inv_head_step;
  try (exists σ2; rewrite dret_1_1; auto; lra); 
  try (exfalso; by eapply (gmap_contras _ _ H)).
  - admit. (* exists (state_upd_heap_N (fresh_loc (heap σ2)) (Z.to_nat n) v0 σ2). *)
  - exists (state_upd_heap <[l0:=v0]> σ2). rewrite dret_1_1; auto; lra.
  - admit.
  - exists σ2. eapply dmap_pos.
    by exists x.
  - exists σ2. eapply dmap_pos.
    by exists x1.
  - eexists. rewrite dret_1_1; auto; lra.
  - exists σ2. eapply dmap_pos. 
    by exists x1.


Admitted. *)
Print expr.

Print base_lit.
Fixpoint is_pure (e : expr) := 
  match e with
  | Rec _ _ e' => is_pure e'
  | App e1 e2 => is_pure e1 && is_pure e2
  | UnOp _ e2 => is_pure e2
  | BinOp _ e1 e2 => is_pure e1 && is_pure e2
  | If e1 e2 e3 => is_pure e1 && is_pure e2 && is_pure e3
  | Pair e1 e2 => is_pure e1 && is_pure e2
  | Fst e' => is_pure e'
  | Snd e' => is_pure e'
  | InjL e' => is_pure e'
  | InjR e' => is_pure e'
  | Case e1 e2 e3 => is_pure e1 && is_pure e2 && is_pure e3
  | Rand _ (LitV (LitUnit))=> true
  | AllocN _ _ | Load _ | Store _ _ | AllocTape _ | Rand _ _ => false
  | _ => true
end.

Lemma pure_state_head_step (e e' : expr) (σ σ': state) : 
  is_pure e = true -> head_step e σ' (e', σ) > 0 -> σ = σ'.
Proof.
  intros.
  destruct e; inv_head_step; auto.
Qed.


Lemma pure_head_step_inv (e e' : expr) (σ : state):
  is_pure e = true -> 
  head_step e σ (e', σ) > 0 -> 
  is_pure e' = true.
Proof.
  intros.
  destruct e; inv_head_step; auto; try apply andb_prop in H as [H1 H2]; auto.
  - admit.
  - by rewrite H1.
  - by rewrite H2.
Admitted.

Lemma is_pure_heads (e : expr): 
  is_pure e = true -> is_pure (decomp e).2 = true.
Proof.
  destruct (decomp e) eqn : Hde.
  simpl.
  remember (length l).
  revert e e0 l Hde Heqn.
  induction n.
  {
    intros.
    destruct l; inversion Heqn.
    apply decomp_inv_nil in Hde as [Hd Hde].
    by subst e.
  }
  intros.
  rewrite decomp_unfold in Hde.
  destruct (ectxi_language.decomp_item e) eqn : Hde'; intros.
  2: {inversion Hde. by subst e. }
  destruct p.
  destruct (decomp e2) eqn: Hde2.
  inversion Hde.
  subst e3. 
Admitted.


Lemma pure_state_step (e e' : expr) (σ σ': state) : 
  is_pure e = true -> step (e, σ) (e', σ') > 0 -> σ = σ'.
Proof.
  rewrite /step. simpl. rewrite /prim_step. simpl.
  destruct (decomp e) eqn: Hde. rewrite Hde. simpl.
  rewrite dmap_pos. 
  intros. destruct H0 as [a [H0 H1]]. destruct a.
  simpl in H0. inversion H0. 
  apply is_pure_heads in H. rewrite Hde in H. 
  apply pure_state_head_step in H1; subst; auto.
Qed.

Lemma dret_cfg_eq (e e': expr) (σ1 σ2: state) :
  dret (e, σ1) (e', σ1) = dret (e, σ2) (e', σ2).
Proof.
  destruct (decide (e = e')); try subst e'. 
  - rewrite !dret_1_1; auto.
  - rewrite !dret_0; auto;
    move => a; apply n; by inversion a.
Qed.

Lemma pure_step (e e': expr) (σ1 σ2: state) :
  is_pure e = true -> step (e, σ1) (e', σ1) = step (e, σ2) (e', σ2).
Proof.
  intros.
  rewrite /step. simpl. rewrite /prim_step. simpl.
  destruct (decomp e) eqn: Hde. rewrite Hde. simpl.
  apply is_pure_heads in H. rewrite Hde in H. simpl in H.
  destruct e0; inv_head_step; 
  try (rewrite dmap_dzero; by rewrite !dzero_0);
  try (rewrite !dmap_dret /fill_lift; apply (dret_cfg_eq _ e' σ1 σ2)). 
  erewrite !dmap_comp.
  rewrite /fill_lift. simpl.
  replace ((λ '(e0, σ), (fill l e0, σ)) ∘ λ n0 : fin (S (Z.to_nat n)), (_, σ1)) with (λ n0 : fin (S (Z.to_nat n)), (fill l #n0, σ1)).
  2: by apply functional_extensionality.
  replace ((λ '(e0, σ), (fill l e0, σ)) ∘ λ n0 : fin (S (Z.to_nat n)), (_, σ2)) with (λ n0 : fin (S (Z.to_nat n)), (fill l #n0, σ2)).
  2: by apply functional_extensionality.
  rewrite !dmap_unfold_pmf.
  apply SeriesC_ext.
  intros. case_bool_decide; case_bool_decide; auto.
  - inversion H. subst e'. contradiction.
  - inversion H0. subst e'. contradiction.
Qed.

Lemma pure_pterm n (e : expr) (σ σ' : state) :
  is_pure e = true -> pterm n (e, σ) = pterm n (e, σ').
Proof.
  intros.
  revert e H.
  induction n.
  {
    intros.
    rewrite /pterm /exec /to_final. simpl.
    destruct (to_val e) eqn: He; auto.
  }
  intros.
  destruct (to_val e) eqn: He. 
  { rewrite /pterm /exec /to_final. simpl. by rewrite He. }
  rewrite !pterm_rec; try assumption.
  rewrite /Expval.
  rewrite fubini_pos_seriesC_prod_rl.
  2: { admit. }
  2: { admit. }
  rewrite fubini_pos_seriesC_prod_rl.
  2: { admit. }
  2: { admit. }
  rewrite (SeriesC_ext 
    (λ b : language.state prob_lang, _) 
    (λ b, if bool_decide (b = σ) then SeriesC (λ a : language.expr prob_lang, step (e, σ) (a, b) * pterm n (a, b)) else 0)).
  2: {
    intros.
    case_bool_decide; auto.
    admit.
  }
  rewrite (SeriesC_ext 
    (λ b : language.state prob_lang, SeriesC _) 
    (λ b, if bool_decide (b = σ') then SeriesC (λ a : language.expr prob_lang, step (e, σ') (a, b) * pterm n (a, b)) else 0)).
  2: {
    intros.
    case_bool_decide; auto.
    admit.
  }
  rewrite !(SeriesC_singleton_dependent).
  apply SeriesC_ext.
  intros.
  rewrite IHn.
  { rewrite (pure_step _ n0 σ σ' H). auto. }


Admitted.
   
(* 
Lemma state_incl_head_reducible' (σ1 σ2 σ' : state) (e e' : expr):
  σ1.(tapes) ⊆ σ2.(tapes) -> σ1.(heap) ⊆ σ2.(heap) ->
  e' = state_incl_transform σ1 σ2 e' ->
    head_step e σ1 (e', σ') > 0 -> ∃ σ, head_step e σ2 (e', σ) > 0.
Proof. 
  intros.
  destruct e; inv_head_step;
  try (exists σ2; rewrite dret_1_1; auto; lra); 
  try (exfalso; by eapply (gmap_contras _ _ H));
  try (exists σ2; eapply dmap_pos; by eexists).
  - admit. (* exists (state_upd_heap_N (fresh_loc (heap σ2)) (Z.to_nat n) v0 σ2). *)
  - exists (state_upd_heap <[l0:=v0]> σ2). rewrite dret_1_1; auto; lra.
  - eexists. rewrite dret_1_1; auto; lra.
Admitted. *)

Lemma dmap_dzero_contra {A B : Type} `{Countable A} `{Countable B} {f: A -> B}: 
  (∃ (b : B), dmap f dzero b > 0) -> False.
Proof.
  rewrite dmap_dzero. intros.
  destruct H1. rewrite dzero_0 in H1. lra.
Qed.

(* Somewhat provable? *)
Lemma state_incl_reducible (σ1 σ2 : state) (e : expr):
  σ1.(tapes) ⊆ σ2.(tapes) -> σ1.(heap) ⊆ σ2.(heap) ->
    reducible (e, σ1) -> reducible (e, σ2).
Proof. 
  rewrite /reducible /step. simpl.
  rewrite /prim_step. simpl.
  intros.
  destruct H1 as [[e' σ'] H1].
  destruct (decomp e) eqn: Hde. 
  revert H1.
  rewrite Hde.
  simpl in *. 
  intros.
  apply dmap_pos in H1. 
  destruct H1 as [a [H1 H2]].
  assert (head_reducible e0 σ1). {
    rewrite /head_reducible. by exists a.
  }
  eapply state_incl_head_reducible in H3.
  2: apply H.
  2: apply H0.
  destruct H3.
  rewrite /fill_lift in H1. destruct a.
  inversion H1. subst s.
  subst e'.
  eexists (_, σ').
Admitted.

Lemma state_decomp_reducible (σ1 σ2 : state) : state_decomp σ1 ∗ state_interp σ2 ⊢ ⌜(tapes σ1 ⊆ tapes σ2) ∧ (heap σ1 ⊆ heap σ2) ∧∀ e, reducible (e, σ1) -> reducible (e, σ2)⌝.
Proof.
  iIntros "[[Hheape Htapese] [Hheapa Htapesa]]".
  iDestruct (ghost_map_lookup_big with "Hheapa Hheape") as "%H1".
  iDestruct (ghost_map_lookup_big with "Htapesa Htapese") as "%H2".
  iPureIntro.
  intros.
  split. {auto. }
  split. {auto. }
  intros.
  by apply (state_incl_reducible σ1).
Qed.

(* (* Very Likely Provable *)
Lemma state_update_step_pos' {e e' : expr} {σ σ' : state} :
  0 < step (e, σ) (e', σ') -> 
    state_interp σ ∗ state_decomp σ ==∗ state_interp σ' ∗ state_decomp σ'.
Proof.
  rewrite /step.
  simpl.
  rewrite /prim_step.
  simpl.
  intros.
  destruct (decomp e) eqn : Hde.
  rewrite Hde in H.
  destruct e0; inv_head_step; try (rewrite dmap_dzero dzero_0 in H; lra);
  try (rewrite dmap_dret /fill_lift in H; simpl in H; apply dret_pos in H; inversion H; 
  try (subst σ'; iIntros "[Ha Ht]"; iFrame; done));
  try (
    apply dmap_pos in H;
    destruct H as [[e1 σ1] [H1 H]];
    inversion H1; subst σ1;
    apply dmap_pos in H;
    destruct H as [nn [H H3]];
    inversion H; subst σ';
    iIntros "[Ha Ht]"; iFrame; done).
  - simpl. iIntros "[[Hh Ht] [Hdt Hdh]]". iFrame.
    iPoseProof (ghost_map_insert (fresh_loc (heap σ))) as "Hnew".
    { apply not_elem_of_dom_1, fresh_loc_is_fresh. }
    rewrite /heap_array.
  - simpl. iIntros "[[Hh Ht] [Hdt Hdh]]". iFrame.
    
  - simpl. iIntros "[[Hh Ht] [Hdt Hdh]]". iFrame.
    iMod (ghost_map_insert (fresh_loc (tapes σ)) with "Ht") as "[Ht Hnewdt]".
    { apply not_elem_of_dom_1, fresh_loc_is_fresh. }
    iSplitL "Ht"; iFrame; auto.
    iPoseProof (big_opM_fn_insert (fun l a _ => l ↪[erisGS_tapes_name] a)%I _ (tapes σ) with "[Hnewdt Hdh]") as "H".
    { apply not_elem_of_dom_1, fresh_loc_is_fresh. }
    { iFrame. }
    by iFrame.
  

    (* iPoseProof (big_sepM_fn_insert' with "Hdh") as "H". *)
  - simpl. iIntros "[[Hh Ht] [Hdt Hdh]]". iFrame. 
Admitted.
 *)

Print lim_exec.

Lemma state_interp_agree (σ1 σ2 : state) : 
  state_interp σ1 -∗ state_interp σ2 -∗  ⌜σ1 = σ2⌝.
Proof.
  destruct σ1, σ2.
  iIntros "[Hh1 Ht1] [Hh2 Ht2]".
  simpl.
  iPoseProof (ghost_map_auth_agree with "Ht1 Ht2") as "%H1".
  iPoseProof (ghost_map_auth_agree with "Hh1 Hh2") as "%H2".
  iPureIntro.
  subst. auto.
Qed.


(* Lemma AST_complete_pre' (n: nat) (e : expr) (σ : state): 
  state_decomp σ ∗ state_interp σ ∗ ↯ (pterm_comp n (e, σ)) -∗ WP e [{ v, True }].
Proof.
  iInduction n as [|n] "IH" forall (e σ).
  - destruct ( language.to_val e) eqn: He.
    { iIntros. apply of_to_val in He as <-. by wp_pures. }
    iIntros "[Hsd [Hse Herr]]". 
    rewrite /pterm_comp /pterm. simpl. rewrite He dzero_mass. 
    rewrite Rminus_0_r. iPoseProof (ec_contradict with "Herr") as "H"; 
    auto; try lra.
  - destruct ( language.to_val e) eqn: He.
    { iIntros. apply of_to_val in He as <-. by wp_pures. }
    iIntros "[Hsd [Hse Herr]]". 
    iApply twp_lift_step_fupd_glm; auto.
    iIntros "%% [Hs Herra]". 
    iPoseProof (state_interp_agree with "Hs Hse") as "%Hst".
    subst σ1.
    iClear "Hse".
    iDestruct (ec_supply_ec_inv with "Herra Herr") as %(ε1' & ε3 & Hε_now & Hε1').
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "hclose".
    iApply glm_adv_comp. 
    iExists (fun s => 0 < step (e, σ) s), 0%NNR, (fun x => (ε3 + (pterm_comp n x))%NNR).
    destruct (Rlt_dec 0 (pterm (S n) (e, σ))).
    2 : {
      iExFalso.
      iApply (ec_contradict with "Herr").
      rewrite /pterm_comp. simpl. lra. 
    }
    iSplitR.
    {
      iPureIntro.
      by eapply pterm_reducible.
    }
    iSplitR.
    {
      unfold state_interp. simpl. unfold heap_auth.
      Print erisGS_heap_name.
      iPureIntro.
      exists (ε3 + 1).
      intros. simpl.
      apply Rplus_le_compat_l.
      apply Rminus_le_0_compat.
      apply pmf_SeriesC_ge_0.
    }
    iSplitR.
    {
      admit.
    }
    iSplitR.
    {
      admit.
    }
    iIntros.
    iMod ((state_update_step_pos' H) with "[Hs Hsd]") as "[Hs1 Hs2]". {iFrame. }

    iMod (ec_supply_decrease with "Herra Herr") as (????) "Herra".
    iModIntro.
    destruct (Rlt_decision (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply exec_stutter_spend.
      iPureIntro.
      simpl.
      simpl in Hdec. lra.
    }
    iApply exec_stutter_free.
    replace (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R with (nonneg (ε3 + (pterm_comp n (e2, σ2)))%NNR); [|by simpl].
    iMod (ec_supply_increase ε3 (pterm_comp n (e2, σ2)) with "[Herra]") as "[Herra Herr]"; try lra.
    { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
    iMod "hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros.
    iFrame.
    iApply "IH". iFrame.
Admitted. *)

Print pgl.
Search (erisWpGS).

Lemma AST_complete_pure_pre (n: nat) (e : expr) (σ : state) E : 
  is_pure e = true -> 
  ↯ (pterm_comp n (e, σ)) -∗ WP e @ E [{ v, True }].
Proof. 
  intros.
  iInduction n as [|n] "IH" forall (e H σ).
  - destruct ( language.to_val e) eqn: He.
    { iIntros. apply of_to_val in He as <-. by wp_pures. }
    iIntros "Herr". 
    rewrite /pterm_comp /pterm. simpl. rewrite He dzero_mass. 
    rewrite Rminus_0_r. iPoseProof (ec_contradict with "Herr") as "H"; 
    auto; try lra.
  - destruct ( language.to_val e) eqn: He.
    { iIntros. apply of_to_val in He as <-. by wp_pures. }
    iIntros "Herr".
    iApply twp_lift_step_fupd_glm; auto.
    iIntros "%% [Hs Herra]". 
    iDestruct (ec_supply_ec_inv with "Herra Herr") as %(ε1' & ε3 & Hε_now & Hε1').
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "hclose".
    iApply glm_adv_comp. 
    iExists (fun s => step (e, σ1) s > 0), 0%NNR, (fun x => (ε3 + (pterm_comp n x))%NNR).
    destruct (Rlt_dec 0 (pterm (S n) (e, σ))).
    2 : {
      iExFalso.
      iApply (ec_contradict with "Herr").
      rewrite /pterm_comp. simpl. lra. 
    }
    iSplitR.
    { iPureIntro. apply (pterm_reducible (S n)); auto. rewrite (pure_pterm _ _ σ1 σ); auto. }
    iSplitR.
    { admit. }
    iSplitR.
    { admit. }
    iSplitR.
    { admit. }
    iIntros. 
    iMod (ec_supply_decrease with "Herra Herr") as (????) "Herra".
    iModIntro.
    destruct (Rlt_decision (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply exec_stutter_spend.
      iPureIntro.
      simpl.
      simpl in Hdec. lra.
    }
    iApply exec_stutter_free.
    replace (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R with (nonneg (ε3 + (pterm_comp n (e2, σ2)))%NNR); [|by simpl].
    iMod (ec_supply_increase ε3 (pterm_comp n (e2, σ2)) with "[Herra]") as "[Herra Herr]"; try lra.
    { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
    simpl in H0. 
    apply (pure_state_step) in H0 as H'0; auto.
    subst σ2.
    iFrame.
    iMod "hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros.
    iApply "IH"; iFrame.
    { iPureIntro. admit. }
Admitted.


Lemma AST_complete_pre (n: nat) (e : expr) (σ : state) E : 
  state_decomp σ ∗ ↯ (pterm_comp n (e, σ)) -∗ WP e @ E [{ v, True }].
Proof. 
  iInduction n as [|n] "IH" forall (e σ).
  - destruct ( language.to_val e) eqn: He.
    { iIntros. apply of_to_val in He as <-. by wp_pures. }
    iIntros "[Hse Herr]". 
    rewrite /pterm_comp /pterm. simpl. rewrite He dzero_mass. 
    rewrite Rminus_0_r. iPoseProof (ec_contradict with "Herr") as "H"; 
    auto; try lra.
  - destruct ( language.to_val e) eqn: He.
    { iIntros. apply of_to_val in He as <-. by wp_pures. }
    iIntros "[Hse Herr]". 
    iApply twp_lift_step_fupd_glm; auto.
    iIntros "%% [Hs Herra]". 
    iDestruct (ec_supply_ec_inv with "Herra Herr") as %(ε1' & ε3 & Hε_now & Hε1').
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros "hclose".
    iApply glm_adv_comp. 
    iExists (fun s => 0 < step (e, σ1) s), 0%NNR, (fun x => (ε3 + (pterm_comp n x))%NNR).
    iDestruct (state_decomp_reducible with "[Hse Hs]") as "%Hr"; iFrame.
    destruct Hr as [Hss1 [Hss2 Hred]].
    destruct (Rlt_dec 0 (pterm (S n) (e, σ))).
    2 : {
      iExFalso.
      iApply (ec_contradict with "Herr").
      rewrite /pterm_comp. simpl. lra. 
    }
    iSplitR.
    { 
      iPureIntro. 
      by eapply Hred, pterm_reducible. 
    }
    iSplitR.
    { 
      admit.
    }
    iSplitR.
    {
      iPureIntro.
      simpl. rewrite Rplus_0_l. 
      rewrite (SeriesC_ext _ (λ r, (λ a, (prim_step e σ1 a) * (ε3 + 1)) r + (-1) * (λ a,  (prim_step e σ1 a) * (pterm n a)) r)).
      2: {
        intros.
        field_simplify. real_solver.
      }
      rewrite (SeriesC_plus).
      2 : {
        apply ex_seriesC_scal_r. apply pmf_ex_seriesC.
      }
      2 : {
        apply ex_seriesC_scal_l.
        apply pmf_ex_seriesC_mult_fn. 
        exists 1. intros. split.
        - apply pmf_SeriesC_ge_0.
        - apply pmf_SeriesC.
      }
      rewrite Hε_now. replace (nonneg (ε1' + ε3)%NNR) with (nonneg ε1' + ε3); auto.
      rewrite Hε1'.
      rewrite /pterm_comp. simpl. 
      rewrite SeriesC_scal_l SeriesC_scal_r.
      rewrite pterm_rec /Expval; auto.
      rewrite /step. simpl. field_simplify.
      rewrite <- Rplus_minus_swap. 
      rewrite !Rminus_def.
      apply Rplus_le_compat.
      {
        apply Rplus_le_compat.
        - simpl. rewrite <- Rmult_1_l.
          apply Rmult_le_compat_r; auto.
        - apply pmf_SeriesC.
      }
      apply Ropp_le_contravar.
      epose proof (pterm_rec n (e ,σ) _). rewrite /Expval in H.
      simpl in H. rewrite <- H.
      epose proof (pterm_rec n (e ,σ1) _). rewrite /Expval in H0.
      simpl in H0. trans (pterm (S n) (e, σ1)).
      - apply state_incl_pterm_le; auto.
      - rewrite H0. apply Req_le_sym. apply SeriesC_ext. intros. auto.
    }
    iSplitR.
    {
      iPureIntro.
      rewrite /pgl. simpl.
      admit.
    }
    iIntros. 
    (* iMod ((state_update_step_pos H) with "[Hs Hse]") as "[Hs Hse]".
    { iFrame. } *)
    iMod (ec_supply_decrease with "Herra Herr") as (????) "Herra".
    iModIntro.
    destruct (Rlt_decision (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R 1%R) as [Hdec|Hdec]; last first.
    { apply Rnot_lt_ge, Rge_le in Hdec.
      iApply exec_stutter_spend.
      iPureIntro.
      simpl.
      simpl in Hdec. lra.
    }
    iApply exec_stutter_free.
    replace (nonneg ε3 + nonneg (pterm_comp n (e2, σ2)))%R with (nonneg (ε3 + (pterm_comp n (e2, σ2)))%NNR); [|by simpl].
    iMod (ec_supply_increase ε3 (pterm_comp n (e2, σ2)) with "[Herra]") as "[Herra Herr]"; try lra.
    { iApply ec_supply_eq; [|done]. simplify_eq. lra. }
    iMod "hclose".
    iApply fupd_mask_intro.
    { set_solver. }
    iIntros.
    iSplitR "Herra Herr Hse";
    iFrame. iApply "IH". iFrame. 
    (* admit. iApply "IH". *)
Admitted.

(* 
Lemma AST_complete (e : expr) ε (m : nat) E : 
  almost_surely_terminates (e, σ₀) ->
  0 < ε -> 
  ↯ ε -∗ WP e @ E [{ v, True }].
Proof.
  iIntros "%% Herr".
  assert (0 <= ε). { lra. }
  destruct ( language.to_val e) eqn: He.
  { auto. apply of_to_val in He. rewrite <- He. wp_pures. auto. }
  destruct (Rlt_le_dec ε 1).
  2 : {
    set er := mknonnegreal ε H1.
    wp_apply (twp_ec_spend _ _ _ er); simpl; auto; try lra. 
  } 
  specialize (AST_pt_lim (e, σ₀) (1 - ε) H) as []. {lra. }
  assert (1 - pterm x (e, σ₀) < ε). { lra. }
  (* iPoseProof ((ec_weaken _ (1 - pterm x (e, σ₀))) with "Herr") as "Herr".
  - pose proof (pmf_SeriesC (exec x (e, σ₀))). 
    split; try lra. 
    rewrite /pterm. simpl. 
  - iApply ec_ast_amplify_pre; auto. *)
  
Admitted. *)
Print state.
Check ().



Import uPred.

Search (_ ==∗ _).

Lemma AST_complete (e : expr) ε (m : nat) : 
  almost_surely_terminates (e, σ₀) ->
  0 < ε -> 
  ↯ ε -∗ WP e [{ v, True }].
Proof.
  iIntros "%% Herr".
  Print HeapG.
  assert (0 <= ε). { lra. }
  apply (AST_pt_lim _ (1-ε)) in H as [n H']; auto; try lra.
  iPoseProof ((ec_weaken ε (1 - pterm n (e, σ₀))) with "[Herr]") as "Herr"; try iFrame.
  - pose proof (pmf_SeriesC (exec n (e, σ₀))).
    split; try lra. apply pterm_le1.
  - (* set (HclutchGS := HeapG Σ _ _ _ γH γT _).
    iApply (AST_complete_pre'). iFrame.  *)
Admitted.

End Complete.


 *)