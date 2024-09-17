From clutch.coneris Require Import coneris.
From clutch.coneris Require Import flip hocap.

Set Default Proof Using "Type*".

Class flip_spec `{!conerisGS Σ} := FlipSpec
{
  (** * Operations *)
  allocate_tape : val;
  flip_tape : val;
  (** * Ghost state *)
  (** The assumptions about [Σ] *)
  flipG : gFunctors → Type;
  (** [name] is used to associate [locked] with [is_lock] *)
  error_name : Type;
  tape_name: Type;
  (** * Predicates *)
  is_flip {L : flipG Σ} (N:namespace) 
    (γ1: error_name) (γ2: tape_name): iProp Σ;
  flip_error_auth {L : flipG Σ} (γ: error_name) (x:R): iProp Σ;
  flip_error_frag {L : flipG Σ} (γ: error_name) (x:R): iProp Σ;
  flip_tapes_auth {L : flipG Σ} (γ: tape_name) (m:gmap loc (list bool)): iProp Σ;
  flip_tapes_frag {L : flipG Σ} (γ: tape_name) (α:loc) (ns:list bool): iProp Σ;
  (** * General properties of the predicates *)
  #[global] is_flip_persistent {L : flipG Σ} N γ1 γ2 ::
    Persistent (is_flip (L:=L) N γ1 γ2);
  #[global] flip_error_auth_timeless {L : flipG Σ} γ x ::
    Timeless (flip_error_auth (L:=L) γ x);
  #[global] flip_error_frag_timeless {L : flipG Σ} γ x ::
    Timeless (flip_error_frag (L:=L) γ x);
  #[global] flip_tapes_auth_timeless {L : flipG Σ} γ m ::
    Timeless (flip_tapes_auth (L:=L) γ m);
  #[global] flip_tapes_frag_timeless {L : flipG Σ} γ α ns ::
    Timeless (flip_tapes_frag (L:=L) γ α ns);

  flip_error_auth_exclusive {L : flipG Σ} γ x1 x2:
    flip_error_auth (L:=L) γ x1 -∗ flip_error_auth (L:=L) γ x2 -∗ False;
  flip_error_frag_exclusive {L : flipG Σ} γ x1 x2:
  flip_error_frag (L:=L) γ x1 -∗ flip_error_frag (L:=L) γ x2 -∗ False;
  flip_error_auth_pos {L : flipG Σ} γ x:
    flip_error_auth (L:=L) γ x -∗ ⌜(0<=x)%R⌝;
  flip_error_auth_frag {L : flipG Σ} γ x:
    flip_error_frag (L:=L) γ x -∗ ⌜(0<=x)%R⌝;
  flip_error_agree {L : flipG Σ} γ x1 x2:
    flip_error_auth (L:=L) γ x1 -∗ flip_error_frag (L:=L) γ x2 -∗ ⌜x1 = x2 ⌝;
  flip_error_update {L : flipG Σ} γ x1 x2 (x3:nonnegreal):
    flip_error_auth (L:=L) γ x1 -∗ flip_error_frag (L:=L) γ x2 ==∗
    flip_error_auth (L:=L) γ x3 ∗ flip_error_frag (L:=L) γ x3;

  flip_tapes_auth_exclusive {L : flipG Σ} γ m m':
  flip_tapes_auth (L:=L) γ m -∗ flip_tapes_auth (L:=L) γ m' -∗ False;
  flip_tapes_frag_exclusive {L : flipG Σ} γ α ns ns':
  flip_tapes_frag (L:=L) γ α ns -∗ flip_tapes_frag (L:=L) γ α ns' -∗ False;
  flip_tapes_agree {L : flipG Σ} γ α m ns:
    flip_tapes_auth (L:=L) γ m -∗ flip_tapes_frag (L:=L) γ α ns -∗ ⌜ m!! α = Some (ns) ⌝;
  flip_tapes_update {L : flipG Σ} γ α m ns n:
    flip_tapes_auth (L:=L) γ m -∗ flip_tapes_frag (L:=L) γ α ns ==∗
    flip_tapes_auth (L:=L) γ (<[α := (ns ++[n])]> m) ∗ flip_tapes_frag (L:=L) γ α (ns ++ [n]);

  (** * Program specs *)
  flip_inv_create_spec {L : flipG Σ} N E ε:
  ↯ ε -∗
  wp_update E (∃ γ1 γ2, is_flip (L:=L) N γ1 γ2 ∗
                        flip_error_frag (L:=L) γ1 ε);
  
  flip_allocate_tape_spec {L: flipG Σ} N E γ1 γ2:
    ↑N ⊆ E->
    {{{ is_flip (L:=L) N γ1 γ2 }}}
      allocate_tape #() @ E
      {{{ (v:val), RET v;
          ∃ (α:loc), ⌜v=#lbl:α⌝ ∗ flip_tapes_frag (L:=L) γ2 α []
      }}};
  flip_tape_spec_some {L: flipG Σ} N E γ1 γ2 (P: iProp Σ) (Q:iProp Σ) (α:loc) (n:bool) ns:
    ↑N⊆E -> 
    {{{ is_flip (L:=L) N γ1 γ2 ∗
        □ (P ={E∖↑N}=∗ Q) ∗
        P ∗ flip_tapes_frag (L:=L) γ2 α (n::ns)
    }}}
      flip_tape #lbl:α @ E
                       {{{ RET #n; Q ∗ flip_tapes_frag (L:=L) γ2 α ns}}};
  flip_presample_spec {L: flipG Σ} NS E ns α
     (ε2 : R -> bool -> R)
    (P : iProp Σ) T γ1 γ2:
    ↑NS ⊆ E ->
    (∀ ε n, 0<= ε -> 0<=ε2 ε n)%R ->
    (∀ (ε:R), 0<= ε -> (ε2 ε true + ε2 ε false)/2 <= ε)%R->
    is_flip (L:=L) NS γ1 γ2 -∗
    (□∀ (ε:R) n, (P ∗ flip_error_auth (L:=L) γ1 ε) ={E∖↑NS}=∗
        (⌜(1<=ε2 ε n)%R⌝ ∨ (flip_error_auth (L:=L) γ1 (ε2 ε n)  ∗ T (n)))) 
        -∗
    P -∗ flip_tapes_frag (L:=L) γ2 α ns-∗
        wp_update E (∃ n, T (n) ∗ flip_tapes_frag (L:=L) γ2 α (ns++[n]))
}.


Section lemmas.
  Context `{rc:flip_spec} {L: flipG Σ}.
  
  Lemma flip_tape_spec_none  N E γ1 γ2 (ε2:R -> bool -> R) (P: iProp Σ) (T: bool -> iProp Σ) (Q: bool -> iProp Σ)(α:loc):
    ↑N ⊆ E->
    (∀ ε n, 0<= ε -> 0<= ε2 ε n)%R->
    (∀ (ε:R), 0<=ε -> ((ε2 ε true) + (ε2 ε false))/2 <= ε)%R →
    {{{ is_flip (L:=L) N γ1 γ2 ∗
        □(∀ (ε:R) (n : bool), P ∗ flip_error_auth (L:=L) γ1 ε
                           ={E∖↑N}=∗ (⌜(1<=ε2 ε n)%R⌝∨ flip_error_auth (L:=L) γ1 (ε2 ε n) ∗ T n) ) ∗
        □ (∀ (n:bool), T n  ={E∖↑N}=∗ Q n) ∗
        P ∗ flip_tapes_frag (L:=L) γ2 α []
    }}}
      flip_tape #lbl:α @ E
                                 {{{ (b:bool), RET #b; Q b ∗ flip_tapes_frag (L:=L) γ2 α [] }}}.
  Proof.
    iIntros (Hsubset Hpos Hineq Φ) "(#Hinv & #Hvs1 & #Hvs2 & HP & Hα) HΦ".
    iMod (flip_presample_spec with "[//][//][$][$]") as "(%&HT&Hα)"; [done..|].
    iApply (flip_tape_spec_some _ _ _ _ (T n) with "[$Hα $HT]"); try done.
    { by iSplit. }
    by iNext.
  Qed.
  
End lemmas.


(** Instantiate flip *)
Class flipG1 Σ := FlipG1 { flipG1_error::hocap_errorGS Σ;
                                    flipG1_tapes:: hocap_tapesGS Σ;
                    }.
Local Definition flip_inv_pred1 `{!conerisGS Σ, !hocap_errorGS Σ, !hocap_tapesGS Σ} γ1 γ2:=
    (∃ (ε:R) (m:gmap loc (nat * list nat)) ,
        ↯ ε ∗ ●↯ ε @ γ1 ∗
        ([∗ map] α ↦ t ∈ m, α ↪N ( t.1 ; t.2 )) ∗ ●m@γ2 
    )%I.

#[local] Program Definition flip_spec1 `{!conerisGS Σ}: flip_spec :=
  {| allocate_tape:= (λ: <>, allocB);
     flip_tape:= flipL;
     flipG := flipG1;
    error_name := gname;
    tape_name := gname;
    is_flip _ N γ1 γ2 := inv N (flip_inv_pred1 γ1 γ2);
    flip_error_auth _ γ x := ●↯ x @ γ;
    flip_error_frag _ γ x := ◯↯ x @ γ;
    flip_tapes_auth _ γ m := (●((λ ns, (1, bool_to_nat<$>ns))<$>m)@γ)%I;
    flip_tapes_frag _ γ α ns := (α◯↪N (1%nat;bool_to_nat<$> ns) @ γ)%I;
  |}.

Next Obligation.
  simpl.
  iIntros (??????) "(%&<-&H1)(%&<-&H2)".
  iCombine "H1 H2" gives "%H". by rewrite excl_auth.excl_auth_auth_op_valid in H.
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "(%&<-&H1)(%&<-&H2)".
  iCombine "H1 H2" gives "%H". by rewrite excl_auth.excl_auth_frag_op_valid in H.
Qed.
Next Obligation.
  simpl.
  iIntros (?????) "H".
  iApply (hocap_error_auth_pos with "[$]").
Qed.
Next Obligation.
  simpl.
  iIntros (?????) "H".
  iApply (hocap_error_frag_pos with "[$]").
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "H1 H2".
  iApply (hocap_error_agree with "[$][$]").
Qed.
Next Obligation.
  simpl. iIntros (???????) "??".
  iApply (hocap_error_update with "[$][$]").
Qed.
Next Obligation.
  simpl.
  iIntros (??????) "H1 H2".
  by iDestruct (ghost_map_auth_valid_2 with "[$][$]") as "[%H _]".
Qed.
Next Obligation.
  simpl. 
  iIntros (???????) "H1 H2".
  iDestruct (ghost_map_elem_frac_ne with "[$][$]") as "%"; last done.
  rewrite dfrac_op_own dfrac_valid_own. by intro.
Qed.
Next Obligation.
  simpl.
  iIntros.
  iDestruct (hocap_tapes_agree with "[$][$]") as "%H".
  iPureIntro.
  rewrite lookup_fmap_Some in H. destruct H as (?&?&K).
  simplify_eq.
  rewrite K.
  f_equal.
  eapply fmap_inj; last done.
  intros [][]?; by simplify_eq.
Qed.
Next Obligation.
  iIntros.
  iMod (hocap_tapes_presample with "[$][$]") as "[??]".
  iModIntro. iFrame.
  rewrite fmap_insert.
  rewrite fmap_app; iFrame.
Qed.
Next Obligation.
  simpl.
  iIntros (????? ε) "H1".
  iApply fupd_wp_update.
  iApply wp_update_ret.
  iDestruct (ec_valid with "[$]") as "%".
  unshelve iMod (hocap_error_alloc (mknonnegreal ε _)) as "(%γ1 & H2 & H3)"; first naive_solver.
  simpl.
  iMod (hocap_tapes_alloc ∅) as "(%γ2 & H4 & H5)".
  iMod (inv_alloc _ _ (flip_inv_pred1 γ1 γ2) with "[H1 H2 H4]").
  { iFrame. by iNext. }
  by iFrame.
Qed.
Next Obligation.
  Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
