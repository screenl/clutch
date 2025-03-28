From clutch.coneris Require Import coneris.

Set Default Proof Using "Type*".

(*
   A concurrent interface for hash functions with presampling
   for individual keys
 *)




Class con_hash4 `{!conerisGS Σ} (val_size max_key : nat ):= Con_Hash4
{
  (** * Operations *)
  init_hash4 : val;
  compute_hash4 : val;
  (** * Ghost state *)

  (** [name] is used to associate [locked] with [is_lock] *)
  (* tape_name: Type; *)

  hash_view_gname:Type;
  hash_lock_gname:Type;

  (** * Predicates *)
  con_hash_inv4 (N:namespace) (f l hm: val) (R:gmap nat nat -> iProp Σ) {HR: ∀ m, Timeless (R m )} (γ1:hash_view_gname) (γ_lock:hash_lock_gname): iProp Σ;
  hash_auth4 (m:gmap nat nat) (γ:hash_view_gname) : iProp Σ;
  hash_frag4 (k v : nat) (γ:hash_view_gname) : iProp Σ;

  (** * General properties of the predicates *)
  (* #[global] concrete_seq_hash_timeless {L : seq_hashG Σ} f m :: *)
  (*   Timeless (concrete_seq_hash (L:=L) f m); *)
  #[global] hash_auth_timeless m γ ::
    Timeless (hash_auth4 m γ );
  #[global] hash_frag_timeless v res γ ::
    Timeless (hash_frag4 v res γ );
  #[global] con_hash_inv_persistent N f l hm γ1 R {HR: ∀ m, Timeless (R m )}  γ_lock ::
    Persistent (con_hash_inv4 N f l hm R γ1 γ_lock);
  #[global] hash_frag_persistent k v γ ::
    Persistent (hash_frag4 k v γ );
  hash_auth_exclusive m m' γ :
    hash_auth4 m γ  -∗ hash_auth4 m' γ  -∗ False;
  hash_auth_frag_agree m k v γ :
    hash_auth4 m γ  -∗ hash_frag4 k v γ  -∗ ⌜m!!k=Some v⌝;
  hash_auth_duplicate m k v γ :
    m!!k=Some v -> hash_auth4 m γ  -∗ hash_frag4 k v γ ;
  hash_frag_frag_agree k v1 v2 γ :
    hash_frag4 k v1 γ  -∗ hash_frag4 k v2 γ  -∗ ⌜v1=v2⌝;
  hash_frag_valid k v γ :
    hash_frag4 k v γ -∗ ⌜ (v ≤ val_size)%nat ⌝;


  hash_preview4 N k f l hm R {HR: ∀ m, Timeless (R m )}  m γ_hv γ_lock (bad : gset nat)(ε εI εO:nonnegreal) E:
  ↑(N) ⊆ E ->
  (forall x : nat, x ∈ bad -> (x < S val_size)%nat) ->
  (εI * (size bad) + εO * (val_size + 1 - size bad) <= ε * (val_size + 1))%R ->
  hash_auth4 m γ_hv -∗
  con_hash_inv4 N f l hm R γ_hv γ_lock -∗
  ⌜ m !! k = None ⌝ -∗
  ↯ ε -∗
    state_update E E (∃ (n:fin(S val_size)),
          ( (⌜fin_to_nat n ∈ bad⌝) ∗ ↯ εI  ∨
            (⌜fin_to_nat n ∉ bad⌝) ∗ ↯ εO
          )∗
          hash_auth4 (<[k:=fin_to_nat n]> m) γ_hv);


  con_hash_init4 N R {HR: ∀ m, Timeless (R m)} :
    {{{ R ∅ }}}
      init_hash4 #()
      {{{ (f:val), RET f; ∃ l hm γ1 γ_lock, con_hash_inv4 N f l hm R γ1 γ_lock ∗
                                                  hash_auth4 ∅ γ1
      }}} ;


  con_hash_spec4 N f l hm R {HR: ∀ m, Timeless (R m)} γ1 γ_lock (k:nat) v:
  {{{ con_hash_inv4 N f l hm R γ1 γ_lock ∗
       hash_frag4 k v γ1
  }}}
      f #k
      {{{ (res:nat), RET (#res);  ⌜ res = v ⌝
      }}}

}.


Section derived_lemmas.
  Context `{conerisGS Σ, !con_hash4 val_size max_key}.

  Lemma wp_hash_lookup_safe N k f l hm m R {HR: ∀ m, Timeless (R m )} γhv γlock :
    (k ≤ max_key)%nat ->
    {{{ hash_auth4 m γhv ∗ con_hash_inv4 N f l hm R γhv γlock }}}
        f #k
    {{{ (v : nat), RET #v; ⌜ (v ≤ val_size)%nat ⌝ ∗ hash_auth4 (<[k:=v]> m) γhv }}}.
  Proof.
    iIntros (Hk Φ) "(Hhauth & #Hinv) HΦ".
    destruct (m !! k) as [v|] eqn:Hlookup.
    - iPoseProof (hash_auth_duplicate m k v with "Hhauth") as "#Hfrag"; auto.
      wp_apply con_hash_spec4; auto.
      iPoseProof (hash_frag_valid with "Hfrag") as "%".
      iIntros (?) "->".
      iApply "HΦ".
      iSplit; auto.
      by rewrite insert_id.
    - iMod (ec_zero) as "Herr".
      iApply state_update_pgl_wp.
      iMod (hash_preview4 N _  _ _ _ _ _ _ _ ∅ nnreal_zero nnreal_zero nnreal_zero with "Hhauth [] [] [Herr]")
        as "(%v & _ & Hhauth)"; auto.
      + set_solver.
      + rewrite size_empty /=.
        lra.
      + iModIntro.
        iPoseProof (hash_auth_duplicate _ k v with "Hhauth") as "#Hfrag"; auto.
        {
          rewrite lookup_insert //.
        }
        wp_apply con_hash_spec4; auto.
        iPoseProof (hash_frag_valid with "Hfrag") as "%".
        iIntros (?) "->".
        iApply "HΦ".
        iSplit; auto.
   Qed.

  Lemma wp_hash_lookup_avoid_set N k f l hm m R {HR: ∀ m, Timeless (R m )} γhv γlock (bad : gset nat)(ε εI εO:nonnegreal) :
    (forall x : nat, x ∈ bad -> (x < S val_size)%nat) ->
    (εI * (size bad) + εO * (val_size + 1 - size bad) <= ε * (val_size + 1))%R ->
    (k ≤ max_key)%nat ->
    m !! k = None ->
    {{{ ↯ ε ∗ hash_auth4 m γhv ∗ con_hash_inv4 N f l hm R γhv γlock }}}
      f #k
      {{{ (v : nat), RET #v; ⌜ (v ≤ val_size)%nat ⌝ ∗
                             ((⌜v ∈ bad⌝) ∗ ↯ εI  ∨
                                (⌜v ∉ bad⌝) ∗ ↯ εO) ∗
                             hash_auth4 (<[k:=v]> m) γhv }}}.
  Proof.
    iIntros (Hbad Hdistr Hk Hnone Φ) "(Herr & Hhauth & #Hinv) HΦ".
    iApply state_update_pgl_wp.
    iMod (hash_preview4 N _  _ _ _ _ _ _ _ bad ε εI εO with "Hhauth [] [] [Herr]")
      as "(%v & Hv & Hhauth)"; auto.
    iModIntro.
    iPoseProof (hash_auth_duplicate _ k v with "Hhauth") as "#Hfrag"; auto.
    {
      rewrite lookup_insert //.
    }
    wp_apply con_hash_spec4; auto.
    iPoseProof (hash_frag_valid with "Hfrag") as "%".
    iIntros (?) "->".
    iApply "HΦ".
    iSplit; auto.
    by iFrame.
  Qed.

End derived_lemmas.

