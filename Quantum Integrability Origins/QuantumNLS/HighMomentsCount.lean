import Mathlib

/-!
# PROP-008 `lem:B4-high-moments`, stage B (combinatorial core): no isolated vertex
(source/chapters/propagation/spectral_calculus.tex:24-60, the cluster/forest argument)

Pure counting, no Hilbert space.  For `m` independent uniform subsets `S_j ⊆ Fin N` of prescribed sizes `r_j`
(the tuples `S ∈ piFinset (fun j => powersetCard (r j) univ)`), call `S` *isolated-free* if every `j` has an
`i ≠ j` with `S_j ∩ S_i ≠ ∅`.  `card_noiso_le` proves, for `m = 2p`, `N ≥ 1`, `1 ≤ r_j ≤ N`:
`#{S isolated-free} ≤ (∏_j C(N,r_j)) · m^m · (∏_j r_j)^{2m} / N^p`.

Route (own design, avoiding spectral measures/forests): for an isolated-free `S` let `f(j)` be the least `i ≠ j`
meeting `S_j`; then `f j ≠ j` and `f (f j) ≤ j` (`exists_f`).  For a fixed such `f`, leaf removal: if some
`j ∈ R` has no `f`-preimage in `R` its constraint involves a coordinate nothing else uses and costs a factor
`r_j r_{f j} / N` (`card_split`, `card_meeting_mul_le`); otherwise `f` is a bijection of `R` with `f ∘ f ≤ id`,
hence an involution, and removing a pair `{j, f j}` costs one such factor (`count_aux`).  Each step removes at
most two vertices per factor, so `≥ m/2` factors.
-/

set_option autoImplicit false
open Finset

namespace QuantumNLS.HighMomentsCount

section Meet
variable {N : ℕ}

theorem card_filter_mem (r : ℕ) (hr : 1 ≤ r) (x : Fin N) :
    ((powersetCard r (univ : Finset (Fin N))).filter (fun s => x ∈ s)).card =
      (N - 1).choose (r - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have e : (powersetCard (k + 1) (univ : Finset (Fin N))).filter (fun s => x ∈ s) =
      (powersetCard k ((univ : Finset (Fin N)).erase x)).image (insert x) := by
    ext s
    simp only [mem_filter, mem_powersetCard, mem_image, subset_univ, true_and]
    constructor
    · rintro ⟨hs, hx⟩
      refine ⟨s.erase x, ⟨?_, ?_⟩, insert_erase hx⟩
      · intro y hy
        rw [mem_erase] at hy ⊢
        exact ⟨hy.1, mem_univ _⟩
      · rw [card_erase_of_mem hx, hs]; rfl
    · rintro ⟨t, ⟨ht, htc⟩, rfl⟩
      have hxt : x ∉ t := fun h => by have := ht h; simp at this
      exact ⟨by rw [card_insert_of_notMem hxt, htc], mem_insert_self _ _⟩
  rw [e, card_image_of_injOn, card_powersetCard, card_erase_of_mem (mem_univ x), card_univ,
    Fintype.card_fin]
  · simp
  · intro t ht t' ht' h
    have hxt : x ∉ t := by
      have := (mem_powersetCard.mp (Finset.mem_coe.mp ht)).1 
      intro hx; have := this hx; simp at this
    have hxt' : x ∉ t' := by
      have := (mem_powersetCard.mp (Finset.mem_coe.mp ht')).1
      intro hx; have := this hx; simp at this
    rw [← erase_insert hxt, ← erase_insert hxt']
    exact congrArg (fun z => z.erase x) h

theorem card_meeting_mul_le (r : ℕ) (T0 : Finset (Fin N)) :
    ((powersetCard r (univ : Finset (Fin N))).filter (fun s => (s ∩ T0).Nonempty)).card * N ≤
      r * T0.card * N.choose r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : (powersetCard 0 (univ : Finset (Fin N))).filter (fun s => (s ∩ T0).Nonempty) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro s hs
      have : s = ∅ := by simpa using hs
      simp [this]
    simp [this]
  rcases T0.eq_empty_or_nonempty with rfl | ⟨x0, hx0⟩
  · have : (powersetCard r (univ : Finset (Fin N))).filter (fun s => (s ∩ ∅).Nonempty) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro s _; simp
    simp [this]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := x0.2; omega⟩
  have hsub : (powersetCard r (univ : Finset (Fin (n + 1)))).filter (fun s => (s ∩ T0).Nonempty) ⊆
      T0.biUnion (fun x => (powersetCard r (univ : Finset (Fin (n + 1)))).filter (fun s => x ∈ s)) := by
    intro s hs
    rw [mem_filter] at hs
    obtain ⟨hs1, y, hy⟩ := hs
    rw [mem_inter] at hy
    exact mem_biUnion.mpr ⟨y, hy.2, mem_filter.mpr ⟨hs1, hy.1⟩⟩
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∑ x ∈ T0, ((powersetCard r (univ : Finset (Fin (n + 1)))).filter (fun s => x ∈ s)).card =
      T0.card * n.choose (r - 1) := by
    rw [Finset.sum_congr rfl (fun x _ => card_filter_mem r hr x)]
    simp
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  have h3 := Nat.add_one_mul_choose_eq n k
  calc _ ≤ (T0.card * n.choose (k + 1 - 1)) * (n + 1) := by
        have := h1.trans_eq h2
        exact Nat.mul_le_mul_right _ this
    _ = (k + 1) * T0.card * (n + 1).choose (k + 1) := by
        simp only [Nat.add_sub_cancel]
        rw [mul_assoc, mul_comm (n.choose k), ← mul_assoc] at *
        nlinarith [h3]

end Meet

section Split
variable {N m : ℕ}

theorem card_split {X : Fin m → Finset (Finset (Fin N))} (j k : Fin m) (hjk : k ≠ j)
    (s0 : Finset (Fin N)) (hs0 : s0 ∈ X j)
    (Q : (Fin m → Finset (Fin N)) → Prop) [DecidablePred Q]
    (hQ : ∀ S s, Q (Function.update S j s) ↔ Q S)
    (P : Finset (Fin N) → Finset (Fin N) → Prop) [DecidableRel P] (b : ℝ)
    (hb : ∀ T ∈ X k, (((X j).filter (fun s => P s T)).card : ℝ) ≤ b) :
    (((Fintype.piFinset X).filter (fun S => Q S ∧ P (S j) (S k))).card : ℝ) ≤
      b * (((Fintype.piFinset (Function.update X j {s0})).filter Q).card : ℝ) := by
  set E := (Fintype.piFinset X).filter (fun S => Q S ∧ P (S j) (S k)) with hE
  set E' := (Fintype.piFinset (Function.update X j {s0})).filter Q with hE'
  have hmaps : ∀ S ∈ E, Function.update S j s0 ∈ E' := by
    intro S hS
    rw [hE, mem_filter, Fintype.mem_piFinset] at hS
    rw [hE', mem_filter, Fintype.mem_piFinset]
    refine ⟨fun i => ?_, (hQ S s0).mpr hS.2.1⟩
    by_cases hi : i = j
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]; exact hS.1 i
  have hcard : E.card = ∑ S' ∈ E', (E.filter (fun S => Function.update S j s0 = S')).card :=
    card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ S' ∈ E', ((E.filter (fun S => Function.update S j s0 = S')).card : ℝ) ≤ b := by
    intro S' hS'
    have hS'1 := (mem_filter.mp hS').1
    rw [Fintype.mem_piFinset] at hS'1
    have hk : S' k ∈ X k := by
      have := hS'1 k
      rwa [Function.update_of_ne hjk] at this
    refine le_trans ?_ (hb (S' k) hk)
    have hle : (E.filter (fun S => Function.update S j s0 = S')).card ≤
        ((X j).filter (fun s => P s (S' k))).card := by
      apply card_le_card_of_injOn (fun S => S j)
      · intro S hS
        rw [Finset.mem_coe, mem_filter] at hS
        obtain ⟨hSE, hSu⟩ := hS
        rw [hE, mem_filter, Fintype.mem_piFinset] at hSE
        rw [Finset.mem_coe, mem_filter]
        refine ⟨hSE.1 j, ?_⟩
        have : S' k = S k := by rw [← hSu, Function.update_of_ne hjk]
        rw [this]; exact hSE.2.2
      · intro S hS T hT hST
        rw [Finset.mem_coe, mem_filter] at hS hT
        funext i
        by_cases hi : i = j
        · subst hi; exact hST
        · have h1 : Function.update S j s0 i = S i := Function.update_of_ne hi _ _
          have h2 : Function.update T j s0 i = T i := Function.update_of_ne hi _ _
          rw [← h1, ← h2, hS.2, hT.2]
    exact_mod_cast hle
  rw [hcard]
  push_cast
  calc ∑ S' ∈ E', ((E.filter (fun S => Function.update S j s0 = S')).card : ℝ)
      ≤ ∑ S' ∈ E', b := Finset.sum_le_sum hfib
    _ = b * (E'.card : ℝ) := by rw [sum_const, nsmul_eq_mul, mul_comm]

end Split

section Main
variable {N m : ℕ}

theorem prod_card_update (X : Fin m → Finset (Finset (Fin N))) (j : Fin m) (s0 : Finset (Fin N)) :
    (∏ i, (((Function.update X j {s0}) i).card : ℝ)) * ((X j).card : ℝ) =
      ∏ i, ((X i).card : ℝ) := by
  rw [← Finset.mul_prod_erase univ (fun i => (((Function.update X j {s0}) i).card : ℝ)) (mem_univ j),
    ← Finset.mul_prod_erase univ (fun i => ((X i).card : ℝ)) (mem_univ j)]
  have : ∏ i ∈ univ.erase j, (((Function.update X j {s0}) i).card : ℝ) =
      ∏ i ∈ univ.erase j, ((X i).card : ℝ) :=
    Finset.prod_congr rfl (fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)])
  rw [this]
  simp only [Function.update_self, card_singleton, Nat.cast_one]
  ring

theorem invol_aux (f : Fin m → Fin m) (hff : ∀ j, f (f j) ≤ j) (R : Finset (Fin m))
    (hR : ∀ j ∈ R, f j ∈ R) (hsurj : ∀ j ∈ R, ∃ i ∈ R, f i = j) : ∀ j ∈ R, f (f j) = j := by
  have himg : R.image f = R := by
    apply Finset.Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
      exact hR x hx
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hsurj y hy
      exact mem_image.mpr ⟨x, hx, hxy⟩
  have hinj : Set.InjOn f R := card_image_iff.mp (by rw [himg])
  have key : ∀ n : ℕ, ∀ j ∈ R, (j : ℕ) = n → f (f j) = j := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hj hjn
      by_contra hne
      have hlt : f (f j) < j := lt_of_le_of_ne (hff j) hne
      have hmem : f (f j) ∈ R := hR _ (hR _ hj)
      have h1 := ih (f (f j) : ℕ) (by rw [← hjn]; exact hlt) (f (f j)) hmem rfl
      have hfj : f j ∈ R := hR j hj
      have hffj : f (f (f j)) ∈ R := hR _ hmem
      have h2 : f (f (f j)) = f j := hinj (Finset.mem_coe.mpr hffj) (Finset.mem_coe.mpr hfj) h1
      have h3 : f (f j) = j := hinj (Finset.mem_coe.mpr hmem) (Finset.mem_coe.mpr hj) h2
      exact hne h3
  intro j hj
  exact key j j hj rfl

/-- The constraint set: `S_i ∩ S_{f i} ≠ ∅` for all `i ∈ R`. -/
def Cons {N m : ℕ} (f : Fin m → Fin m) (R : Finset (Fin m)) (S : Fin m → Finset (Fin N)) : Prop :=
  ∀ i ∈ R, (S i ∩ S (f i)).Nonempty

instance {N m : ℕ} (f : Fin m → Fin m) (R : Finset (Fin m)) : DecidablePred (Cons (N := N) f R) :=
  fun S => by unfold Cons; infer_instance

theorem count_aux (hN : 0 < N) (r : Fin m → ℕ) (hrN : ∀ i, r i ≤ N) (f : Fin m → Fin m)
    (hf : ∀ j, f j ≠ j) (hff : ∀ j, f (f j) ≤ j) :
    ∀ (R : Finset (Fin m)), (∀ j ∈ R, f j ∈ R) →
    ∀ (X : Fin m → Finset (Finset (Fin N))), (∀ i ∈ R, X i = powersetCard (r i) univ) →
    ∃ L : Finset (Fin m), L ⊆ R ∧ R.card ≤ 2 * L.card ∧
      ((((Fintype.piFinset X).filter (Cons f R)).card : ℕ) : ℝ) ≤
        (∏ i, ((X i).card : ℝ)) * ∏ t ∈ L, ((r t : ℝ) * r (f t) / N) := by
  intro R
  induction R using Finset.strongInduction with
  | H R ih =>
  intro hR X hX
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmeet : ∀ j k : Fin m, j ∈ R → k ∈ R → ∀ T ∈ X k,
      (((X j).filter (fun s => (s ∩ T).Nonempty)).card : ℝ) ≤
        ((r j : ℝ) * r k / N) * ((X j).card : ℝ) := by
    intro j k hj hk T hT
    have hXj : X j = powersetCard (r j) univ := hX j hj
    have hXk : X k = powersetCard (r k) univ := hX k hk
    rw [hXk] at hT
    have hTc : T.card = r k := (mem_powersetCard.mp hT).2
    have h1 := card_meeting_mul_le (N := N) (r j) T
    rw [hTc] at h1
    have hc : ((X j).card : ℝ) = (N.choose (r j) : ℝ) := by
      rw [hXj, card_powersetCard, card_univ, Fintype.card_fin]
    rw [hc, hXj, div_mul_eq_mul_div, le_div_iff₀ hNr]
    have h2 : ((((powersetCard (r j) (univ : Finset (Fin N))).filter
        (fun s => (s ∩ T).Nonempty)).card * N : ℕ) : ℝ) ≤ ((r j * r k * N.choose (r j) : ℕ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  by_cases hleaf : ∃ j ∈ R, ∀ i ∈ R, f i ≠ j
  · obtain ⟨j, hjR, hnop⟩ := hleaf
    have hkR : f j ∈ R := hR j hjR
    have hkj : f j ≠ j := hf j
    have hXj : X j = powersetCard (r j) univ := hX j hjR
    have hne : (X j).Nonempty := by
      rw [hXj, powersetCard_nonempty, card_univ, Fintype.card_fin]; exact hrN j
    obtain ⟨s0, hs0⟩ := hne
    have hR'sub : R.erase j ⊂ R := erase_ssubset hjR
    have hR'cl : ∀ i ∈ R.erase j, f i ∈ R.erase j := by
      intro i hi
      rw [mem_erase] at hi ⊢
      exact ⟨hnop i hi.2, hR i hi.2⟩
    have hX' : ∀ i ∈ R.erase j, Function.update X j {s0} i = powersetCard (r i) univ := by
      intro i hi
      rw [Function.update_of_ne (mem_erase.mp hi).1]
      exact hX i (mem_of_mem_erase hi)
    obtain ⟨L', hL'R, hL'c, hL'b⟩ := ih (R.erase j) hR'sub hR'cl (Function.update X j {s0}) hX'
    have hjL' : j ∉ L' := fun h => by simpa using hL'R h
    refine ⟨insert j L', ?_, ?_, ?_⟩
    · intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact hjR
      · exact mem_of_mem_erase (hL'R ht)
    · rw [card_insert_of_notMem hjL']
      have := card_erase_add_one hjR
      omega
    · rw [prod_insert hjL']
      have hQ : ∀ S s, Cons f (R.erase j) (Function.update S j s) ↔ Cons (N := N) f (R.erase j) S := by
        intro S s
        refine forall₂_congr (fun i hi => ?_)
        have hij : i ≠ j := (mem_erase.mp hi).1
        have hfi : f i ≠ j := hnop i (mem_of_mem_erase hi)
        rw [Function.update_of_ne hij, Function.update_of_ne hfi]
      have hsubset : (Fintype.piFinset X).filter (Cons f R) ⊆
          (Fintype.piFinset X).filter
            (fun S => Cons f (R.erase j) S ∧
              (fun a b : Finset (Fin N) => (a ∩ b).Nonempty) (S j) (S (f j))) := by
        intro S hS
        rw [mem_filter] at hS ⊢
        exact ⟨hS.1, fun i hi => hS.2 i (mem_of_mem_erase hi), hS.2 j hjR⟩
      have hsplit := card_split (X := X) j (f j) hkj s0 hs0 (Cons f (R.erase j)) hQ
        (fun a b : Finset (Fin N) => (a ∩ b).Nonempty)
        (((r j : ℝ) * r (f j) / N) * ((X j).card : ℝ)) (hmeet j (f j) hjR hkR)
      have hP := prod_card_update X j s0
      have hw : 0 ≤ ((r j : ℝ) * r (f j) / N) * ((X j).card : ℝ) := by positivity
      calc ((((Fintype.piFinset X).filter (Cons f R)).card : ℕ) : ℝ)
          ≤ ((((Fintype.piFinset X).filter
            (fun S => Cons f (R.erase j) S ∧
              (fun a b : Finset (Fin N) => (a ∩ b).Nonempty) (S j) (S (f j)))).card : ℕ) : ℝ) := by
            exact_mod_cast card_le_card hsubset
        _ ≤ _ := hsplit
        _ ≤ (((r j : ℝ) * r (f j) / N) * ((X j).card : ℝ)) *
              ((∏ i, (((Function.update X j {s0}) i).card : ℝ)) *
                ∏ t ∈ L', ((r t : ℝ) * r (f t) / N)) :=
            mul_le_mul_of_nonneg_left hL'b hw
        _ = ((∏ i, ((X i).card : ℝ))) * (((r j : ℝ) * r (f j) / N) * ∏ t ∈ L', ((r t : ℝ) * r (f t) / N)) := by
            rw [← hP]; ring
  · push_neg at hleaf
    rcases R.eq_empty_or_nonempty with rfl | ⟨j, hjR⟩
    · refine ⟨∅, subset_refl _, by simp, ?_⟩
      have : (Fintype.piFinset X).filter (Cons (N := N) f ∅) = Fintype.piFinset X := by
        apply filter_true_of_mem
        intro S _ i hi; simp at hi
      rw [this, Fintype.card_piFinset]
      simp
    have hinv := invol_aux f hff R hR hleaf
    have hkR : f j ∈ R := hR j hjR
    have hkj : f j ≠ j := hf j
    have hfk : f (f j) = j := hinv j hjR
    have hXj : X j = powersetCard (r j) univ := hX j hjR
    have hXk : X (f j) = powersetCard (r (f j)) univ := hX (f j) hkR
    have hne : (X j).Nonempty := by
      rw [hXj, powersetCard_nonempty, card_univ, Fintype.card_fin]; exact hrN j
    have hne' : (X (f j)).Nonempty := by
      rw [hXk, powersetCard_nonempty, card_univ, Fintype.card_fin]; exact hrN _
    obtain ⟨s0, hs0⟩ := hne
    obtain ⟨s1, hs1⟩ := hne'
    obtain ⟨R'', hR''⟩ : ∃ R'', R'' = (R.erase j).erase (f j) := ⟨_, rfl⟩
    have hR''sub : R'' ⊂ R := by
      rw [hR'']
      exact lt_of_le_of_lt (erase_subset _ _) (erase_ssubset hjR)
    have hmemR'' : ∀ i, i ∈ R'' → i ∈ R ∧ i ≠ j ∧ i ≠ f j := by
      intro i hi
      rw [hR'', mem_erase, mem_erase] at hi
      exact ⟨hi.2.2, hi.2.1, hi.1⟩
    have hR''cl : ∀ i ∈ R'', f i ∈ R'' := by
      intro i hi
      obtain ⟨hiR, hij, hik⟩ := hmemR'' i hi
      rw [hR'', mem_erase, mem_erase]
      refine ⟨?_, ?_, hR i hiR⟩
      · intro h
        apply hij
        have := hinv i hiR
        rw [h, hfk] at this
        exact this.symm
      · intro h
        apply hik
        have := hinv i hiR
        rw [h] at this
        exact this.symm
    have hX'' : ∀ i ∈ R'',
        Function.update (Function.update X j {s0}) (f j) {s1} i = powersetCard (r i) univ := by
      intro i hi
      obtain ⟨hiR, hij, hik⟩ := hmemR'' i hi
      rw [Function.update_of_ne hik, Function.update_of_ne hij]
      exact hX i hiR
    obtain ⟨L'', hL''R, hL''c, hL''b⟩ := ih R'' hR''sub hR''cl _ hX''
    have hjL'' : j ∉ L'' := fun h => (hmemR'' j (hL''R h)).2.1 rfl
    refine ⟨insert j L'', ?_, ?_, ?_⟩
    · intro t ht
      rcases mem_insert.mp ht with rfl | ht
      · exact hjR
      · exact (hmemR'' t (hL''R ht)).1
    · rw [card_insert_of_notMem hjL'']
      have h1 := card_erase_add_one hjR
      have h3 : f j ∈ R.erase j := mem_erase.mpr ⟨hkj, hkR⟩
      have h4 : R''.card + 1 = (R.erase j).card := by rw [hR'']; exact card_erase_add_one h3
      omega
    · rw [prod_insert hjL'']
      have hQj : ∀ S s, Cons f R'' (Function.update S j s) ↔ Cons (N := N) f R'' S := by
        intro S s
        refine forall₂_congr (fun i hi => ?_)
        have hij : i ≠ j := (hmemR'' i hi).2.1
        have hfi : f i ≠ j := (hmemR'' _ (hR''cl i hi)).2.1
        rw [Function.update_of_ne hij, Function.update_of_ne hfi]
      have hQk : ∀ S s, Cons f R'' (Function.update S (f j) s) ↔ Cons (N := N) f R'' S := by
        intro S s
        refine forall₂_congr (fun i hi => ?_)
        have hij : i ≠ f j := (hmemR'' i hi).2.2
        have hfi : f i ≠ f j := (hmemR'' _ (hR''cl i hi)).2.2
        rw [Function.update_of_ne hij, Function.update_of_ne hfi]
      have hsubset : (Fintype.piFinset X).filter (Cons f R) ⊆
          (Fintype.piFinset X).filter
            (fun S => Cons f R'' S ∧
              (fun a b : Finset (Fin N) => (a ∩ b).Nonempty) (S j) (S (f j))) := by
        intro S hS
        rw [mem_filter] at hS ⊢
        exact ⟨hS.1, fun i hi => hS.2 i (hmemR'' i hi).1, hS.2 j hjR⟩
      have hsplit1 := card_split (X := X) j (f j) hkj s0 hs0 (Cons f R'') hQj
        (fun a b : Finset (Fin N) => (a ∩ b).Nonempty)
        (((r j : ℝ) * r (f j) / N) * ((X j).card : ℝ)) (hmeet j (f j) hjR hkR)
      have hs1' : s1 ∈ (Function.update X j {s0}) (f j) := by
        rw [Function.update_of_ne hkj]; exact hs1
      have hX'k : ((Function.update X j {s0}) (f j)).card = (X (f j)).card := by
        rw [Function.update_of_ne hkj]
      have hsplit2 := card_split (X := Function.update X j {s0}) (f j) j hkj.symm s1 hs1'
        (Cons f R'') hQk (fun _ _ : Finset (Fin N) => True) ((X (f j)).card : ℝ) (by
          intro T _
          rw [Function.update_of_ne hkj]
          simp)
      have e : ((Fintype.piFinset (Function.update X j {s0})).filter (Cons f R'')).card ≤
          ((Fintype.piFinset (Function.update X j {s0})).filter
          (fun S => Cons f R'' S ∧ (fun _ _ : Finset (Fin N) => True) (S (f j)) (S j))).card := by
        apply le_of_eq
        congr 1
        ext S
        simp
      have hP1 := prod_card_update X j s0
      have hP2 := prod_card_update (Function.update X j {s0}) (f j) s1
      rw [hX'k] at hP2
      have hw : 0 ≤ ((r j : ℝ) * r (f j) / N) * ((X j).card : ℝ) := by positivity
      have hk0 : (0 : ℝ) ≤ ((X (f j)).card : ℝ) := by positivity
      have e' : ((((Fintype.piFinset (Function.update X j {s0})).filter (Cons f R'')).card : ℕ) : ℝ) ≤
          ((X (f j)).card : ℝ) * ((((Fintype.piFinset (Function.update (Function.update X j {s0})
                (f j) {s1})).filter (Cons f R'')).card : ℕ) : ℝ) :=
        (by exact_mod_cast e : _ ≤ _).trans hsplit2
      calc ((((Fintype.piFinset X).filter (Cons f R)).card : ℕ) : ℝ)
          ≤ ((((Fintype.piFinset X).filter
            (fun S => Cons f R'' S ∧
              (fun a b : Finset (Fin N) => (a ∩ b).Nonempty) (S j) (S (f j)))).card : ℕ) : ℝ) := by
            exact_mod_cast card_le_card hsubset
        _ ≤ _ := hsplit1
        _ ≤ (((r j : ℝ) * r (f j) / N) * ((X j).card : ℝ)) *
              (((X (f j)).card : ℝ) * ((((Fintype.piFinset (Function.update (Function.update X j {s0})
                (f j) {s1})).filter (Cons f R'')).card : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left e' hw
        _ ≤ (((r j : ℝ) * r (f j) / N) * ((X j).card : ℝ)) *
              (((X (f j)).card : ℝ) * ((∏ i, (((Function.update (Function.update X j {s0}) (f j) {s1}) i).card : ℝ)) *
                ∏ t ∈ L'', ((r t : ℝ) * r (f t) / N))) := by
            apply mul_le_mul_of_nonneg_left _ hw
            exact mul_le_mul_of_nonneg_left hL''b hk0
        _ = ((∏ i, ((X i).card : ℝ))) *
              (((r j : ℝ) * r (f j) / N) * ∏ t ∈ L'', ((r t : ℝ) * r (f t) / N)) := by
            rw [← hP1, ← hP2]; ring
end Main

section Final
variable {N m : ℕ}

theorem exists_f (S : Fin m → Finset (Fin N)) (h : ∀ j, ∃ i, i ≠ j ∧ (S j ∩ S i).Nonempty) :
    ∃ f : Fin m → Fin m, (∀ j, f j ≠ j) ∧ (∀ j, f (f j) ≤ j) ∧
      ∀ j, (S j ∩ S (f j)).Nonempty := by
  have h' : ∀ j, ∃ i, (i ≠ j ∧ (S j ∩ S i).Nonempty) ∧
      ∀ i', (i' ≠ j ∧ (S j ∩ S i').Nonempty) → i ≤ i' := by
    intro j
    obtain ⟨i, hi⟩ := h j
    have hne : (univ.filter (fun i => i ≠ j ∧ (S j ∩ S i).Nonempty)).Nonempty :=
      ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    refine ⟨(univ.filter (fun i => i ≠ j ∧ (S j ∩ S i).Nonempty)).min' hne, ?_, ?_⟩
    · exact (mem_filter.mp (min'_mem _ hne)).2
    · intro i' hi'
      exact Finset.min'_le _ i' (mem_filter.mpr ⟨mem_univ _, hi'⟩)
  choose f hf1 hf2 using h'
  refine ⟨f, fun j => (hf1 j).1, fun j => ?_, fun j => (hf1 j).2⟩
  apply hf2 (f j) j
  refine ⟨(hf1 j).1.symm, ?_⟩
  rw [inter_comm]
  exact (hf1 j).2

theorem one_le_prod_aux (r : Fin m → ℕ) (hr1 : ∀ i, 1 ≤ r i) (s : Finset (Fin m)) :
    (1 : ℝ) ≤ ∏ i ∈ s, (r i : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have : (1 : ℝ) ≤ r a := by exact_mod_cast hr1 a
    nlinarith

theorem weight_bound (hN : 0 < N) (p : ℕ) (hm : m = 2 * p) (r : Fin m → ℕ)
    (hr1 : ∀ i, 1 ≤ r i) (f : Fin m → Fin m) (L : Finset (Fin m)) (hLc : m ≤ 2 * L.card) :
    ∏ t ∈ L, ((r t : ℝ) * r (f t) / N) ≤ (∏ i, (r i : ℝ)) ^ (2 * m) / (N : ℝ) ^ p := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hP1 : (1 : ℝ) ≤ ∏ i, (r i : ℝ) := one_le_prod_aux r hr1 univ
  have hLm : L.card ≤ m := by
    have := card_le_univ L
    rwa [Fintype.card_fin] at this
  have hLp : p ≤ L.card := by omega
  have hone : ∀ t : Fin m, (r t : ℝ) ≤ ∏ i, (r i : ℝ) := by
    intro t
    rw [← Finset.mul_prod_erase univ (fun i => (r i : ℝ)) (mem_univ t)]
    have := one_le_prod_aux r hr1 (univ.erase t)
    have h0 : (0 : ℝ) ≤ r t := Nat.cast_nonneg _
    nlinarith
  have hw : ∀ t ∈ L, (r t : ℝ) * r (f t) / N ≤ (∏ i, (r i : ℝ)) ^ 2 / N := by
    intro t _
    apply div_le_div_of_nonneg_right _ hNr.le
    have h1 := hone t
    have h2 := hone (f t)
    nlinarith [(Nat.cast_nonneg (r t) : (0:ℝ) ≤ r t), (Nat.cast_nonneg (r (f t)) : (0:ℝ) ≤ r (f t))]
  calc ∏ t ∈ L, ((r t : ℝ) * r (f t) / N) ≤ ∏ t ∈ L, ((∏ i, (r i : ℝ)) ^ 2 / N) :=
        Finset.prod_le_prod₀ (fun t _ => by positivity) hw
    _ = ((∏ i, (r i : ℝ)) ^ 2 / N) ^ L.card := prod_const _
    _ = (∏ i, (r i : ℝ)) ^ (2 * L.card) / (N : ℝ) ^ L.card := by rw [div_pow, ← pow_mul]
    _ ≤ (∏ i, (r i : ℝ)) ^ (2 * m) / (N : ℝ) ^ p := by
        apply div_le_div₀ (by positivity)
        · exact pow_le_pow_right₀ hP1 (by omega)
        · positivity
        · exact pow_le_pow_right₀ (by exact_mod_cast hN) hLp

theorem card_noiso_le (hN : 0 < N) (p : ℕ) (hm : m = 2 * p) (r : Fin m → ℕ)
    (hr1 : ∀ i, 1 ≤ r i) (hrN : ∀ i, r i ≤ N) :
    (((Fintype.piFinset (fun i => powersetCard (r i) (univ : Finset (Fin N)))).filter
        (fun S => ∀ j, ∃ i, i ≠ j ∧ (S j ∩ S i).Nonempty)).card : ℝ) ≤
      (∏ i, ((powersetCard (r i) (univ : Finset (Fin N))).card : ℝ)) *
        (((m ^ m : ℕ) : ℝ) * ((∏ i, (r i : ℝ)) ^ (2 * m) / (N : ℝ) ^ p)) := by
  have hbound : ∀ f ∈ (univ.filter (fun f : Fin m → Fin m =>
        (∀ j, f j ≠ j) ∧ ∀ j, f (f j) ≤ j)),
      ((((Fintype.piFinset (fun i => powersetCard (r i) (univ : Finset (Fin N)))).filter
        (Cons f univ)).card : ℕ) : ℝ) ≤
      (∏ i, ((powersetCard (r i) (univ : Finset (Fin N))).card : ℝ)) *
        ((∏ i, (r i : ℝ)) ^ (2 * m) / (N : ℝ) ^ p) := by
    intro f hf
    rw [mem_filter] at hf
    obtain ⟨L, _, hLc, hLb⟩ := count_aux hN r hrN f hf.2.1 hf.2.2 univ (fun _ _ => mem_univ _)
      (fun i => powersetCard (r i) (univ : Finset (Fin N))) (fun _ _ => rfl)
    refine hLb.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [card_univ, Fintype.card_fin] at hLc
    exact weight_bound hN p hm r hr1 f L hLc
  have hsub : (Fintype.piFinset (fun i => powersetCard (r i) (univ : Finset (Fin N)))).filter
      (fun S => ∀ j, ∃ i, i ≠ j ∧ (S j ∩ S i).Nonempty) ⊆
      (univ.filter (fun f : Fin m → Fin m => (∀ j, f j ≠ j) ∧ ∀ j, f (f j) ≤ j)).biUnion
        (fun f => (Fintype.piFinset (fun i => powersetCard (r i) (univ : Finset (Fin N)))).filter
          (Cons f univ)) := by
    intro S hS
    rw [mem_filter] at hS
    obtain ⟨f, hf1, hf2, hf3⟩ := exists_f S hS.2
    refine mem_biUnion.mpr ⟨f, ?_, ?_⟩
    · rw [mem_filter]; exact ⟨mem_univ _, hf1, hf2⟩
    · rw [mem_filter]; exact ⟨hS.1, fun j _ => hf3 j⟩
  have hcardFs : (univ.filter (fun f : Fin m → Fin m => (∀ j, f j ≠ j) ∧ ∀ j, f (f j) ≤ j)).card ≤
      m ^ m := by
    calc _ ≤ (univ : Finset (Fin m → Fin m)).card := card_le_univ _
      _ = m ^ m := by rw [card_univ, Fintype.card_fun, Fintype.card_fin]
  have hnn : 0 ≤ (∏ i, ((powersetCard (r i) (univ : Finset (Fin N))).card : ℝ)) *
        ((∏ i, (r i : ℝ)) ^ (2 * m) / (N : ℝ) ^ p) :=
    mul_nonneg (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _))
      (div_nonneg (pow_nonneg (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg _)) _)
        (pow_nonneg (Nat.cast_nonneg _) _))
  calc _ ≤ ((((univ.filter (fun f : Fin m → Fin m => (∀ j, f j ≠ j) ∧ ∀ j, f (f j) ≤ j)).biUnion
        (fun f => (Fintype.piFinset (fun i => powersetCard (r i) (univ : Finset (Fin N)))).filter
          (Cons f univ))).card : ℕ) : ℝ) := Nat.cast_le.mpr (card_le_card hsub)
    _ ≤ ∑ f ∈ (univ.filter (fun f : Fin m → Fin m => (∀ j, f j ≠ j) ∧ ∀ j, f (f j) ≤ j)),
          ((((Fintype.piFinset (fun i => powersetCard (r i) (univ : Finset (Fin N)))).filter
            (Cons f univ)).card : ℕ) : ℝ) :=
        (Nat.cast_le.mpr card_biUnion_le).trans (le_of_eq (Nat.cast_sum _ _))
    _ ≤ ∑ f ∈ (univ.filter (fun f : Fin m → Fin m => (∀ j, f j ≠ j) ∧ ∀ j, f (f j) ≤ j)),
          ((∏ i, ((powersetCard (r i) (univ : Finset (Fin N))).card : ℝ)) *
            ((∏ i, (r i : ℝ)) ^ (2 * m) / (N : ℝ) ^ p)) := Finset.sum_le_sum hbound
    _ = ((univ.filter (fun f : Fin m → Fin m => (∀ j, f j ≠ j) ∧ ∀ j, f (f j) ≤ j)).card : ℝ) *
          ((∏ i, ((powersetCard (r i) (univ : Finset (Fin N))).card : ℝ)) *
            ((∏ i, (r i : ℝ)) ^ (2 * m) / (N : ℝ) ^ p)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ((m ^ m : ℕ) : ℝ) * ((∏ i, ((powersetCard (r i) (univ : Finset (Fin N))).card : ℝ)) *
            ((∏ i, (r i : ℝ)) ^ (2 * m) / (N : ℝ) ^ p)) :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcardFs) hnn
    _ = _ := by ring

end Final

#print axioms card_noiso_le

end QuantumNLS.HighMomentsCount
