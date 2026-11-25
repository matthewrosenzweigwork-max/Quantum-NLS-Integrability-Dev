import NlsGge.GK38.RealTypeSpectrumSorting

/-! # S5: monotone projection of the real cluster blocks -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem realType_norm_sub_real38 (a b : ℂ) (ha : a.im = 0) (hb : b.im = 0) :
    ‖a - b‖ = |a.re - b.re| := by
  have ea : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [ha])
  have eb : b = (b.re : ℂ) := Complex.ext (by simp) (by simp [hb])
  rw [ea, eb, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp only [Complex.ofReal_re]

/-- Distinct real clusters cannot reverse their order under a projection. -/
theorem realType_cluster_projection_mono38 (s t : Multiset ℂ) (p : ℂ → ℂ) (ρ : ℂ → ℝ)
    (hreal : ∀ a ∈ s, a.im = 0)
    (hgraph : ∀ z ∈ t, p z ∈ s ∧ dist z (p z) < ρ (p z))
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a ≠ b →
      3 * ρ a < dist a b ∧ 3 * ρ b < dist a b) :
    ∀ z ∈ t, ∀ w ∈ t, complexLexLE38 z w → complexLexLE38 (p z) (p w) := by
  intro z hz w hw hzw
  have hzr : z.re ≤ w.re := by
    rcases (complexLexLE_iff38 z w).mp hzw with h | h
    · exact h.le
    · exact h.1.le
  obtain ⟨hps, hzp⟩ := hgraph z hz
  obtain ⟨hqs, hwq⟩ := hgraph w hw
  have hza : |z.re - (p z).re| < ρ (p z) := by
    have h : |z.re - (p z).re| ≤ ‖z - p z‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (z - p z)
    exact h.trans_lt (by simpa [dist_eq_norm] using hzp)
  have hwb : |w.re - (p w).re| < ρ (p w) := by
    have h : |w.re - (p w).re| ≤ ‖w - p w‖ := by
      simpa only [Complex.sub_re] using Complex.abs_re_le_norm (w - p w)
    exact h.trans_lt (by simpa [dist_eq_norm] using hwq)
  have hpq : (p z).re ≤ (p w).re := by
    by_contra h
    have hlt : (p w).re < (p z).re := lt_of_not_ge h
    have hne : p z ≠ p w := by intro he; rw [he] at hlt; exact (lt_irrefl _ hlt)
    obtain ⟨hdp, hdq⟩ := hsep _ hps _ hqs hne
    have hd : dist (p z) (p w) = (p z).re - (p w).re := by
      rw [dist_eq_norm, realType_norm_sub_real38 _ _ (hreal _ hps) (hreal _ hqs),
        abs_of_pos (sub_pos.mpr hlt)]
    rw [hd] at hdp hdq
    have hza' := abs_lt.mp hza
    have hwb' := abs_lt.mp hwb
    linarith
  apply (complexLexLE_iff38 _ _).mpr
  rcases lt_or_eq_of_le hpq with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h, by rw [hreal _ hps, hreal _ hqs]⟩

/-- Actual coverage and cluster counts realize the monotone projection. -/
theorem periodic_cluster_projection38 (u₀ u : PhysicalL2) (N : ℕ)
    (hN₀ : RootCountingAt38 (perChar (realSlice u₀)) 2 N)
    (hN : RootCountingAt38 (perChar (realSlice u)) 2 N) (ρ : ℂ → ℝ)
    (hρ : ∀ a ∈ Lib.zeroMultiset (perChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
      0 < ρ a ∧ closedBall a (ρ a) ⊆ ball 0 (countingRadius38 N) ∧
      ∀ z ∈ closedBall a (3 * ρ a), z ≠ a → perChar (realSlice u₀) z ≠ 0)
    (hc : ∀ a ∈ Lib.zeroMultiset (perChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
      Multiset.card (Lib.zeroMultiset (perChar (realSlice u)) (ball a (ρ a))) =
        (Lib.zeroMultiset (perChar (realSlice u₀)) (ball 0 (countingRadius38 N))).count a) :
    ∃ p : ℂ → ℂ,
      (Lib.zeroMultiset (perChar (realSlice u)) (ball 0 (countingRadius38 N))).map p =
        Lib.zeroMultiset (perChar (realSlice u₀)) (ball 0 (countingRadius38 N)) ∧
      (∀ z ∈ Lib.zeroMultiset (perChar (realSlice u)) (ball 0 (countingRadius38 N)),
        ∀ w ∈ Lib.zeroMultiset (perChar (realSlice u)) (ball 0 (countingRadius38 N)),
        complexLexLE38 z w → complexLexLE38 (p z) (p w)) ∧
      ∀ z ∈ Lib.zeroMultiset (perChar (realSlice u)) (ball 0 (countingRadius38 N)),
        p z ∈ Lib.zeroMultiset (perChar (realSlice u₀)) (ball 0 (countingRadius38 N)) ∧
          z ∈ ball (p z) (ρ (p z)) := by
  classical
  let M₀ := Lib.zeroMultiset (perChar (realSlice u₀)) (ball 0 (countingRadius38 N))
  let M := Lib.zeroMultiset (perChar (realSlice u)) (ball 0 (countingRadius38 N))
  have hcov := periodic_cluster_coverage38 u₀ u N hN₀ hN ρ hρ hc
  let p : ℂ → ℂ := fun z => if hz : z ∈ M then Classical.choose (hcov z hz) else 0
  have hp (z : ℂ) (hz : z ∈ M) : p z ∈ M₀ ∧ z ∈ ball (p z) (ρ (p z)) := by
    simpa only [p, dite_eq_left hz] using Classical.choose_spec (hcov z hz)
  have hmap : M.map p = M₀ := by
    apply Multiset.ext'
    intro a
    by_cases ha : a ∈ M₀
    · have hefilter : M.filter (fun z => a = p z) = M.filter (fun z => z ∈ ball a (ρ a)) := by
        apply Multiset.filter_congr
        intro z hz
        constructor
        · intro he
          rw [he]
          exact (hp z hz).2
        · intro hza
          by_contra hne
          have hd := periodic_cluster_disjoint38 u₀ N hN₀ ρ
            (fun b hb => ⟨(hρ b hb).1, (hρ b hb).2.2⟩)
            a (p z) ha (hp z hz).1 hne
          exact (Set.disjoint_left.mp hd hza) (hp z hz).2
      rw [Multiset.count_map, hefilter, periodic_cluster_filter38 u N hN a (ρ a)
        (fun z hz => (hρ a ha).2.1 (ball_subset_closedBall hz))]
      exact hc a ha
    · rw [Multiset.count_map]
      have hf : M.filter (fun z => a = p z) = 0 := by
        apply Multiset.filter_eq_nil.mpr
        intro z hz he
        exact ha (he ▸ (hp z hz).1)
      rw [hf, Multiset.card_zero, Multiset.count_eq_zero.mpr ha]
  have hreal : ∀ a ∈ M₀, a.im = 0 := fun a ha =>
    perChar_root_real38 u₀ a (((counting_mem_zeroMultiset38 hN₀ _ _ a).mp ha).2)
  have hsep : ∀ a ∈ M₀, ∀ b ∈ M₀, a ≠ b →
      3 * ρ a < dist a b ∧ 3 * ρ b < dist a b := by
    intro a ha b hb hab
    have haz := ((counting_mem_zeroMultiset38 hN₀ _ _ a).mp ha).2
    have hbz := ((counting_mem_zeroMultiset38 hN₀ _ _ b).mp hb).2
    constructor
    · by_contra h
      exact (hρ a ha).2.2 b (by simpa [dist_comm] using le_of_not_gt h) hab.symm hbz
    · by_contra h
      exact (hρ b hb).2.2 a (le_of_not_gt h) hab haz
  exact ⟨p, hmap, realType_cluster_projection_mono38 M₀ M p ρ hreal
    (fun z hz => ⟨(hp z hz).1, (hp z hz).2⟩) hsep, hp⟩

end
end NlsGge.GK38
