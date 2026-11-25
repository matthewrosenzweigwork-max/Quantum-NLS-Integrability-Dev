import NlsGge.GK38.DirichletRealClusters

/-! Monotone projection of actual real Dirichlet root clusters. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

/-- Actual coverage and cluster counts realize the monotone projection. -/
theorem dirichlet_cluster_projection38 (u₀ u : PhysicalL2) (N : ℕ)
    (hN₀ : RootCountingAt38 (dirichletChar (realSlice u₀)) 1 N)
    (hN : RootCountingAt38 (dirichletChar (realSlice u)) 1 N) (ρ : ℂ → ℝ)
    (hρ : ∀ a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
      0 < ρ a ∧ closedBall a (ρ a) ⊆ ball 0 (countingRadius38 N) ∧
      ∀ z ∈ closedBall a (3 * ρ a), z ≠ a → dirichletChar (realSlice u₀) z ≠ 0)
    (hc : ∀ a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
      Multiset.card (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball a (ρ a))) =
        (Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N))).count a) :
    ∃ p : ℂ → ℂ,
      (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N))).map p =
        Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)) ∧
      (∀ z ∈ Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N)),
        ∀ w ∈ Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N)),
        complexLexLE38 z w → complexLexLE38 (p z) (p w)) ∧
      ∀ z ∈ Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N)),
        p z ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)) ∧
          z ∈ ball (p z) (ρ (p z)) := by
  classical
  let M₀ := Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N))
  let M := Lib.zeroMultiset (dirichletChar (realSlice u)) (ball 0 (countingRadius38 N))
  have hcov := dirichlet_cluster_coverage38 u₀ u N hN₀ hN ρ hρ hc
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
          have hd := dirichlet_cluster_disjoint38 u₀ N hN₀ ρ
            (fun b hb => ⟨(hρ b hb).1, (hρ b hb).2.2⟩)
            a (p z) ha (hp z hz).1 hne
          exact (Set.disjoint_left.mp hd hza) (hp z hz).2
      rw [Multiset.count_map, hefilter, dirichlet_cluster_filter38 u N hN a (ρ a)
        (fun z hz => (hρ a ha).2.1 (ball_subset_closedBall hz))]
      exact hc a ha
    · rw [Multiset.count_map]
      have hf : M.filter (fun z => a = p z) = 0 := by
        apply Multiset.filter_eq_nil.mpr
        intro z hz he
        exact ha (he ▸ (hp z hz).1)
      rw [hf, Multiset.card_zero, Multiset.count_eq_zero.mpr ha]
  have hreal : ∀ a ∈ M₀, a.im = 0 := fun a ha =>
    dirichletChar_root_real38 u₀ a (((counting_mem_zeroMultiset38 hN₀ _ _ a).mp ha).2)
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
