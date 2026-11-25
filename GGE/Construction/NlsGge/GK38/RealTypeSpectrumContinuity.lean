import NlsGge.GK38.RealTypeSpectrumProjection

/-! # S5: real homotopy continuity obtained from actual sorted clusters -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem periodic_real_cluster_sorting38 (u₀ : PhysicalL2) (N : ℕ)
    (hN₀ : RootCountingAt38 (perChar (realSlice u₀)) 2 N) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PhysicalL2, U ∈ 𝓝 u₀ ∧ ∀ u ∈ U,
      RootCountingAt38 (perChar (realSlice u)) 2 N → ∀ j : ℕ, j < 4 * N + 2 →
        ‖(centralRoots (perChar (realSlice u)) N).getD j 0 -
          (centralRoots (perChar (realSlice u₀)) N).getD j 0‖ < ε := by
  classical
  obtain ⟨ρ, hρ, hc⟩ := periodic_cluster_counts38 u₀ N hN₀ ε hε
  refine ⟨{u | ∀ a ∈ Lib.zeroMultiset (perChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
    Multiset.card (Lib.zeroMultiset (perChar (realSlice u)) (ball a (ρ a))) =
      (Lib.zeroMultiset (perChar (realSlice u₀)) (ball 0 (countingRadius38 N))).count a},
    hc, ?_⟩
  intro u hu hN j hj
  obtain ⟨p, hmap, hmono, hp⟩ := periodic_cluster_projection38 u₀ u N hN₀ hN ρ
    (fun a ha => ⟨(hρ a ha).1, (hρ a ha).2.2.1, (hρ a ha).2.2.2⟩) hu
  apply realType_sorted_close38 _ _ p ε hmap hmono
  · intro z hz
    have he := mem_ball_iff_norm.mp (hp z hz).2
    exact he.trans ((hρ _ (hp z hz).1).2.1)
  · have he := hN₀.2.2.2.2.2.1
    omega

/-- The only label continuity exported here is along the actual real deformation. -/
theorem periodic_real_path_continuous38 (u : PhysicalL2) (k : ℤ) :
    ContinuousOn (fun t : ℝ => lamSeq (realSlice (t • u)) k) (Icc 0 1) := by
  intro t₀ _ht₀
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨U, hU, N, _hN, hk₁, hk₂, hcount⟩ := periodic_real_fixed_window38 (t₀ • u) k
  have hN₀ := hcount _ (mem_of_mem_nhds hU)
  obtain ⟨V, hV, hsort⟩ := periodic_real_cluster_sorting38 (t₀ • u) N hN₀ ε hε
  have ht : Continuous (fun t : ℝ => t • u) := by fun_prop
  have heU : ∀ᶠ t in 𝓝 t₀, t • u ∈ U := ht.continuousAt.preimage_mem_nhds hU
  have heV : ∀ᶠ t in 𝓝 t₀, t • u ∈ V := ht.continuousAt.preimage_mem_nhds hV
  filter_upwards [heU, heV] with t htU htV
  have hNt := hcount _ htU
  have hval (v : PhysicalL2) (hv : RootCountingAt38 (perChar (realSlice v)) 2 N) :
      lamSeq (realSlice v) k = (centralRoots (perChar (realSlice v)) N).getD
        (k + 2 * (N : ℤ)).toNat 0 := by
    rw [lamSeq_eq_candidate38 _ hv, periodicCandidate38, ite_eq_left ⟨hk₁, hk₂⟩]
  rw [dist_eq_norm, hval _ hNt, hval _ hN₀]
  apply hsort _ htV hNt
  omega

end
end NlsGge.GK38
