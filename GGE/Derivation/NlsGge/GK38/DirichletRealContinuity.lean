import NlsGge.GK38.DirichletRealProjection

/-! Strong continuity of the actual canonical Dirichlet labels from q=1 clusters. -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem dirichlet_real_cluster_sorting38 (u₀ : PhysicalL2) (N : ℕ)
    (hN₀ : RootCountingAt38 (dirichletChar (realSlice u₀)) 1 N) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set PhysicalL2, U ∈ 𝓝 u₀ ∧ ∀ u ∈ U,
      RootCountingAt38 (dirichletChar (realSlice u)) 1 N → ∀ j : ℕ, j < 2 * N + 1 →
        ‖(centralRoots (dirichletChar (realSlice u)) N).getD j 0 -
          (centralRoots (dirichletChar (realSlice u₀)) N).getD j 0‖ < ε := by
  classical
  obtain ⟨ρ, hρ, hc⟩ := dirichlet_cluster_counts38 u₀ N hN₀ ε hε
  refine ⟨{u | ∀ a ∈ Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N)),
    Multiset.card (Lib.zeroMultiset (dirichletChar (realSlice u)) (ball a (ρ a))) =
      (Lib.zeroMultiset (dirichletChar (realSlice u₀)) (ball 0 (countingRadius38 N))).count a},
    hc, ?_⟩
  intro u hu hN j hj
  obtain ⟨p, hmap, hmono, hp⟩ := dirichlet_cluster_projection38 u₀ u N hN₀ hN ρ
    (fun a ha => ⟨(hρ a ha).1, (hρ a ha).2.2.1, (hρ a ha).2.2.2⟩) hu
  apply realType_sorted_close38 _ _ p ε hmap hmono
  · intro z hz
    have he := mem_ball_iff_norm.mp (hp z hz).2
    exact he.trans ((hρ _ (hp z hz).1).2.1)
  · have he := hN₀.2.2.2.2.2.1
    omega

theorem continuous_gkMu38 (k : ℤ) : Continuous (fun u : PhysicalL2 => gkMu u k) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  obtain ⟨U, hU, N, _hN, hk₁, hk₂, hcount⟩ := dirichlet_real_fixed_window38 u₀ k
  have hN₀ := hcount _ (mem_of_mem_nhds hU)
  obtain ⟨V, hV, hsort⟩ := dirichlet_real_cluster_sorting38 u₀ N hN₀ ε hε
  filter_upwards [hU, hV] with u huU huV
  have hNu := hcount _ huU
  have hval (v : PhysicalL2) (hv : RootCountingAt38 (dirichletChar (realSlice v)) 1 N) :
      muSeq (realSlice v) k = (centralRoots (dirichletChar (realSlice v)) N).getD
        (k + (N : ℤ)).toNat 0 := by
    rw [muSeq_eq_candidate38 _ hv, criticalCandidate38, ite_eq_left ⟨hk₁, hk₂⟩]
  have he := hsort u huV hNu (k + (N : ℤ)).toNat (by omega)
  rw [← hval _ hNu, ← hval _ hN₀, muSeq_eq_gkMu38, muSeq_eq_gkMu38] at he
  simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using he

theorem dirichlet_real_path_continuous38 (u : PhysicalL2) (k : ℤ) :
    ContinuousOn (fun t : ℝ => gkMu (t • u) k) (Icc 0 1) :=
  ((continuous_gkMu38 k).comp (continuous_id.smul continuous_const)).continuousOn

end
end NlsGge.GK38
