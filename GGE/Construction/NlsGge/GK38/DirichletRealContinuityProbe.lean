import NlsGge.GK38.DirichletRealContinuity

/-! Checks of free normalization, negative order, and genuinely prescribed q=1 windows. -/
set_option autoImplicit false
open Filter Topology Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem gkMu_free38 (n : ℤ) : gkMu 0 n = (n : ℝ) * Real.pi := by
  simp only [gkMu, realSlice_zero, muSeq_zero38, countingCenter_re38]

theorem dirichlet_negative_order_probe38 (u : PhysicalL2) : gkMu u (-1) < gkMu u 0 :=
  gkMu_strictMono38 u (by norm_num)

theorem dirichlet_prescribed_window_probe38 (u : PhysicalL2) (L : ℕ) :
    ∃ N : ℕ, L ≤ N ∧ RootCountingAt38 (dirichletChar (realSlice u)) 1 N := by
  obtain ⟨U, hU, N, hN, h⟩ := dirichlet_large_counting_cutoff38 (realSlice u) L
  exact ⟨N, hN, h _ (mem_of_mem_nhds hU)⟩

end
end NlsGge.GK38
