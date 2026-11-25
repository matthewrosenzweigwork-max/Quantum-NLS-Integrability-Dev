import NlsGge.GK38.IsolatingBoundaryStability
import NlsGge.GK38.IsolatingGeometry

/-! GK I.12: fixed circles retain their counts near the base potential.
The common cutoff is directly re-certified for all four actual functions. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem fixed_family_local_counts38 (φ₀ : PotPair) (C : ℤ → ℂ) (R : ℤ → ℝ)
    (hfamily : IsolatingFamily38 φ₀ C R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ c : ℝ, ∃ N : ℕ, IsolatingGeometry38 C R c N ∧
      (∀ n : ℤ, |n| ≤ (N : ℤ) → ball (C n) (R n) ⊆ ball 0 (countingRadius38 N)) ∧
      ∀ φ ∈ ball φ₀ ρ,
        RootCountingAt38 (perChar φ) 2 N ∧ RootCountingAt38 (deriv (discrim φ)) 1 N ∧
        RootCountingAt38 (dirichletChar φ) 1 N ∧ RootCountingAt38 (neumannChar38 φ) 1 N ∧
        ∀ n : ℤ, (Lib.zeroMultiset (perChar φ) (ball (C n) (R n))).card = 2 ∧
          (Lib.zeroMultiset (dirichletChar φ) (ball (C n) (R n))).card = 1 ∧
          (Lib.zeroMultiset (neumannChar38 φ) (ball (C n) (R n))).card = 1 ∧
          (Lib.zeroMultiset (deriv (discrim φ)) (ball (C n) (R n))).card = 1 ∧
          ∀ z ∈ sphere (C n) (R n), perChar φ z ≠ 0 ∧ dirichletChar φ z ≠ 0 ∧
            neumannChar38 φ z ≠ 0 ∧ deriv (discrim φ) z ≠ 0 := by
  classical
  obtain ⟨c, N₀, hgeom, hspec⟩ := hfamily
  obtain ⟨L, hL, hfit⟩ := central_finite_fit38 C R c N₀ hgeom
  obtain ⟨Uc, hUc, N, hLN, hcount⟩ := common_counting_boundaries38 φ₀ L
  have hN₀N : N₀ ≤ N := hL.trans hLN
  have hgeomN : IsolatingGeometry38 C R c N := by
    refine ⟨hgeom.1, hgeom.2.1, hgeom.2.2.1, hgeom.2.2.2.1, ?_⟩
    intro n hn
    apply hgeom.2.2.2.2 n
    exact lt_of_le_of_lt (by exact_mod_cast hN₀N) hn
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  obtain ⟨Uf, hUf, hfinite⟩ := finite_boundary_stability38 φ₀ S C R
    (fun n _ => ⟨(hgeom.1 n).1, (hspec.1 n).2.2.2.2.2.2.2.2.2.2.2.2⟩)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem hUc hUf)
  refine ⟨ρ, hρ, c, N, hgeomN, (hfit N hLN).1, fun φ hφ => ?_⟩
  have hc := hcount φ (hball hφ).1
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, fun n => ?_⟩
  by_cases hn : |n| ≤ (N : ℤ)
  · have hnS : n ∈ S := Finset.mem_Icc.mpr (abs_le.mp hn)
    have hf := hfinite φ (hball hφ).2 n hnS
    exact ⟨hf.1.trans (hspec.1 n).2.2.2.2.2.2.2.2.1,
      hf.2.1.trans (hspec.1 n).2.2.2.2.2.2.2.2.2.1,
      hf.2.2.1.trans (hspec.1 n).2.2.2.2.2.2.2.2.2.2.1,
      hf.2.2.2.1.trans (hspec.1 n).2.2.2.2.2.2.2.2.2.2.2.1, hf.2.2.2.2⟩
  · have htail : (N : ℤ) < |n| := lt_of_not_ge hn
    obtain ⟨hC, hR, _⟩ := hgeomN.2.2.2.2 n htail
    rw [hC, hR]
    exact ⟨hc.1.2.2.2.2.1 n htail, hc.2.2.1.2.2.2.2.1 n htail,
      hc.2.2.2.1.2.2.2.2.1 n htail, hc.2.1.2.2.2.2.1 n htail,
      fun z hz => let hb := hc.2.2.2.2 n htail z hz; ⟨hb.1, hb.2.2.1, hb.2.2.2, hb.2.1⟩⟩

end
end NlsGge.GK38
