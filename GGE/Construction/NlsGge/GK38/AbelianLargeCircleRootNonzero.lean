import NlsGge.GK38.AbelianActualLargeCircleRootGrowth
import NlsGge.GK38.Lib.EntireProductsC34a
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! Genuine large-circle nonzero denominators before quotient asymptotics. -/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6LargeCircle_sin_ne_zero38 (ν : ℕ) (z : ℂ)
    (hz : ‖z‖=ν*Real.pi+Real.pi/2) : Complex.sin z ≠ 0 := by
  intro hs
  obtain ⟨m,hm⟩ := Complex.sin_eq_zero_iff.mp hs
  exact Lib.circle_no_lattice hz m hm.symm

theorem p6Actual_large_circle_root_lower_nonzero38 (φ : PotPair) (hφ : φ ∈ gkW) :
    ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ z : ℂ,
      ‖z‖=ν*Real.pi+Real.pi/2 →
      ‖Complex.sin z‖ ≤ ‖canonRoot38 φ z‖ ∧ canonRoot38 φ z ≠ 0 := by
  obtain ⟨N,hN⟩ := p6Actual_canonical_root_large_circle_growth38 φ hφ 1 zero_lt_one
  refine ⟨N,fun ν hν z hz => ?_⟩
  have herr : ‖canonRoot38 φ z+2*Complex.I*Complex.sin z‖ ≤ ‖Complex.sin z‖ := by
    simpa only [one_mul] using hN ν hν z hz
  have htri : 2*‖Complex.sin z‖ ≤
      ‖canonRoot38 φ z+2*Complex.I*Complex.sin z‖+‖canonRoot38 φ z‖ := by
    calc
      _ = ‖2*Complex.I*Complex.sin z‖ := by norm_num [norm_mul]
      _ = ‖(canonRoot38 φ z+2*Complex.I*Complex.sin z)-canonRoot38 φ z‖ := by
        congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hlower : ‖Complex.sin z‖ ≤ ‖canonRoot38 φ z‖ := by linarith
  refine ⟨hlower,norm_pos_iff.mp ?_⟩
  exact (norm_pos_iff.mpr (p6LargeCircle_sin_ne_zero38 ν z hz)).trans_le hlower

end
end NlsGge.GK38
