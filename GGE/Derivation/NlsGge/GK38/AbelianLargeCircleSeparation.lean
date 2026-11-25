import NlsGge.GK38.Lib.EntireProductsGrowth

/-! The midpoint-circle separation in the proof of book Proposition 14.11.
The radius is exactly nu*pi+pi/2; all signed spectral labels are simultaneous.
An actual square-summable deviation is the only mathematical hypothesis. -/
set_option autoImplicit false
open Filter Topology
namespace NlsGge.GK38
noncomputable section

theorem p6LargeCircle_eventual_separation38 (σ : ℤ → ℂ)
    (hσ : Summable (fun m : ℤ => ‖σ m-(m : ℂ)*(Real.pi : ℂ)‖^2)) :
    ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ z : ℂ,
      ‖z‖=ν*Real.pi+Real.pi/2 → ∀ m : ℤ,
      (Real.pi/2)*Lib.circDist ν m ≤ ‖σ m-z‖ := by
  obtain ⟨N,hN⟩ := Lib.circle_sum_bound hσ (half_pos Real.pi_pos)
  refine ⟨N,fun ν hν z hz m => ?_⟩
  have hsingle := hN ν hν ({m} : Finset ℤ)
  simp only [Finset.sum_singleton] at hsingle
  have hdev : ‖σ m-(m : ℂ)*(Real.pi : ℂ)‖ ≤
      (Real.pi/2)*Lib.circDist ν m := by
    exact (div_le_iff₀ (Lib.circDist_pos ν m)).mp hsingle
  have htri : ‖(m : ℂ)*(Real.pi : ℂ)-z‖ ≤
      ‖σ m-(m : ℂ)*(Real.pi : ℂ)‖+‖σ m-z‖ := by
    calc
      _ = ‖((m : ℂ)*(Real.pi : ℂ)-σ m)+(σ m-z)‖ := by congr 1; ring
      _ ≤ ‖(m : ℂ)*(Real.pi : ℂ)-σ m‖+‖σ m-z‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev ( (m : ℂ)*(Real.pi : ℂ)) (σ m)]
  have hcounting := Lib.pi_mul_dd_le hz m
  nlinarith

theorem p6LargeCircle_eventual_nonzero38 (σ : ℤ → ℂ)
    (hσ : Summable (fun m : ℤ => ‖σ m-(m : ℂ)*(Real.pi : ℂ)‖^2)) :
    ∃ N : ℕ, ∀ ν : ℕ, N ≤ ν → ∀ z : ℂ,
      ‖z‖=ν*Real.pi+Real.pi/2 → ∀ m : ℤ, σ m-z ≠ 0 := by
  obtain ⟨N,hN⟩ := p6LargeCircle_eventual_separation38 σ hσ
  refine ⟨N,fun ν hν z hz m => ?_⟩
  have hp : 0 < (Real.pi/2)*Lib.circDist ν m :=
    mul_pos (half_pos Real.pi_pos) (Lib.circDist_pos ν m)
  exact norm_pos_iff.mp (hp.trans_le (hN ν hν z hz m))

end
end NlsGge.GK38
