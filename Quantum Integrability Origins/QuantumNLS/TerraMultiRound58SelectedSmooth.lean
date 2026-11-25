import QuantumNLS.TerraMultiRound58ScalarSmooth
import QuantumNLS.TerraMultiRound58LittleO

/-! Transfer the smooth recursion to any eventually unique small branch. -/
set_option autoImplicit false
noncomputable section
open Complex ComplexConjugate MeasureTheory Finset Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound58SelectedSmooth
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiExpansions QuantumNLS.RiccatiODEConverse QuantumNLS.ClassicalCharges
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound41Coefficients QuantumNLS.TerraMultiRound43TwoSidedExpansion
open QuantumNLS.TerraMultiRound58ScalarSmooth QuantumNLS.TerraMultiRound58LittleO

/-- An eventually unique small branch has the scalar expansion with the literal
smooth recursive coefficients. -/
theorem selected_smooth_scalar_littleO (L : ℝ) [hLf : Fact (0 < L)] (a : ℝ)
    (ha : 1 / 2 < a) (κ : ℝ) (x : Ell2) (f : ℝ → ℂ)
    (hrep : physRep L a x = f) (hf : SmoothPeriodic L f) (r : ℝ → Ell2)
    (huniq : ∀ᶠ Y : ℝ in atTop, ∀ (hY : 0 < |Y|) (t : Ell2),
      ‖t‖ ≤ 2 * ‖x‖ / |Y| → physicalT hLf.out ha hY κ x t = t → t = r Y)
    (N : ℕ) (hN : 1 ≤ N) :
    (fun Y : ℝ => scalar L a x (r Y) - ∑ n ∈ Finset.Icc 1 N,
      coefficient L κ f n * ((Y : ℂ)⁻¹) ^ n) =o[atTop]
      (fun Y : ℝ => Y⁻¹ ^ N) := by
  obtain ⟨z, hz, _, hp, _⟩ := smooth_two_sided_expansion L ha κ f hf
  have he : z = x := physRep_injective hLf.out ha (hz.trans hrep.symm)
  subst z
  obtain ⟨B, C, hB, hb⟩ := hp N hN
  apply inverse_power_bound_littleO N _ ((L * physK L a ^ 2 * ‖x‖) * C)
  filter_upwards [huniq, eventually_ge_atTop B] with Y hYuniq hYB
  obtain ⟨hY, t, p, htn, ht, hpoint, herr⟩ := hb Y hYB
  have het : t = r Y := hYuniq (abs_pos.mpr hY.ne') t (by simpa [abs_of_pos hY] using htn) ht
  rw [← het, ← scalar_recursive_approximant L a κ x p f hf hrep N Y hpoint]
  have hc : 0 ≤ L * physK L a ^ 2 * ‖x‖ := by
    have hL : 0 < L := hLf.out
    positivity
  exact (scalar_approximation_bound L hLf.out ha x t p).trans (by
    calc
      (L * physK L a ^ 2 * ‖x‖) * ‖t - p‖ ≤
          (L * physK L a ^ 2 * ‖x‖) * (C * (Y ^ (N + 1))⁻¹) :=
        mul_le_mul_of_nonneg_left herr hc
      _ = _ := by ring)

#print axioms selected_smooth_scalar_littleO
end QuantumNLS.TerraMultiRound58SelectedSmooth
