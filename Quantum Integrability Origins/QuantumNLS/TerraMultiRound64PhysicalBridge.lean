import QuantumNLS.TerraMultiRound63Remainder
import QuantumNLS.TerraMultiRound62EqualMass
import QuantumNLS.TerraMultiRound64LimitBridge

/-! Specialize finite-division extraction to the actual physical and free measures. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.FreeLimit
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound59SignedCharges QuantumNLS.TerraMultiRound60Kernel
open QuantumNLS.TerraMultiRound63Remainder QuantumNLS.TerraMultiRound62EqualMass
open QuantumNLS.TerraMultiRound64LimitBridge
namespace QuantumNLS.TerraMultiRound64PhysicalBridge

theorem physical_limit_from_lower_moments (L : ℝ) [Fact (0 < L)] (n : ℕ) (hs : 2 ≤ n+1)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (n : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ x : Ell2, ∃ ha0 : 0 ≤ ((n : ℕ) : ℝ), fieldMap L n ha0 x = u ∧
      ((∀ j < n+1, Integrable (fun t : ℝ => t^(2*j)) (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) →
      (∀ j < n+1, Integrable (fun t : ℝ => t^(2*j)) (freeMeasure L u)) →
      (∀ j, 1 ≤ j → j < n+1 →
        (∫ t : ℝ, t^(2*j) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
        (∫ t : ℝ, t^(2*j) ∂(freeMeasure L u)) =
          retainedR (L := L) (n+1) hs κ (physicalToHk (L := L) (n+1-1) x) j) →
      Tendsto (fun Y : ℝ => (∫ t, kernel (n+1) Y t ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
        (∫ t, kernel (n+1) Y t ∂(freeMeasure L u))) atTop
        (𝓝 (retainedR (L := L) (n+1) hs κ (physicalToHk (L := L) (n+1-1) x) (n+1)))) := by
  have hu' : hsq L ((n+1)-1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤ := by simpa using hu
  obtain ⟨x, ha0, hx, hr⟩ := physical_scaled_remainder L (n+1) hs κ hκ u hu'
  simp only [Nat.add_sub_cancel] at ha0 hx hr
  refine ⟨x, ha0, hx, ?_⟩
  intro hμ hν hcoeff
  let R : ℕ → ℝ := fun j => if j = 0 then 0 else retainedR (L := L) (n+1) hs κ (physicalToHk (L := L) (n+1-1) x) j
  have hR0 : R 0 = 0 := by simp [R]
  have hc : ∀ j < n+1, (∫ t : ℝ, t^(2*j) ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
      (∫ t : ℝ, t^(2*j) ∂(freeMeasure L u)) = R j := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simpa only [hR0] using physical_free_mass hκ u
    · simpa only [R, hj0, ↓reduceIte] using hcoeff j (by omega) hj
  have hrem : Tendsto (fun Y : ℝ => Y^(2*(n+1)) *
      (((∫ t, kernel 0 Y t ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
        (∫ t, kernel 0 Y t ∂(freeMeasure L u))) -
        Y * ∑ j ∈ Finset.Icc 1 (n+1), (-1 : ℝ)^j * R j * Y⁻¹^(2*j+1))) atTop (𝓝 0) := by
    apply hr.congr'
    filter_upwards with Y
    congr 2
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj0 : j ≠ 0 := by have := Finset.mem_Icc.mp hj; omega
    simp only [R, hj0, ↓reduceIte]
  have hz := difference_limit_from_lower_moments (QuantumNLS.PhysicalQuantumMeasure.measure hκ u)
    (freeMeasure L u) n R hR0 hμ hν hc hrem
  simpa only [R, Nat.succ_ne_zero, ↓reduceIte] using hz

#print axioms physical_limit_from_lower_moments
end QuantumNLS.TerraMultiRound64PhysicalBridge
