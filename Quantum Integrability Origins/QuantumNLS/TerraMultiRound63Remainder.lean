import QuantumNLS.TerraMultiRound61RegularizedExpansion

/-! Scaling a little-oh remainder by the reciprocal of its reference power. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics MeasureTheory
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound59SignedCharges QuantumNLS.TerraMultiRound60Kernel
open QuantumNLS.TerraMultiRound61RegularizedExpansion QuantumNLS.FreeLimit
namespace QuantumNLS.TerraMultiRound63Remainder

theorem scaled_remainder (n : ℕ) (f : ℝ → ℝ)
    (h : f =o[atTop] (fun Y : ℝ => Y⁻¹ ^ n)) :
    Tendsto (fun Y : ℝ => Y ^ n * f Y) atTop (𝓝 0) := by
  have hd := h.tendsto_div_nhds_zero
  simpa only [div_eq_mul_inv, inv_pow, inv_inv, mul_comm] using hd

theorem scaled_bridge (s : ℕ) (D f P : ℝ → ℝ)
    (hD : ∀ᶠ Y : ℝ in atTop, D Y = Y * f Y)
    (h : (fun Y => f Y - P Y) =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2*s+1))) :
    Tendsto (fun Y : ℝ => Y^(2*s) * (D Y - Y * P Y)) atTop (𝓝 0) := by
  have hh := scaled_remainder (2*s+1) (fun Y => f Y - P Y) h
  apply hh.congr'
  filter_upwards [hD] with Y hY
  rw [hY, pow_succ]
  ring

theorem physical_scaled_remainder (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (s - 1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ x : Ell2, ∃ ha0 : 0 ≤ ((s - 1 : ℕ) : ℝ),
      fieldMap L (s - 1 : ℕ) ha0 x = u ∧
      Tendsto (fun Y : ℝ => Y^(2*s) *
        (((∫ t, kernel 0 Y t ∂(QuantumNLS.PhysicalQuantumMeasure.measure hκ u)) -
          (∫ t, kernel 0 Y t ∂(freeMeasure L u))) -
          Y * ∑ j ∈ Finset.Icc 1 s, (-1 : ℝ)^j *
            retainedR (L := L) s hs κ (physicalToHk (L := L) (s - 1) x) j *
              Y⁻¹^(2*j+1))) atTop (𝓝 0) := by
  obtain ⟨x, ha0, r, hx, hb, he⟩ := regularized_expansion L s hs κ hκ u hu
  refine ⟨x, ha0, hx, ?_⟩
  exact scaled_bridge s _ _ _ hb he

#print axioms physical_scaled_remainder
#print axioms scaled_remainder
#print axioms scaled_bridge
end QuantumNLS.TerraMultiRound63Remainder
