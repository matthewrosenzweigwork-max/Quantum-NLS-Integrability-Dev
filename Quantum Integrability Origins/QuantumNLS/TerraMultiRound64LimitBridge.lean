import QuantumNLS.TerraMultiRound63Division
import QuantumNLS.TerraMultiRound64ExpansionTerm

/-! Extract a regularized difference from a scaled retained expansion. -/
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
namespace QuantumNLS.TerraMultiRound64LimitBridge
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61FiniteDivision
open QuantumNLS.TerraMultiRound63Division QuantumNLS.TerraMultiRound64ExpansionTerm

theorem difference_limit_from_lower_moments (μ ν : Measure ℝ) (n : ℕ) (R : ℕ → ℝ)
    (hR0 : R 0 = 0)
    (hμ : ∀ j < n+1, Integrable (fun t : ℝ => t^(2*j)) μ)
    (hν : ∀ j < n+1, Integrable (fun t : ℝ => t^(2*j)) ν)
    (hcoeff : ∀ j < n+1, (∫ t : ℝ, t^(2*j) ∂μ) -
      (∫ t : ℝ, t^(2*j) ∂ν) = R j)
    (hrem : Tendsto (fun Y : ℝ => Y^(2*(n+1)) *
      (((∫ t, kernel 0 Y t ∂μ) - (∫ t, kernel 0 Y t ∂ν)) -
       Y * ∑ j ∈ Finset.Icc 1 (n+1), (-1 : ℝ)^j * R j * Y⁻¹^(2*j+1)))
      atTop (𝓝 0)) :
    Tendsto (fun Y : ℝ => (∫ t, kernel (n+1) Y t ∂μ) -
      (∫ t, kernel (n+1) Y t ∂ν)) atTop (𝓝 (R (n+1))) := by
  have hlim := hrem.const_mul ((-1 : ℝ)^(n+1))
  have hlim' : Tendsto (fun Y : ℝ => R (n+1) + (-1 : ℝ)^(n+1) *
      (Y^(2*(n+1)) * (((∫ t, kernel 0 Y t ∂μ) - (∫ t, kernel 0 Y t ∂ν)) -
       Y * ∑ j ∈ Finset.Icc 1 (n+1), (-1 : ℝ)^j * R j * Y⁻¹^(2*j+1))))
      atTop (𝓝 (R (n+1))) := by
    simpa using tendsto_const_nhds.add hlim
  apply hlim'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  let c : ℕ → ℝ := fun j => (∫ t : ℝ, t^(2*j) ∂μ) - (∫ t : ℝ, t^(2*j) ∂ν)
  let d := dividedDifference μ ν Y
  let e := d 0 - Y * ∑ j ∈ Finset.Icc 1 (n+1), (-1 : ℝ)^j * R j * Y⁻¹^(2*j+1)
  have hd : ∀ k, d (k+1) = Y^2 * (c k - d k) := by
    intro k
    dsimp [d, dividedDifference, c]
    ring
  have hc : ∑ j ∈ Finset.range (n+1), (-(Y^2))⁻¹^j * c j =
      ∑ j ∈ Finset.range (n+1), (-(Y^2))⁻¹^j * R j := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [show c j = R j from hcoeff j (Finset.mem_range.mp hj)]
  have he : d 0 - ∑ j ∈ Finset.range (n+1), (-(Y^2))⁻¹^j * c j =
      (-(Y^2))⁻¹^(n+1) * R (n+1) + e := by
    dsimp only [e]
    rw [expansion_sum Y (ne_of_gt hY) (n+1) R hR0, hc,
      Finset.sum_range_succ (fun j => (-(Y^2))⁻¹^j * R j) (n+1)]
    ring
  have hx := correction_from_expansion (Y^2) (by positivity) c d hd n (R (n+1)) e he
  rw [show d (n+1) = (∫ t, kernel (n+1) Y t ∂μ) -
      (∫ t, kernel (n+1) Y t ∂ν) from finite_division μ ν Y hY (n+1) hμ hν] at hx
  dsimp only [e, d, dividedDifference] at hx
  rw [hx, neg_pow, pow_mul]
  ring

#print axioms difference_limit_from_lower_moments
end QuantumNLS.TerraMultiRound64LimitBridge
