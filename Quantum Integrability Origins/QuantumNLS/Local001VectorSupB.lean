import QuantumNLS.Local001SeriesRepB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable (L : ℝ) [Fact (0 < L)]

theorem freeDiagonal_ae_sup_bound (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z)
    (f : VectorInterval L) :
    ∀ᵐ (x : ℝ) ∂μI L,
      ‖freeDiagonalResolvent L hL n hr hsmall hz f x‖ ≤
        Real.sqrt (resolventConstantSq L r) * ‖f‖ := by
  have h0 := freeDiagonal_component_ae_bound L hL n hr hsmall hz f 0
  have h1 := freeDiagonal_component_ae_bound L hL n hr hsmall hz f 1
  have hcoords : ∀ᵐ (x : ℝ) ∂μI L,
      vectorToComponentsLinear L (freeDiagonalResolvent L hL n hr hsmall hz f) 0 x =
        (freeDiagonalResolvent L hL n hr hsmall hz f x) 0 ∧
      vectorToComponentsLinear L (freeDiagonalResolvent L hL n hr hsmall hz f) 1 x =
        (freeDiagonalResolvent L hL n hr hsmall hz f x) 1 := by
    have h0' := (fiberCoordinate (0 : Fin 2)).coeFn_compLp
      (freeDiagonalResolvent L hL n hr hsmall hz f)
    have h1' := (fiberCoordinate (1 : Fin 2)).coeFn_compLp
      (freeDiagonalResolvent L hL n hr hsmall hz f)
    filter_upwards [h0', h1'] with x hx0 hx1
    exact ⟨hx0, hx1⟩
  have hinputNorm :
      ‖vectorToComponentsLinear L f 0‖ ^ 2 +
        ‖vectorToComponentsLinear L f 1‖ ^ 2 = ‖f‖ ^ 2 := by
    have hnorm := (vectorComponentsIsometry L).norm_map f
    have hsq := congrArg (fun t : ℝ => t ^ 2) hnorm
    rw [PiLp.norm_sq_eq_of_L2] at hsq
    simpa [vectorComponentsIsometry, vectorComponentsEquiv, Fin.sum_univ_two] using hsq
  have hconstant : 0 ≤ Real.sqrt (resolventConstantSq L r) := Real.sqrt_nonneg _
  have hscale : (Real.sqrt L)⁻¹ *
      Real.sqrt (r⁻¹ ^ 2 + 2 * ∑' k : ℕ+,
        (spacing L * (k : ℝ) - r)⁻¹ ^ 2) = Real.sqrt (resolventConstantSq L r) := by
    rw [resolventConstantSq]
    let S : ℝ := r⁻¹ ^ 2 + 2 * ∑' k : ℕ+,
      (spacing L * (k : ℝ) - r)⁻¹ ^ 2
    have hS : 0 ≤ S := by
      dsimp [S]
      exact add_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
        (tsum_nonneg fun _ => sq_nonneg _))
    have hL2 : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL.le
    have hS2 : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS
    have htarget : 0 ≤ L⁻¹ * S := mul_nonneg (inv_nonneg.mpr hL.le) hS
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
    rw [mul_pow, inv_pow, hL2, hS2, Real.sq_sqrt htarget]
  filter_upwards [h0, h1, hcoords] with x hx0 hx1 hcoord
  have hn0 := hx0
  have hn1 := hx1
  rw [hscale] at hn0 hn1
  rw [hcoord.1] at hn0
  rw [hcoord.2] at hn1
  have hsq0 :
      ‖(freeDiagonalResolvent L hL n hr hsmall hz f x) 0‖ ^ 2 ≤
        (Real.sqrt (resolventConstantSq L r) *
          ‖vectorToComponentsLinear L f 0‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hn0
  have hsq1 :
      ‖(freeDiagonalResolvent L hL n hr hsmall hz f x) 1‖ ^ 2 ≤
        (Real.sqrt (resolventConstantSq L r) *
          ‖vectorToComponentsLinear L f 1‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hn1
  have hsum : ‖freeDiagonalResolvent L hL n hr hsmall hz f x‖ ^ 2 ≤
      (Real.sqrt (resolventConstantSq L r) * ‖f‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    calc
      ‖(freeDiagonalResolvent L hL n hr hsmall hz f x) 0‖ ^ 2 +
          ‖(freeDiagonalResolvent L hL n hr hsmall hz f x) 1‖ ^ 2 ≤
          (Real.sqrt (resolventConstantSq L r) *
              ‖vectorToComponentsLinear L f 0‖) ^ 2 +
            (Real.sqrt (resolventConstantSq L r) *
              ‖vectorToComponentsLinear L f 1‖) ^ 2 :=
        add_le_add hsq0 hsq1
      _ = (Real.sqrt (resolventConstantSq L r)) ^ 2 *
          (‖vectorToComponentsLinear L f 0‖ ^ 2 +
            ‖vectorToComponentsLinear L f 1‖ ^ 2) := by ring
      _ = (Real.sqrt (resolventConstantSq L r) * ‖f‖) ^ 2 := by
        rw [hinputNorm, mul_pow]
  exact QuantumNLS.HilbertDiagOp.le_of_sq_le_sq_nonneg
    (mul_nonneg hconstant (norm_nonneg _)) hsum


#print axioms freeDiagonal_ae_sup_bound

theorem sourceResolvent_norm_le_of_isResolvent (hL : 0 < L) (κ : ℝ) (n : ℤ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hsmall : r < spacing L / 2)
    (hz : OnGamma L r n z) {R : VectorInterval L →L[ℂ] VectorInterval L}
    (hR : LocalSpectral.IsResolvent L κ (fun _ => 0) (LocalSpectral.parity n) z R) :
    ‖R‖ ≤ r⁻¹ := by
  rw [sourceResolvent_eq_freeDiagonal L hL κ n hr hsmall hz hR]
  exact freeDiagonalResolvent_norm_le L hL n hr hsmall hz


#print axioms sourceResolvent_norm_le_of_isResolvent

theorem sourceResolvent_ae_sup_bound_of_isResolvent (hL : 0 < L) (κ : ℝ) (n : ℤ)
    {r : ℝ} {z : ℂ} (hr : 0 < r) (hsmall : r < spacing L / 2)
    (hz : OnGamma L r n z) {R : VectorInterval L →L[ℂ] VectorInterval L}
    (hR : LocalSpectral.IsResolvent L κ (fun _ => 0) (LocalSpectral.parity n) z R)
    (f : VectorInterval L) :
    ∀ᵐ (x : ℝ) ∂μI L, ‖R f x‖ ≤ resolventConstant L r * ‖f‖ := by
  have hEq := sourceResolvent_eq_freeDiagonal L hL κ n hr hsmall hz hR
  rw [hEq]
  simpa [resolventConstant, resolventConstantSq] using
    freeDiagonal_ae_sup_bound L hL n hr hsmall hz f




#print axioms sourceResolvent_ae_sup_bound_of_isResolvent

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
