import QuantumNLS.Local001DiagonalB

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
open QuantumNLS.LocalSpectral
variable (L : ℝ) [Fact (0 < L)]

theorem summable_mul_le_sqrt_tsum {a b : ℤ → ℝ}
    (ha0 : ∀ k, 0 ≤ a k) (hb0 : ∀ k, 0 ≤ b k)
    (ha : Summable fun k => a k ^ (2 : ℝ)) (hb : Summable fun k => b k ^ (2 : ℝ)) :
    Summable (fun k => a k * b k) ∧
      ∑' k, a k * b k ≤ Real.sqrt (∑' k, a k ^ (2 : ℝ)) *
        Real.sqrt (∑' k, b k ^ (2 : ℝ)) := by
  obtain ⟨hs, hle⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    (p := 2) (q := 2) Real.HolderConjugate.two_two ha0 hb0 ha hb
  refine ⟨hs, ?_⟩
  simpa [Real.sqrt_eq_rpow] using hle


#print axioms summable_mul_le_sqrt_tsum

def denominatorMajorant (r : ℝ) (k : ℤ) : ℝ :=
  (spacing L * |(k : ℝ)| - r)⁻¹ ^ 2


#print axioms denominatorMajorant

theorem sourceMode_distance_lower (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ} (hr : 0 < r)
    (hsmall : r < spacing L / 2) (hz : OnGamma L r n z) (j : Fin 2) (k : ℤ) :
    spacing L * |(k : ℝ)| - r ≤
      ‖z - (LocalSpectral.pm L (sourceMode n (j, k)) : ℂ)‖ := by
  have h := contour_distance_lower hL (n := n) (k := sourceModeIndex j k) hz
  fin_cases j <;> simpa [sourceMode, sourceModeIndex] using h


#print axioms sourceMode_distance_lower

theorem freeResolventMultiplier_sq_le_majorant (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z)
    (i : Fin 2 × ℤ) :
    ‖freeResolventMultiplier L n z i‖ ^ 2 ≤ denominatorMajorant L r i.2 := by
  rcases i with ⟨j, k⟩
  by_cases hk : k = 0
  · subst k
    have hz0 : ‖z - (LocalSpectral.pm L n : ℂ)‖ = r := hz
    have hpm : sourceMode n (j, 0) = n := by simp [sourceMode, sourceModeIndex]
    rw [freeResolventMultiplier, hpm, norm_inv, denominatorMajorant]
    rw [hz0]
    simp [spacing, hr.ne']
  · have hdist := sourceMode_distance_lower L hL n hr hsmall hz j k
    have hdistpos : 0 < ‖z - (LocalSpectral.pm L (sourceMode n (j, k)) : ℂ)‖ :=
      lt_of_lt_of_le hr (contour_denominator_lower hL hsmall hz (sourceMode_parity n (j, k)))
    have hkabs : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hd : 0 < spacing L := spacing_pos (L := L) hL
    have hminor : 0 < spacing L * |(k : ℝ)| - r := by
      have hgap : r < spacing L := by linarith
      have hmul : spacing L ≤ spacing L * |(k : ℝ)| := by
        calc
          spacing L = spacing L * 1 := by ring
          _ ≤ spacing L * |(k : ℝ)| := mul_le_mul_of_nonneg_left hkabs hd.le
      linarith
    have hinv : ‖z - (LocalSpectral.pm L (sourceMode n (j, k)) : ℂ)‖⁻¹ ≤
        (spacing L * |(k : ℝ)| - r)⁻¹ :=
      (inv_le_inv₀ hdistpos hminor).2 hdist
    rw [freeResolventMultiplier, norm_inv, denominatorMajorant]
    exact (sq_le_sq₀ (by positivity) (by positivity)).2 hinv


#print axioms freeResolventMultiplier_sq_le_majorant

theorem denominatorMajorant_summable (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hsmall : r < spacing L / 2) : Summable (denominatorMajorant L r) := by
  exact QuantumNLS.ResetFreeResolventLOCAL001.denominatorMajorant_summable hL hr hsmall


#print axioms denominatorMajorant_summable

theorem denominatorMajorant_tsum_eq_source (hL : 0 < L) {r : ℝ} (hr : 0 < r)
    (hsmall : r < spacing L / 2) :
    ∑' k : ℤ, denominatorMajorant L r k =
      r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2 := by
  exact QuantumNLS.ResetFreeResolventLOCAL001.denominatorMajorant_tsum_eq_source hL hr hsmall


#print axioms denominatorMajorant_tsum_eq_source

theorem freeResolventMultiplier_sq_summable_bound (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z) (j : Fin 2) :
    Summable (fun k : ℤ => ‖freeResolventMultiplier L n z (j, k)‖ ^ 2) ∧
      ∑' k : ℤ, ‖freeResolventMultiplier L n z (j, k)‖ ^ 2 ≤
        r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2 := by
  have hmajor := denominatorMajorant_summable L hL hr hsmall
  have hsq : Summable (fun k : ℤ => ‖freeResolventMultiplier L n z (j, k)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => freeResolventMultiplier_sq_le_majorant L hL n hr hsmall hz (j, k)) hmajor
  refine ⟨hsq, ?_⟩
  calc
    ∑' k : ℤ, ‖freeResolventMultiplier L n z (j, k)‖ ^ 2 ≤
        ∑' k : ℤ, denominatorMajorant L r k :=
          hsq.tsum_le_tsum (fun k => freeResolventMultiplier_sq_le_majorant L hL n hr hsmall hz (j, k)) hmajor
    _ = r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2 :=
      denominatorMajorant_tsum_eq_source L hL hr hsmall


#print axioms freeResolventMultiplier_sq_summable_bound

theorem freeResolventCoefficient_l1 (hL : 0 < L) (n : ℤ) {r : ℝ} {z : ℂ}
    (hr : 0 < r) (hsmall : r < spacing L / 2) (hz : OnGamma L r n z)
    (f : VectorInterval L) (j : Fin 2) :
    Summable (fun k : ℤ => ‖freeResolventMultiplier L n z (j, k) *
      ⟪vectorModeBasis L n (j, k), f⟫_ℂ‖) ∧
      ∑' k : ℤ, ‖freeResolventMultiplier L n z (j, k) *
        ⟪vectorModeBasis L n (j, k), f⟫_ℂ‖ ≤
        Real.sqrt (r⁻¹ ^ 2 + 2 * ∑' k : ℕ+,
          (spacing L * (k : ℝ) - r)⁻¹ ^ 2) *
          ‖vectorToComponentsLinear L f j‖ := by
  let a : ℤ → ℝ := fun k => ‖freeResolventMultiplier L n z (j, k)‖
  let c : ℤ → ℝ := fun k => ‖⟪intervalShiftedBasis L (componentShift n j) k,
    vectorToComponentsLinear L f j⟫_ℂ‖
  have hm := freeResolventMultiplier_sq_summable_bound L hL n hr hsmall hz j
  have ha : Summable (fun k : ℤ => a k ^ (2 : ℝ)) := by
    simpa [a, Real.rpow_two] using hm.1
  have haBound : ∑' k : ℤ, a k ^ (2 : ℝ) ≤
      r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2 := by
    simpa [a, Real.rpow_two] using hm.2
  have hparseval := QuantumNLS.HilbertDiagOp.parseval_hasSum
    (intervalShiftedBasis L (componentShift n j)) (vectorToComponentsLinear L f j)
  have hc : Summable (fun k : ℤ => c k ^ (2 : ℝ)) := by
    simpa [c, Real.rpow_two] using hparseval.summable
  have hcTsum : ∑' k : ℤ, c k ^ (2 : ℝ) =
      ‖vectorToComponentsLinear L f j‖ ^ 2 := by
    simpa [c, Real.rpow_two] using hparseval.tsum_eq
  have hholder := summable_mul_le_sqrt_tsum
    (fun k => norm_nonneg _) (fun k => norm_nonneg _) ha hc
  have hcoeff : ∀ k : ℤ, ⟪vectorModeBasis L n (j, k), f⟫_ℂ =
      ⟪intervalShiftedBasis L (componentShift n j) k,
        vectorToComponentsLinear L f j⟫_ℂ :=
    fun k => vectorModeBasis_inner_component L n j k f
  have hsum : Summable (fun k : ℤ => ‖freeResolventMultiplier L n z (j, k) *
      ⟪vectorModeBasis L n (j, k), f⟫_ℂ‖) := by
    refine hholder.1.congr ?_
    intro k
    simp [a, c, norm_mul, hcoeff k]
  refine ⟨hsum, ?_⟩
  have htsum : (∑' k : ℤ, ‖freeResolventMultiplier L n z (j, k) *
      ⟪vectorModeBasis L n (j, k), f⟫_ℂ‖) = ∑' k : ℤ, a k * c k := by
    apply tsum_congr
    intro k
    simp [a, c, norm_mul, hcoeff k]
  rw [htsum]
  calc
    ∑' k : ℤ, a k * c k ≤
        Real.sqrt (∑' k : ℤ, a k ^ (2 : ℝ)) *
          Real.sqrt (∑' k : ℤ, c k ^ (2 : ℝ)) := hholder.2
    _ ≤ Real.sqrt (r⁻¹ ^ 2 + 2 * ∑' k : ℕ+,
          (spacing L * (k : ℝ) - r)⁻¹ ^ 2) *
          ‖vectorToComponentsLinear L f j‖ := by
      rw [hcTsum, Real.sqrt_sq (norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt haBound) (norm_nonneg _)




#print axioms freeResolventCoefficient_l1

end QuantumNLS.ResetFreeResolventLOCAL001.CompletionB
