import NlsGge.Measure.CountableSupport
import NlsGge.Sobolev.CMCoordinateSeries
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NlsGge.Pilot

variable {lower upper : ℝ}

/-- Each real coordinate direction contributes one half of the scalar Sobolev
weight after the identity inclusion from the CM weighted space to `E_s`. -/
theorem cmToFullWeightedHilbert_basis_norm_sq
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : 0 ≤ s)
    (p : ℤ × Fin 2) :
    ‖cmToFullWeightedHilbert c s hs
      (weightedRealHilbertBasis (cmModeWeight c) p)‖ ^ 2 =
      Real.rpow (japaneseBracket p.1) (-2 * s) / 2 := by
  rw [NlsGge.Pilot.cm_norm_coordinate_series]
  rw [weightedRealHilbertBasis_apply]
  rw [tsum_eq_single p.1]
  · rw [weightedRealBasisVector_apply]
    simp only [ite_true]
    rw [fullModeWeight, cmModeWeight]
    have he : ‖(Complex.orthonormalBasisOneI p.2 : ℂ)‖ = 1 :=
      Complex.orthonormalBasisOneI.orthonormal.norm_eq_one p.2
    have hsqrt : 0 < Real.sqrt (2 * sourceRate c p.1) :=
      Real.sqrt_pos.2 (mul_pos (by norm_num) (sourceRate_pos c p.1))
    have hnorm :
        ‖(Complex.orthonormalBasisOneI p.2 : ℂ) /
          (Real.sqrt (2 * sourceRate c p.1) : ℂ)‖ ^ 2 =
        1 / (2 * sourceRate c p.1) := by
      rw [norm_div, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt]
      rw [div_pow, one_pow, Real.sq_sqrt (mul_pos (by norm_num) (sourceRate_pos c p.1)).le]
    rw [hnorm]
    have hrate : 0 < sourceRate c p.1 := sourceRate_pos c p.1
    field_simp [hrate.ne']
    <;> ring
  · intro n hn
    rw [weightedRealBasisVector_apply]
    simp [hn]

/-- The complete real basis-image square sum is exactly the scalar Sobolev
weight sum. This is only the concrete basis sum; it makes no Gaussian or
generic Hilbert--Schmidt identification. -/
theorem cmToFullWeightedHilbert_basis_square_sum
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    HasSum
      (fun p : ℤ × Fin 2 =>
        ‖cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
          (weightedRealHilbertBasis (cmModeWeight c) p)‖ ^ 2)
      (∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s)) := by
  let f : ℤ × Fin 2 → ℝ := fun p =>
    ‖cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
      (weightedRealHilbertBasis (cmModeWeight c) p)‖ ^ 2
  have hfinite (n : ℤ) :
      HasSum (fun j : Fin 2 => f (n, j)) (Real.rpow (japaneseBracket n) (-2 * s)) := by
    convert (hasSum_fintype fun _ : Fin 2 =>
      Real.rpow (japaneseBracket n) (-2 * s) / 2) using 1
    · funext j
      exact cmToFullWeightedHilbert_basis_norm_sq c s (by linarith) (n, j)
    · simp [Fin.sum_univ_two]
      ring
  have hnonneg (p : ℤ × Fin 2) : 0 ≤ f p := sq_nonneg _
  have hfinite_summable (n : ℤ) : Summable (fun j : Fin 2 => f (n, j)) :=
    (hfinite n).summable
  have hbase_summable :
      Summable (fun n : ℤ => ∑' j : Fin 2, f (n, j)) := by
    apply (NlsGge.Measure.summable_japaneseBracket_sobolev_decay s hs).congr
    intro n
    exact (hfinite n).tsum_eq.symm
  have hproduct_summable : Summable f :=
    (summable_prod_of_nonneg hnonneg).2 ⟨hfinite_summable, hbase_summable⟩
  have htsum :
      ∑' p : ℤ × Fin 2, f p =
        ∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s) := by
    rw [hproduct_summable.tsum_prod' hfinite_summable]
    apply tsum_congr
    intro n
    exact (hfinite n).tsum_eq
  change HasSum f (∑' n : ℤ, Real.rpow (japaneseBracket n) (-2 * s))
  rw [← htsum]
  exact hproduct_summable.hasSum

theorem cmToFullWeightedHilbert_basis_square_summable
    (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s) :
    Summable (fun p : ℤ × Fin 2 =>
      ‖cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s))
        (weightedRealHilbertBasis (cmModeWeight c) p)‖ ^ 2) :=
  (cmToFullWeightedHilbert_basis_square_sum c s hs).summable

end NlsGge.Pilot

