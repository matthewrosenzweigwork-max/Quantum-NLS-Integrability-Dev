import QuantumNLS.Prop020Diag
import QuantumNLS.RootMeasureTransfer

/-!
# PROP-020 (`Q7A:thm:main`), input 3: the vector-level steps of the proof

Source: proof of `Q7A:thm:main`: "Let `Φ_N` be [the normalization of `P_N u^{⊗N}`]. Then `‖Φ_N − u^{⊗N}‖ ≤ 2√P(𝓔_Nᶜ)`. ...
All these operators share their spectral resolution, so the inequality `|e^{−ix} − e^{−iy}| ≤ |x − y|` gives the same Hilbert-norm
error for the time-one evolutions. ... partial trace is contractive and, for normalized vectors `v, w`,
`‖|v⟩⟨v| − |w⟩⟨w|‖₁ ≤ 2‖v − w‖`."

* `norm_exp_sub_le`: `|e^{−ix} − e^{−iy}| ≤ |x − y|`;
* `diag_apply_le`: a diagonal operator whose eigenvalues are `≤ δ` on `S` maps a vector supported on `S` into norm `≤ δ‖φ‖`;
* `normalize_proj`: the normalized projection `Φ = Pw/‖Pw‖` satisfies `‖Φ − w‖ ≤ 2‖(1 − P)w‖`;
* `traceNorm_gamma_sub_le`: `‖γ^{(k)}_x − γ^{(k)}_y‖₁ ≤ 2‖x − y‖` for unit vectors.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace QuantumNLS.Prop020Vector

/-- `|e^{−ix} − e^{−iy}| ≤ |x − y|`. -/
theorem norm_exp_sub_le (x y : ℝ) :
    ‖Complex.exp (-(x : ℂ) * Complex.I) - Complex.exp (-(y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  have e : Complex.exp (-(x : ℂ) * Complex.I) - Complex.exp (-(y : ℂ) * Complex.I) =
      Complex.exp (-(y : ℂ) * Complex.I) * (Complex.exp (Complex.I * ((y - x : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [e, norm_mul]
  have h1 : ‖Complex.exp (-(y : ℂ) * Complex.I)‖ = 1 := by
    rw [show -(y : ℂ) * Complex.I = ((-y : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [h1, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := y - x)).trans ?_
  rw [Real.norm_eq_abs, abs_sub_comm]

section Hilbert

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A diagonal operator with eigenvalues `≤ δ` on `S`, applied to a vector supported on `S`. -/
theorem diag_apply_le (b : HilbertBasis ι ℂ E) (D : E →L[ℂ] E) (μ : ι → ℂ) (hD : ∀ i, D (b i) = μ i • b i)
    (S : Set ι) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ i ∈ S, ‖μ i‖ ≤ δ) (φ : E) (hφ : ∀ i ∉ S, ⟪b i, φ⟫_ℂ = 0) :
    ‖D φ‖ ≤ δ * ‖φ‖ := by
  classical
  have h1 := QuantumNLS.RootMeasureTransfer.hasSum_norm_sq_diag b D μ hD 0 φ
  have h2 := (QuantumNLS.RootMeasureTransfer.hasSum_norm_sq b φ).mul_right (δ ^ 2)
  have hle := hasSum_le (fun i => ?_) h1 h2
  · have e : (D - (0 : ℂ) • (1 : E →L[ℂ] E)) φ = D φ := by simp
    rw [e] at hle
    have hsq : ‖D φ‖ ^ 2 ≤ (δ * ‖φ‖) ^ 2 := by rw [mul_pow]; linarith [hle]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 hsq
  · by_cases hi : i ∈ S
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [sub_zero]
      exact pow_le_pow_left₀ (norm_nonneg _) (hδ i hi) 2
    · rw [hφ i hi, norm_zero]
      simp

/-- The normalized projection: `Φ = Pw/‖Pw‖` is a unit vector with `‖Φ − w‖ ≤ 2‖w − Pw‖`. -/
theorem normalize_proj (P : E →L[ℂ] E) (w : E) (hw : ‖w‖ = 1) (hP : ‖w - P w‖ < 1) :
    ‖P w‖ ≠ 0 ∧ ‖(‖P w‖⁻¹ : ℂ) • P w‖ = 1 ∧ ‖(‖P w‖⁻¹ : ℂ) • P w - w‖ ≤ 2 * ‖w - P w‖ := by
  have h1 : 1 - ‖w - P w‖ ≤ ‖P w‖ := by
    have := norm_sub_norm_le w (w - P w)
    rw [sub_sub_cancel, hw] at this; linarith
  have hpos : 0 < ‖P w‖ := by linarith
  refine ⟨hpos.ne', ?_, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hpos.ne']
  · have e : (‖P w‖⁻¹ : ℂ) • P w - w = ((‖P w‖⁻¹ : ℂ) - 1) • P w + (P w - w) := by
      rw [sub_smul, one_smul]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_sub_rev (P w) w]
    have h2 : ‖((‖P w‖⁻¹ : ℂ) - 1)‖ * ‖P w‖ = |1 - ‖P w‖| := by
      have : ((‖P w‖⁻¹ : ℂ) - 1) = (((‖P w‖⁻¹ - 1 : ℝ)) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, ← abs_of_pos hpos, ← abs_mul, abs_of_pos hpos]
      congr 1; field_simp
    have h3 : ‖P w‖ ≤ 1 + ‖w - P w‖ := by
      have := norm_sub_le w (w - P w); rw [sub_sub_cancel, hw] at this; linarith
    rw [h2]
    have : |1 - ‖P w‖| ≤ ‖w - P w‖ := abs_le.2 ⟨by linarith, by linarith⟩
    linarith

end Hilbert

open QuantumNLS.TensorCarrier QuantumNLS.TraceClass

/-- `‖γ^{(k)}_x − γ^{(k)}_y‖₁ ≤ 2‖x − y‖` for unit vectors. -/
theorem traceNorm_gamma_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (k m : ℕ) (x y : HilbertTensorPower ℂ E (k + m)) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    traceNorm (reducedDensityPower k m x - reducedDensityPower k m y) ≤ ENNReal.ofReal (2 * ‖x - y‖) := by
  have h := traceNorm_reducedDensity_sub_le (splitIsometry k m x) (splitIsometry k m y)
  rw [← map_sub, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map,
    hx, hy] at h
  unfold reducedDensityPower
  refine h.trans (le_of_eq ?_)
  ring_nf

end QuantumNLS.Prop020Vector

#print axioms QuantumNLS.Prop020Vector.norm_exp_sub_le
#print axioms QuantumNLS.Prop020Vector.diag_apply_le
#print axioms QuantumNLS.Prop020Vector.normalize_proj
#print axioms QuantumNLS.Prop020Vector.traceNorm_gamma_sub_le
