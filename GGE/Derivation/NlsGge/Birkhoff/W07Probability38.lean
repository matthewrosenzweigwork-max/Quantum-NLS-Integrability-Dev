import NlsGge.Birkhoff.W06Jacobian38b
import NlsGge.Birkhoff.W05ChargeSeries38
import NlsGge.Birkhoff.W09Approx38
import NlsGge.Hierarchy.FourierTilt38

/-! # W07 (`D:prop:probability`, v2 l.1554-1574), part a: the finite-section weights `f_N` (B-free)

Source: `paper/v2.tex` l.1547-1560 (`D:eq:fN`) and `blueprint/claims/W07.md`.

`f_N(x) = exp[-E_W(𝓕⁻¹ x_N) + A(x_N)]`, `x_N = P_N x`, `A(x_N) = ∑_{|n|≤N} a_n |x_n|²`, with `E_W` the
complete spectral energy (`spectralEnergyW38`, `(2/π)∫ W(2λ) v`) of the physical field `𝓕⁻¹ x_N`.

* `fN38`: this function on `E_s`; every term is a finite quantity (`spectralEnergy_planeL2_W07`).
* `fN38_eq_fFourier`: `f_N(x) = fFourier38 c N w`, `w = planeOfSeq38 N (x)` the plane coordinates of
  the physical trigonometric polynomial `𝓕⁻¹ x_N` (the field `planeField w` has Fourier coefficient
  `w_i` at mode `n_i`, while `x = 𝓕 u` has `x_n = -û(-n)`, hence the reflection `reflectPlane`).
* `integral_fN38`: `∫ f_N dγ_W = Z_N(W)` (`relativePartition38`), via `fourierTilt_identity38` at `δ = 0`
  and the reflection invariance of the Fourier-plane Gaussian.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.Weights NlsGge.HierarchyRiccati.Core NlsGge.Ramer Filter Topology
open NlsGge.AblowitzLadik (alTiltCoeff38)
open scoped ENNReal Real

section Plane

/-- Plane coordinates of the physical trigonometric polynomial `𝓕⁻¹ (P_N x)`: `w = reflectPlane (x_{n_i})`. -/
def planeOfSeq38 (N : ℕ) (x : ℤ → ℂ) : FourierPlane N :=
  reflectPlane N (fun i => x (modeIndex N i))

theorem fourierSeq38_planeL2_W07 (N : ℕ) (w : FourierPlane N) (n : ℤ) :
    fourierSeq38 (planeL2 N w) n = reflectedFourier (planeField N w) n := by
  rw [fourierSeq38_apply, physicalFourier_planeL2]
  rfl

theorem fourierSeq38_planeOfSeq38 (N : ℕ) (x : ℤ → ℂ) (n : ℤ) :
    fourierSeq38 (planeL2 N (planeOfSeq38 N x)) n = if n ∈ symmetricModes N then x n else 0 := by
  rw [fourierSeq38_planeL2_W07]
  by_cases hn : n ∈ symmetricModes N
  · simp only [hn, ↓reduceIte]
    obtain ⟨i, hi⟩ : ∃ i, modeIndex N i = n := by
      have := hn
      rw [symmetricModes_eq_image] at this
      simpa using this
    subst hi
    rw [reflectedFourier_planeField]
    unfold planeOfSeq38
    rw [reflectPlane_involutive]
  · simp only [hn, ↓reduceIte]
    unfold reflectedFourier
    rw [physicalFourier_planeField_outside, neg_zero]
    simp only [symmetricModes, Finset.mem_Icc, not_and_or, not_le] at hn
    omega

/-- The weighted quadratic form `A(x_N) = ∑_{|n|≤N} a_n |x_n|²`. -/
def Afin38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (N : ℕ) (x : ℤ → ℂ) : ℝ :=
  ∑ n ∈ symmetricModes N, fullWeightRate c.val n * ‖x n‖ ^ 2

theorem sum_plane_eq_Afin38 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (N : ℕ)
    (x : ℤ → ℂ) :
    ∑ i : Fin (2 * N + 1), fullWeightRate c.val (modeIndex N i) * ‖planeOfSeq38 N x i‖ ^ 2 =
      Afin38 c N x := by
  unfold Afin38
  rw [symmetricModes_eq_image, Finset.sum_image (fun i _ j _ h => modeIndex_injective N h)]
  rw [← Equiv.sum_comp (reflectMode_involutive N).toPerm
    (fun i => fullWeightRate c.val (modeIndex N i) * ‖x (modeIndex N i)‖ ^ 2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [planeOfSeq38, reflectPlane, norm_neg, Function.Involutive.coe_toPerm]
  rw [← fullWeightRate_even c.val (modeIndex N i), ← modeIndex_reflect]

/-- The spectral energy of a finite plane field is the finite `fullEnergy38` (W01, `E_W = (2/π)∫ W(2λ) v`). -/
theorem spectralEnergy_planeL2_W07 {lower upper : ℝ} (c : BoundedCoefficients lower upper) (N : ℕ)
    (w : FourierPlane N) :
    spectralEnergyW38 c.val (planeL2 N w) = ENNReal.ofReal (fullEnergy38 c N w) := by
  obtain ⟨hint, heq⟩ := fullEnergy38_eq_spectral c N w
  unfold spectralEnergyW38
  rw [heq, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t =>
      mul_nonneg (weight_pos38 c _).le (actualGapHeightE02_38_nonneg _ t))]

theorem spectralEnergy_planeL2_ne_top_W07 {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (N : ℕ) (w : FourierPlane N) : spectralEnergyW38 c.val (planeL2 N w) ≠ ⊤ := by
  rw [spectralEnergy_planeL2_W07]; exact ENNReal.ofReal_ne_top

theorem toReal_spectralEnergy_planeL2_W07 {lower upper : ℝ} (c : BoundedCoefficients lower upper)
    (N : ℕ) (w : FourierPlane N) :
    (spectralEnergyW38 c.val (planeL2 N w)).toReal = fullEnergy38 c N w := by
  rw [spectralEnergy_planeL2_W07]
  exact ENNReal.toReal_ofReal (by
    obtain ⟨hint, heq⟩ := fullEnergy38_eq_spectral c N w
    rw [heq]
    exact mul_nonneg (by positivity) (integral_nonneg fun t =>
      mul_nonneg (weight_pos38 c _).le (actualGapHeightE02_38_nonneg _ t)))

end Plane

section EsLevel

variable {lower upper : ℝ} (c : BoundedCoefficients lower upper) (s : ℝ)

/-- **`f_N` on `E_s` (v2 `D:eq:fN`).** `f_N(x) = exp[-E_W(𝓕⁻¹ x_N) + A(x_N)]`, `x_N = P_N x`
(`projE38`), `E_W` the spectral energy (`(2/π)∫ W(2λ) v`, finite for these fields), and
`A(x_N) = ∑_{|n|≤N} a_n |x_n|²`. -/
def fN38 (N : ℕ) (x : FullWeightedHilbert c s) : ℝ :=
  Real.exp (-(spectralEnergyW38 c.val (physOfE38 c s (projE38 c s N x))).toReal +
    Afin38 c N (coordE c s x))

/-- The same function on coordinate sequences (the Fourier-plane form `fFourier38`). -/
def fNseq38 (N : ℕ) (z : ℤ → ℂ) : ℝ := fFourier38 c N (planeOfSeq38 N z)

theorem coordE_eq_eCoe38 (x : FullWeightedHilbert c s) (n : ℤ) :
    coordE c s x n = eCoe38 c s x n := rfl

theorem physOfE38_projE38_W07 (N : ℕ) (x : FullWeightedHilbert c s) :
    physOfE38 c s (projE38 c s N x) = planeL2 N (planeOfSeq38 N (coordE c s x)) := by
  apply fourierSeq38_injective
  funext n
  rw [fourierSeq38_physOfE38, fourierSeq38_planeOfSeq38]
  exact eCoe38_projE38 c s N x n

theorem fN38_eq_fNseq (N : ℕ) (x : FullWeightedHilbert c s) :
    fN38 c s N x = fNseq38 c N (coordE c s x) := by
  unfold fN38 fNseq38 fFourier38
  rw [physOfE38_projE38_W07, toReal_spectralEnergy_planeL2_W07, sum_plane_eq_Afin38]

theorem fN38_pos (N : ℕ) (x : FullWeightedHilbert c s) : 0 < fN38 c s N x := Real.exp_pos _

theorem continuous_fNseq38 (N : ℕ) : Continuous (fNseq38 c N) := by
  unfold fNseq38 fFourier38
  have h1 : Continuous (fun z : ℤ → ℂ => planeOfSeq38 N z) := by
    unfold planeOfSeq38 reflectPlane
    exact continuous_pi fun i => (continuous_apply _).neg.comp
      (continuous_pi fun j => continuous_apply _)
  have h2 := continuous_fullEnergy38 c N
  refine Real.continuous_exp.comp ?_
  refine ((h2.comp h1).neg).add ?_
  refine continuous_finsetSum _ fun i _ => ?_
  exact continuous_const.mul ((continuous_norm.comp ((continuous_apply i).comp h1)).pow 2)

theorem measurable_fNseq38 (N : ℕ) : Measurable (fNseq38 c N) :=
  (continuous_fNseq38 c N).measurable

theorem alTiltCoeff38_zero (c : ℕ → ℝ) : alTiltCoeff38 c 0 = c := by
  funext j; simp [alTiltCoeff38]

theorem tiltD38_zero {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) :
    tiltD38 c.val 0 N = 1 := by
  unfold tiltD38
  rw [alTiltCoeff38_zero]
  refine Finset.prod_eq_one fun i _ => ?_
  exact div_self (fullWeightRate_pos38 c _).ne'

theorem map_planeOfSeq38 (N : ℕ) :
    (fullWeightSequenceGaussian c.val).map (planeOfSeq38 N) = fullWeightFourierGaussian N c.val := by
  have h1 : Measurable (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) => z (modeIndex N i)) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have h2 : Measurable (reflectPlane N) := by
    unfold reflectPlane
    exact measurable_pi_iff.2 fun i => (measurable_pi_apply _).neg
  have : planeOfSeq38 N = reflectPlane N ∘ (fun z : ℤ → ℂ => fun i : Fin (2 * N + 1) =>
      z (modeIndex N i)) := rfl
  rw [this, ← Measure.map_map h2 h1, fullWeightSequenceGaussian_map_modes,
    fullWeightFourierGaussian_map_reflectPlane]

theorem integrable_fNseq38 (N : ℕ) :
    Integrable (fNseq38 c N) (fullWeightSequenceGaussian c.val) := by
  have h := integrable_fFourier_tilt38 c c 0 (by rw [alTiltCoeff38_zero]) N
  simp only [zero_mul, Real.exp_zero, mul_one] at h
  have hm : Measurable (planeOfSeq38 N) := by
    unfold planeOfSeq38 reflectPlane
    exact measurable_pi_iff.2 fun i => (measurable_pi_apply _).neg.comp
      (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  rw [← map_planeOfSeq38 c N] at h
  exact (integrable_map_measure h.aestronglyMeasurable hm.aemeasurable).1 h

/-- **`∫ f_N dγ_W = Z_N(W)`** (v2 `D:eq:fN`), on the sequence space of the Gaussian. -/
theorem integral_fNseq38 (N : ℕ) :
    ∫ z, fNseq38 c N z ∂(fullWeightSequenceGaussian c.val) = relativePartition38 c N := by
  have h := fourierTilt_identity38 c c 0 (by rw [alTiltCoeff38_zero]) N
  simp only [zero_mul, Real.exp_zero, mul_one, tiltD38_zero, inv_one, one_mul] at h
  have hm : Measurable (planeOfSeq38 N) := by
    unfold planeOfSeq38 reflectPlane
    exact measurable_pi_iff.2 fun i => (measurable_pi_apply _).neg.comp
      (measurable_pi_iff.2 fun j => measurable_pi_apply _)
  rw [← h, ← map_planeOfSeq38 c N, integral_map hm.aemeasurable]
  · rfl
  · have := integrable_fFourier_tilt38 c c 0 (by rw [alTiltCoeff38_zero]) N
    simp only [zero_mul, Real.exp_zero, mul_one] at this
    rw [map_planeOfSeq38 c N]
    exact this.aestronglyMeasurable

/-- `∫ f_N dγ_W = Z_N(W)` on `E_s`. -/
theorem integral_fN38 (hs : (1 : ℝ) / 2 < s) (N : ℕ) :
    ∫ x, fN38 c s N x ∂(fullWeightedSequenceGaussian c s) = relativePartition38 c N := by
  have : (fun x => fN38 c s N x) = fun x => fNseq38 c N (coordE c s x) :=
    funext (fN38_eq_fNseq c s N)
  rw [this, integral_comp_coordE c s hs (integrable_fNseq38 c N).aestronglyMeasurable]
  exact integral_fNseq38 c N

end EsLevel

end NlsGge.Birkhoff
