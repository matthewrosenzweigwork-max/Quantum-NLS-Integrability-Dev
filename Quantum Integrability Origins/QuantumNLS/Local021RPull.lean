import Mathlib
import QuantumNLS.ResetMoserPrinted

/-!
# LOCAL-021 repair, stage R1: the pulled-back symplectic form `Ω = (ζ̃⁻¹)^*ω = η^*ω` for an analytic `η : ℓ² → ℓ²`

`pullForm η y (v, w) = ω(Dη_y v, Dη_y w)` (this is the formula `P.Ω_y(v,w) = ω(Dη_y v, Dη_y w)` of the frozen `Local021Setting.Setting.hΩ`).
For `η` analytic at `z` (in the full operator norm: `fderiv η` is analytic into `ℓ² →L ℓ²`) this proves:

* `pullForm_alt` : alternating;  `analyticAt_pullForm` : analytic as a `Form`-valued map (full operator norm);
* `pullForm_closed` : `dΩ = 0`, i.e. `DΩ_z(a;b,c) + DΩ_z(b;c,a) + DΩ_z(c;a,b) = 0` (second derivative of `η` is symmetric, `ω` alternating);
* `pullForm_sub_le` : `‖Ω_y − ω‖ ≤ 2e(2+e)` whenever `‖Dη_y − 1‖ ≤ e`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.Local021R

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser

/-- `Ω_y(v,w) = ω(Dη_y v, Dη_y w)`. -/
def pullForm (η : K → K) (y : K) : Form := omegaF.bilinearComp (fderiv ℝ η y) (fderiv ℝ η y)

theorem pullForm_apply (η : K → K) (y v w : K) :
    pullForm η y v w = omegaF (fderiv ℝ η y v) (fderiv ℝ η y w) := rfl

theorem pullForm_alt (η : K → K) (y v w : K) : pullForm η y v w = - pullForm η y w v := by
  rw [pullForm_apply, pullForm_apply]; exact omegaF_alt _ _

theorem abs_omegaF_le (v w : K) : |omegaF v w| ≤ 2 * ‖v‖ * ‖w‖ := by
  rw [omegaF_apply, omega]
  have h1 : |(inner ℂ v w).im| ≤ ‖inner ℂ v w‖ := Complex.abs_im_le_norm _
  have h2 : ‖inner ℂ v w‖ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm v w
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith

theorem norm_omegaF_le : ‖omegaF‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [Real.norm_eq_abs]
  have := abs_omegaF_le v w
  nlinarith [norm_nonneg v, norm_nonneg w]

theorem pull_bilinear :
    IsBoundedBilinearMap ℝ (fun p : (K →L[ℝ] K) × (K →L[ℝ] K) => omegaF.bilinearComp p.1 p.2) where
  add_left x₁ x₂ y := by ext v w; simp
  smul_left c x y := by ext v w; simp
  add_right x y₁ y₂ := by ext v w; simp
  smul_right c x y := by ext v w; simp
  bound := by
    refine ⟨2 + 1, by norm_num, fun A B => ?_⟩
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    simp only [ContinuousLinearMap.bilinearComp_apply, Real.norm_eq_abs]
    have h1 := abs_omegaF_le (A v) (B w)
    have h2 : ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
    have h3 : ‖B w‖ ≤ ‖B‖ * ‖w‖ := B.le_opNorm w
    have h4 : ‖A v‖ * ‖B w‖ ≤ (‖A‖ * ‖v‖) * (‖B‖ * ‖w‖) :=
      mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
    have h5 : 0 ≤ ‖A‖ * ‖v‖ * (‖B‖ * ‖w‖) := by positivity
    nlinarith [norm_nonneg v, norm_nonneg w, norm_nonneg A, norm_nonneg B, mul_nonneg (norm_nonneg A) (norm_nonneg B)]

/-- the bilinear (in the pair of operators) map `(A, B) ↦ ω(A·, B·)`. -/
def pullB : (K →L[ℝ] K) →L[ℝ] (K →L[ℝ] K) →L[ℝ] Form := pull_bilinear.toContinuousLinearMap

theorem pullB_apply (A B : K →L[ℝ] K) (v w : K) : pullB A B v w = omegaF (A v) (B w) := rfl

theorem pullForm_eq (η : K → K) : pullForm η = fun y => pullB (fderiv ℝ η y) (fderiv ℝ η y) := rfl

theorem analyticAt_pullForm {η : K → K} {z : K} (h : AnalyticAt ℝ η z) : AnalyticAt ℝ (pullForm η) z := by
  have hA : AnalyticAt ℝ (fderiv ℝ η) z := h.fderiv
  have hb : AnalyticAt ℝ (fun p : (K →L[ℝ] K) × (K →L[ℝ] K) => pullB p.1 p.2) (fderiv ℝ η z, fderiv ℝ η z) :=
    pullB.analyticAt_bilinear _
  rw [pullForm_eq]
  exact hb.comp₂ hA hA

theorem pullForm_closed {η : K → K} {z : K} (h : AnalyticAt ℝ η z) (a b c : K) :
    fderiv ℝ (pullForm η) z a b c + fderiv ℝ (pullForm η) z b c a + fderiv ℝ (pullForm η) z c a b = 0 := by
  have h3 : ContDiffAt ℝ 3 η z := h.contDiffAt.of_le le_top
  have hsym : IsSymmSndFDerivAt ℝ η z := h3.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hdA : DifferentiableAt ℝ (fderiv ℝ η) z :=
    (h3.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hA : HasFDerivAt (fderiv ℝ η) (fderiv ℝ (fderiv ℝ η) z) z := hdA.hasFDerivAt
  have hΩ := pullB.hasFDerivAt_of_bilinear hA hA
  have e1 : ∀ a b c : K, fderiv ℝ (pullForm η) z a b c =
      omegaF (fderiv ℝ (fderiv ℝ η) z a b) (fderiv ℝ η z c) + omegaF (fderiv ℝ η z b) (fderiv ℝ (fderiv ℝ η) z a c) := by
    intro a b c
    rw [pullForm_eq, hΩ.fderiv]
    simp [pullB_apply, add_comm]
  simp only [e1]
  have h1 : fderiv ℝ (fderiv ℝ η) z b a = fderiv ℝ (fderiv ℝ η) z a b := hsym b a
  have h2 : fderiv ℝ (fderiv ℝ η) z c b = fderiv ℝ (fderiv ℝ η) z b c := hsym c b
  have h3 : fderiv ℝ (fderiv ℝ η) z c a = fderiv ℝ (fderiv ℝ η) z a c := hsym c a
  rw [h1, h2, h3]
  have al1 := omegaF_alt (fderiv ℝ (fderiv ℝ η) z a b) (fderiv ℝ η z c)
  have al2 := omegaF_alt (fderiv ℝ η z b) (fderiv ℝ (fderiv ℝ η) z a c)
  have al3 := omegaF_alt (fderiv ℝ (fderiv ℝ η) z b c) (fderiv ℝ η z a)
  linarith

theorem pullForm_sub_le (η : K → K) (y : K) {e : ℝ} (he0 : 0 ≤ e) (he : ‖fderiv ℝ η y - 1‖ ≤ e) :
    ‖pullForm η y - omegaF‖ ≤ 2 * e * (2 + e) := by
  set A := fderiv ℝ η y with hA
  have hAn : ‖A‖ ≤ 1 + e := by
    have := norm_add_le (A - 1) 1
    have h1 : ‖(1 : K →L[ℝ] K)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    rw [sub_add_cancel] at this
    linarith
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  have hD : ∀ x : K, ‖A x - x‖ ≤ e * ‖x‖ := by
    intro x
    have := (A - 1).le_opNorm x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at this
    exact this.trans (mul_le_mul_of_nonneg_right he (norm_nonneg _))
  have hAx : ∀ x : K, ‖A x‖ ≤ (1 + e) * ‖x‖ := fun x => (A.le_opNorm x).trans
    (mul_le_mul_of_nonneg_right hAn (norm_nonneg _))
  have key : (pullForm η y - omegaF) v w = omegaF (A v - v) (A w) + omegaF v (A w - w) := by
    simp only [ContinuousLinearMap.sub_apply, pullForm_apply, map_sub, ContinuousLinearMap.sub_apply]
    ring
  rw [key, Real.norm_eq_abs]
  have t1 := abs_omegaF_le (A v - v) (A w)
  have t2 := abs_omegaF_le v (A w - w)
  have u1 := hD v
  have u2 := hD w
  have u3 := hAx w
  calc |omegaF (A v - v) (A w) + omegaF v (A w - w)|
      ≤ |omegaF (A v - v) (A w)| + |omegaF v (A w - w)| := abs_add_le _ _
    _ ≤ 2 * ‖A v - v‖ * ‖A w‖ + 2 * ‖v‖ * ‖A w - w‖ := add_le_add t1 t2
    _ ≤ 2 * (e * ‖v‖) * ((1 + e) * ‖w‖) + 2 * ‖v‖ * (e * ‖w‖) := by
        gcongr
    _ = 2 * e * (2 + e) * ‖v‖ * ‖w‖ := by ring

end QuantumNLS.Local021R

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021R.analyticAt_pullForm
#print axioms QuantumNLS.Local021R.pullForm_closed
#print axioms QuantumNLS.Local021R.pullForm_sub_le
