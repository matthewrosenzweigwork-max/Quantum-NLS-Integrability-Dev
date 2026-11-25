import Mathlib
import QuantumNLS.ResetMoserProcedure
import QuantumNLS.Local021Mono
import QuantumNLS.Local021Haar
import QuantumNLS.Local021Equiv

/-!
# LOCAL-021, stage 4: coupling scaling of the procedure

Source: `local_covariance.tex:193-215`: "As bilinear forms, `Ω_{κ,z} = Ω_{1,√κ z}`.  The radial primitive has the corresponding homogeneity, its
scalar Haar integral has `f_κ(z) = κ^{-1} f_1(√κ z)`, and the defining linear equation gives `Y_{κ,t}(z) = κ^{-1/2} Y_{1,t}(√κ z)`.
Consequently `S_κ` and `Φ_κ` have the same scaling relation."

Here two instances `(PA, BA)` (coupling `κ`) and `(PB, BB)` (coupling `κ s²`) of the LOCAL-017 procedure are compared, given
`ScaleΩ PA PB s` (`Ω^A_{s y} = Ω^B_y` as bilinear forms on the common domain):

* `beta_scale`  : `β^A_{s z} = s β^B_z`;   `f_scale` : `f^A(s z) = s² f^B(z)`;   `beta0_scale` : `β⁰^A_{s z} = s β⁰^B_z`;
* `moserY_scale`: `Y^A_t(s z) = s Y^B_t(z)`;
* `Sm_scale`, `Si_scale` : `S^A(s z) = s S^B(z)`, `(S^A)⁻¹(s w) = s (S^B)⁻¹(w)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.Local021

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.ResetMoser QuantumNLS.ResetMoserClamp
open QuantumNLS.Ext025B7LocalPath QuantumNLS.LOCAL017Haar

/-- multiplication by `s ≠ 0` as a continuous linear equivalence. -/
def sCLE (s : ℝ) (hs : s ≠ 0) : K ≃L[ℝ] K := ContinuousLinearEquiv.smulLeft (Units.mk0 s hs)

theorem sCLE_apply (s : ℝ) (hs : s ≠ 0) (z : K) : sCLE s hs z = s • z := rfl

theorem fderiv_const_mul_ne {c : ℝ} (hc : c ≠ 0) (g : K → ℝ) (x : K) :
    fderiv ℝ (fun y => c * g y) x = c • fderiv ℝ g x := by
  by_cases hd : DifferentiableAt ℝ g x
  · exact fderiv_const_mul hd c
  · have hd' : ¬ DifferentiableAt ℝ (fun y => c * g y) x := by
      intro h
      apply hd
      have := h.const_mul c⁻¹
      simpa [← mul_assoc, inv_mul_cancel₀ hc] using this
    rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']; simp

/-- `Ω^A_{s y} = Ω^B_y` as bilinear forms (`s > 0`), on the common domain. -/
def ScaleΩ (PA PB : PrintedHyp) (s : ℝ) : Prop :=
  ∀ y ∈ ball (0 : K) PB.R, s • y ∈ ball (0 : K) PA.R → PA.Ω (s • y) = PB.Ω y

variable {PA PB : PrintedHyp}

theorem beta_scale {s : ℝ} (hs : 0 < s) (h : ScaleΩ PA PB s) {z : K} (hz : z ∈ ball (0 : K) PB.R)
    (hsz : s • z ∈ ball (0 : K) PA.R) : betaR PA.toHyp (s • z) = s • betaR PB.toHyp z := by
  rw [PA.betaR_toHyp hsz, PB.betaR_toHyp hz]
  unfold PrintedHyp.betaP
  rw [← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le zero_le_one] at ht
  have h1 : t • z ∈ ball (0 : K) PB.R := scale_mem' hz ht
  have h2 : s • (t • z) ∈ ball (0 : K) PA.R := by
    have h3 := mem_ball_zero_iff.1 hsz
    rw [mem_ball_zero_iff, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht.1, abs_of_pos hs]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs] at h3
    have h4 : t * ‖z‖ ≤ ‖z‖ := mul_le_of_le_one_left (norm_nonneg z) ht.2
    nlinarith [mul_le_mul_of_nonneg_left h4 hs.le]
  have e1 : t • s • z = s • (t • z) := smul_comm t s z
  ext h'
  simp only [e1, h _ h1 h2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul, map_smul,
    omegaF_apply]
  ring_nf

theorem rotation_smul (s : ℝ) (p : PathParameter) (z : H) : rotation p (s • z) = s • rotation p z := by
  refine lp.ext (funext fun n => ?_)
  show (rotationAngles p n : ℂ) * (s • z n) = s • ((rotationAngles p n : ℂ) * z n)
  rw [mul_smul_comm]

theorem velocity_smul (s : ℝ) (θ : AngleBox) (w : H) : velocity θ (s • w) = s • velocity θ w := by
  refine lp.ext (funext fun n => ?_)
  show Complex.I * (((θ n).val : ℝ) : ℂ) * (s • w n) = s • (Complex.I * (((θ n).val : ℝ) : ℂ) * w n)
  rw [mul_smul_comm]

theorem f_scale {s : ℝ} (hs : 0 < s) (h : ScaleΩ PA PB s) {z : K} (hz : z ∈ ball (0 : K) PB.R)
    (hsz : s • z ∈ ball (0 : K) PA.R) :
    primitive (betaR PA.toHyp) (s • z) = s ^ 2 * primitive (betaR PB.toHyp) z := by
  unfold primitive
  have : ∀ p, pathIntegrand (betaR PA.toHyp) (s • z) p = s ^ 2 * pathIntegrand (betaR PB.toHyp) z p := by
    intro p
    unfold pathIntegrand
    have hr : rotation p z ∈ ball (0 : K) PB.R := by
      rw [mem_ball_zero_iff, rotation_norm]; exact mem_ball_zero_iff.1 hz
    have hr2 : s • rotation p z ∈ ball (0 : K) PA.R := by
      rw [← rotation_smul]
      rw [mem_ball_zero_iff, rotation_norm]; exact mem_ball_zero_iff.1 hsz
    rw [rotation_smul, velocity_smul, beta_scale hs h hr hr2]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul]
    ring
  simp only [this]
  rw [MeasureTheory.integral_const_mul]; ring


end QuantumNLS.Local021

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.Local021.beta_scale
#print axioms QuantumNLS.Local021.f_scale
