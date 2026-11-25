import QuantumNLS.ResetMoserInst

/-!
# `thm:reset-moser` (LOCAL-017), stage 0: `D_t = t(Ω − ω)` discharges `hiso` of `dq_Ycov_zero`

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "For `0 ≤ t ≤ 1`, put `Ω^t = ω + t(Ω − ω)` ... Both `ω` and `Ω^t` vanish on `𝒯_z × 𝒯_z`." and the conclusion "`dq_n(z) Y_t(z) = 0` for every `n` ... at all points".

* `Dt S t z = t • (Ω z − ω)`, the perturbation of `Ω^t`;
* `Dt_Tz`: `D_t` (and `Ω^t = ω + D_t`) vanishes on `𝒯_z × 𝒯_z` for every `z ∈ B_R` (`omega_Tz` + `isotropy`);
* `norm_Dt_lt`: `‖D_t z‖ < 1`; `continuousOn_Dt`;
* `dq_Yt_zero`: with `β⁰` continuous on `B_R` and annihilating `𝒯_z` (the named clause `hann`, still carried), `dq_n(z) Y_t(z) = 0` for every `z ∈ B_R`, every `n` and every `t ∈ [0,1]`, and `Y_t(z) ∈ 𝒯_z` at points with all coordinates nonzero. `hiso` is no longer an input.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket

/-- `D_t = t (Ω − ω)`. -/
def Dt (S : Hyp) (t : ℝ) (z : K) : Form := t • (S.Ω z - omegaF)

/-- `Ω_z − ω` vanishes on `𝒯_z × 𝒯_z`. -/
theorem Ω_sub_omega_Tz (S : Hyp) {z : K} (hz : z ∈ ball (0 : K) S.R) :
    ∀ h ∈ Tz z, ∀ h' ∈ Tz z, (S.Ω z - omegaF) h h' = 0 := by
  intro h hh h' hh'
  simp only [ContinuousLinearMap.sub_apply, omegaF_apply]
  rw [isotropy S hz h hh h' hh', omega_Tz hh hh']
  ring

theorem Dt_Tz (S : Hyp) (t : ℝ) {z : K} (hz : z ∈ ball (0 : K) S.R) :
    ∀ h ∈ Tz z, ∀ h' ∈ Tz z, Dt S t z h h' = 0 := by
  intro h hh h' hh'
  simp only [Dt, ContinuousLinearMap.smul_apply]
  rw [Ω_sub_omega_Tz S hz h hh h' hh', smul_zero]

theorem norm_Dt_lt (S : Hyp) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : K} (hz : z ∈ ball (0 : K) S.R) :
    ‖Dt S t z‖ < 1 := by
  unfold Dt
  have h1 := S.Ω_lt z hz
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  calc t * ‖S.Ω z - omegaF‖ ≤ 1 * ‖S.Ω z - omegaF‖ :=
        mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    _ < 1 := by linarith

theorem continuousOn_Dt (S : Hyp) (t : ℝ) : ContinuousOn (Dt S t) (ball (0 : K) S.R) := by
  unfold Dt
  exact (S.Ω_continuousOn.sub continuousOn_const).const_smul t

/-- **`dq_n(z) Y_t(z) = 0` for `Y_t = Ycov D_t β⁰`**, with `hiso` discharged. Remaining named input: `hann`. -/
theorem dq_Yt_zero (S : Hyp) {β0 : K → Cov} (hβc : ContinuousOn β0 (ball (0 : K) S.R))
    (hann : ∀ z ∈ ball (0 : K) S.R, ∀ h ∈ Tz z, β0 z h = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (∀ z ∈ ball (0 : K) S.R, ∀ n : ℤ, fderiv ℝ (q n) z (Ycov (Dt S t z) (β0 z)) = 0) ∧
    (∀ z ∈ ball (0 : K) S.R, (∀ n, z n ≠ 0) → Ycov (Dt S t z) (β0 z) ∈ Tz z) :=
  dq_Ycov_zero (continuousOn_Dt S t) hβc (fun z hz => norm_Dt_lt S ht hz)
    (fun z hz _ => Dt_Tz S t hz) hann

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.Dt_Tz
#print axioms QuantumNLS.ResetMoser.norm_Dt_lt
#print axioms QuantumNLS.ResetMoser.dq_Yt_zero
