import Mathlib
import QuantumNLS.ComplexifiedDiscriminant
import QuantumNLS.RiccatiMonodromyV

/-!
# R-3FEAD88B stage E2: independent-field monodromy link (`RiccatiIndependentV`)

Imported frozen inputs (read only): `ComplexifiedDiscriminant` (`cxCoef`, `cxDisc`), `RiccatiMonodromyV`
(`coefV`, `psiV`, `continuous_coefV`, `trace_monodromyV`), `L1SpatialTransfer.fundamental_spec`,
`LinearFundamental.exists_isFundamental`, `SpatialTransfer.IsFundamental`.

Proved here:
* `cxCoef_eq_gauge`: for `κ > 0`, `cxCoef κ u v z x = G⁻¹ * coefV κ u v z x * G` with the constant diagonal gauge
  `G = diag(1, (√κ)⁻¹)`, `G⁻¹ = diag(1, √κ)`. So the complexified coefficient of `cxDisc` is a constant gauge of
  the independent-profile monodromy coefficient of `RiccatiMonodromyV`; similar matrices have equal trace.
* `isFundamental_cxCoef`: gauge transport of a classical fundamental solution.
* `transfer_eq_of_fundamental`: a classical fundamental solution equals `L1SpatialTransfer.transfer` at the endpoint.
* `trace_transfer_cxCoef`, `cxDisc_eq_monodromy`: for continuous profiles `u`, `v` and a classical `L`-periodic
  solution `r` of `r' = iz r + u - κ v r²`, `cxDisc κ u v z = m + m⁻¹` with `m = ψ(L)` (independent `v`).
* `JV`, `psiV_at_L`: `ψ(L) = exp(-izL/2 + κ J_v)` with `J_v = ∫₀ᴸ v r` (independent-`v` Floquet integral).
* `exp_log_cx`, `logS_eq_cxDisc`: the branch identity `exp(κJ_v + log(1 + exp(izL - 2κJ_v))) = exp(izL/2) cxDisc`,
  under `‖exp(izL - 2κJ_v)‖ < 1`.
* `norm_exp_logArg_le`, `logS_sub_bound_gen`: the exponential smallness of `w = exp(izL - 2κJ_v)` and the
  log-remainder estimate `‖log(1+w) + κ(J - S)‖ ≤ |κ| E + (3/2)‖w‖` from `‖J - S‖ ≤ E`, `‖w‖ ≤ 1/2`.

Not proved here: the sup-norm expansion `‖J_v - i ∑ I_n z⁻ⁿ‖ ≤ E` for independent `v` (needs the independent-`v`
version of the pointwise remainder bounds of `RiccatiExpansions`), and the bridge from the H^S Picard branch to a
classical pointwise `C¹` solution `r` (the hypotheses `hr`, `hper` are taken as inputs).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Filter Topology MeasureTheory

open QuantumNLS.SpatialTransfer (IsFundamental)
open QuantumNLS.RiccatiMonodromyV (coefV psiV gcoefV continuous_coefV trace_monodromyV)

namespace QuantumNLS.RiccatiIndependentV

open PhysicalTensor (L2T)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Constant diagonal gauge `G = diag(1, (√κ)⁻¹)`. -/
def cxGauge (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, (((Real.sqrt κ)⁻¹ : ℝ) : ℂ)]

/-- Inverse gauge `G⁻¹ = diag(1, √κ)`. -/
def cxGaugeInv (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, ((Real.sqrt κ : ℝ) : ℂ)]

theorem cxGaugeInv_mul_cxGauge {κ : ℝ} (hκ : 0 < κ) : cxGaugeInv κ * cxGauge κ = 1 := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hsC : ((Real.sqrt κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cxGaugeInv, cxGauge, Matrix.mul_apply, Fin.sum_univ_two, hs, hsC]

theorem cxGauge_mul_cxGaugeInv {κ : ℝ} (hκ : 0 < κ) : cxGauge κ * cxGaugeInv κ = 1 := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hsC : ((Real.sqrt κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cxGaugeInv, cxGauge, Matrix.mul_apply, Fin.sum_univ_two, hs, hsC]

/-- Pointwise gauge identity: the complexified coefficient is the gauge of the independent-profile coefficient. -/
theorem cxCoef_eq_gauge {κ : ℝ} (hκ : 0 < κ) (u v : ℝ → ℂ) (z : ℂ) (x : ℝ) :
    ComplexifiedDiscriminant.cxCoef κ u v z x = cxGaugeInv κ * coefV κ u v z x * cxGauge κ := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hsC : ((Real.sqrt κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  have hk : (κ : ℂ) = ((Real.sqrt κ : ℝ) : ℂ) * ((Real.sqrt κ : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hκ.le).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ComplexifiedDiscriminant.cxCoef, cxGaugeInv, cxGauge, coefV, Matrix.mul_apply, Fin.sum_univ_two,
      hk, hsC] <;>
    field_simp <;> ring

theorem cxCoef_eq_fun {κ : ℝ} (hκ : 0 < κ) (u v : ℝ → ℂ) (z : ℂ) :
    ComplexifiedDiscriminant.cxCoef κ u v z
      = fun x => cxGaugeInv κ * coefV κ u v z x * cxGauge κ :=
  funext (cxCoef_eq_gauge hκ u v z)

/-- Gauge transport of a classical fundamental solution of `coefV` to one of the complexified coefficient. -/
theorem isFundamental_cxCoef {κ : ℝ} (hκ : 0 < κ) {u v : ℝ → ℂ} {z : ℂ}
    {Mu : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hMu : IsFundamental (coefV κ u v z) Mu) :
    IsFundamental (ComplexifiedDiscriminant.cxCoef κ u v z)
      (fun x => cxGaugeInv κ * Mu x * cxGauge κ) := by
  have hid1 := cxGaugeInv_mul_cxGauge hκ
  have hid2 := cxGauge_mul_cxGaugeInv hκ
  have hid' : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, cxGauge κ * (cxGaugeInv κ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hid2, Matrix.one_mul]
  refine ⟨?_, fun x => ?_⟩
  · simp [hMu.1, hid1]
  · have h1 := ((hMu.2 x).const_mul (cxGaugeInv κ)).mul_const (cxGauge κ)
    refine h1.congr_deriv ?_
    rw [cxCoef_eq_gauge hκ u v z x]
    simp only [Matrix.mul_assoc, hid']

/-- A classical fundamental solution of a continuous coefficient is the Volterra transfer at the endpoint. -/
theorem transfer_eq_of_fundamental {L : ℝ} (hL : 0 ≤ L) {A M : ℝ → Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Continuous A) (hM0 : M 0 = 1) (hMd : ∀ x, HasDerivAt M (A x * M x) x) :
    L1SpatialTransfer.transfer A L = M L := by
  have hMc : Continuous M := continuous_iff_continuousAt.2 fun y => (hMd y).continuousAt
  have hint : ∀ x : ℝ, ∫ s in (0 : ℝ)..x, A s * M s = M x - M 0 := fun x =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hMd y)
      ((hA.matrix_mul hMc).intervalIntegrable 0 x)
  have hEq := (L1SpatialTransfer.fundamental_spec hL (hA.intervalIntegrable 0 L)).2.2.2 M hMc.continuousOn
    (fun x _ => by rw [hint x, hM0]; abel)
  exact (hEq ⟨hL, le_rfl⟩).symm

/-- **Trace link.** For continuous `u`, `v`, a pointwise `C¹`, `L`-periodic solution `r` of
`r' = iz r + u - κ v r²` and a fundamental matrix `Mu` of `coefV κ u v z`, the trace of the Volterra transfer of
the complexified coefficient `cxCoef κ u v z` equals `m + m⁻¹`, `m = ψ(L) = exp(-izL/2 + κ ∫₀ᴸ v r)`. -/
theorem trace_transfer_cxCoef {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) {u v r : ℝ → ℂ} {z : ℂ}
    (hu : Continuous u) (hv : Continuous v)
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + u x - (κ : ℂ) * v x * r x ^ 2) x)
    (hper : r L = r 0) {Mu : ℝ → Matrix (Fin 2) (Fin 2) ℂ} (hMu : IsFundamental (coefV κ u v z) Mu) :
    Matrix.trace (L1SpatialTransfer.transfer (ComplexifiedDiscriminant.cxCoef κ u v z) L)
      = psiV κ v r z L + (psiV κ v r z L)⁻¹ := by
  have hcont : Continuous (ComplexifiedDiscriminant.cxCoef κ u v z) := by
    rw [cxCoef_eq_fun hκ u v z]
    exact (continuous_const.matrix_mul (continuous_coefV κ hu hv z)).matrix_mul continuous_const
  have hF := isFundamental_cxCoef hκ hMu
  have hT : L1SpatialTransfer.transfer (ComplexifiedDiscriminant.cxCoef κ u v z) L
      = cxGaugeInv κ * Mu L * cxGauge κ :=
    transfer_eq_of_fundamental (M := fun x => cxGaugeInv κ * Mu x * cxGauge κ) hL.le hcont hF.1 hF.2
  have htr : Matrix.trace (cxGaugeInv κ * Mu L * cxGauge κ) = Matrix.trace (Mu L) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, cxGauge_mul_cxGaugeInv hκ, Matrix.one_mul]
  rw [hT, htr]
  exact trace_monodromyV hL hu hv hr hper hMu

/-- **Discriminant link for profiles.** For `L2` fields `u`, `v` with continuous representatives and a classical
`L`-periodic Riccati solution `r` for `(u, v)`: `cxDisc κ u v z = m + m⁻¹`, `m = ψ(L)` with the independent `v`. -/
theorem cxDisc_eq_monodromy {L κ : ℝ} [Fact (0 < L)] {u v : L2T L} {z : ℂ} {r : ℝ → ℂ}
    (hκ : 0 < κ) (hu : Continuous (L2SpatialTransfer.profile u))
    (hv : Continuous (L2SpatialTransfer.profile v))
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + L2SpatialTransfer.profile u x
      - (κ : ℂ) * L2SpatialTransfer.profile v x * r x ^ 2) x)
    (hper : r L = r 0) :
    ComplexifiedDiscriminant.cxDisc κ u v z
      = psiV κ (L2SpatialTransfer.profile v) r z L
        + (psiV κ (L2SpatialTransfer.profile v) r z L)⁻¹ := by
  obtain ⟨Mu, hMu⟩ := LinearFundamental.exists_isFundamental (continuous_coefV κ hu hv z)
  exact trace_transfer_cxCoef (Fact.out : 0 < L) hκ hu hv hr hper hMu

/-- Independent-field Floquet integral `J_v = ∫₀ᴸ v r`. -/
def JV (v r : ℝ → ℂ) (L : ℝ) : ℂ := ∫ s in (0 : ℝ)..L, v s * r s

/-- Companion Floquet multiplier for the independent field: `ψ(L) = exp(-izL/2 + κ J_v)`. -/
theorem psiV_at_L (κ : ℝ) {v r : ℝ → ℂ} (z : ℂ) (L : ℝ) (hv : Continuous v) (hr : Continuous r) :
    psiV κ v r z L = Complex.exp ((L : ℂ) * (-(Complex.I * z) / 2) + (κ : ℂ) * JV v r L) := by
  unfold psiV JV gcoefV
  congr 1
  have hi1 : IntervalIntegrable (fun _ : ℝ => -(Complex.I * z) / 2) MeasureTheory.volume 0 L :=
    continuous_const.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun s : ℝ => (κ : ℂ) * (v s * r s)) MeasureTheory.volume 0 L :=
    (continuous_const.mul (hv.mul hr)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul]
  simp only [sub_zero, Complex.real_smul] <;> ring

/-- Branch identity for the independent field: `exp(κJ + log(1 + w)) = exp(izL/2)(m + m⁻¹)` with
`w = exp(izL - 2κJ)`, `m = exp(-izL/2 + κJ)`, under `‖w‖ < 1` (so that `1 + w ≠ 0`). -/
theorem exp_log_cx (L κ : ℝ) (z J : ℂ)
    (hw : ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)‖ < 1) :
    Complex.exp ((κ : ℂ) * J + Complex.log (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)))
      = Complex.exp (Complex.I * z * (L : ℂ) / 2) *
        (Complex.exp ((L : ℂ) * (-(Complex.I * z) / 2) + (κ : ℂ) * J)
          + (Complex.exp ((L : ℂ) * (-(Complex.I * z) / 2) + (κ : ℂ) * J))⁻¹) := by
  have hne : 1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J) ≠ 0 := by
    intro h
    have h1 : Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J) = -1 := by linear_combination h
    rw [h1, norm_neg, norm_one] at hw
    exact lt_irrefl _ hw
  have e1 : Complex.exp (Complex.I * z * (L : ℂ) / 2)
      * Complex.exp ((L : ℂ) * (-(Complex.I * z) / 2) + (κ : ℂ) * J) = Complex.exp ((κ : ℂ) * J) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : Complex.exp (Complex.I * z * (L : ℂ) / 2)
      * (Complex.exp ((L : ℂ) * (-(Complex.I * z) / 2) + (κ : ℂ) * J))⁻¹
      = Complex.exp (Complex.I * z * (L : ℂ) - (κ : ℂ) * J) := by
    rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
  rw [mul_add, e1, e2, Complex.exp_add, Complex.exp_log hne, mul_add, mul_one, ← Complex.exp_add]
  congr 1
  congr 1
  ring

/-- Exponential smallness of `w = exp(izL - 2κJ)`: `‖w‖ ≤ exp(-L Im z + 2|κ| ‖J‖)`. -/
theorem norm_exp_logArg_le (L κ : ℝ) (z J : ℂ) :
    ‖Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J)‖
      ≤ Real.exp (-(L * z.im) + 2 * |κ| * ‖J‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have h1 : (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * J).re = -(L * z.im) - 2 * (κ * J.re) := by
    simp [Complex.mul_re] <;> ring
  rw [h1]
  have h3 : |κ| * |J.re| ≤ |κ| * ‖J‖ :=
    mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm J) (abs_nonneg _)
  have h4 : -(κ * J.re) ≤ |κ| * |J.re| := by
    rw [← abs_mul]; exact neg_le_abs _
  linarith

/-- Log-remainder estimate for an arbitrary small `w`: `‖κJ + log(1+w) - κS‖ ≤ |κ| E + (3/2)‖w‖`
from `‖J - S‖ ≤ E` and `‖w‖ ≤ 1/2`. -/
theorem logS_sub_bound_gen (κ : ℝ) (J S w : ℂ) (E : ℝ) (hJ : ‖J - S‖ ≤ E) (hw : ‖w‖ ≤ 1 / 2) :
    ‖(κ : ℂ) * J + Complex.log (1 + w) - (κ : ℂ) * S‖ ≤ ‖(κ : ℂ)‖ * E + 3 / 2 * ‖w‖ := by
  have h1 : (κ : ℂ) * J + Complex.log (1 + w) - (κ : ℂ) * S
      = (κ : ℂ) * (J - S) + Complex.log (1 + w) := by ring
  rw [h1]
  calc ‖(κ : ℂ) * (J - S) + Complex.log (1 + w)‖
      ≤ ‖(κ : ℂ) * (J - S)‖ + ‖Complex.log (1 + w)‖ := norm_add_le _ _
    _ = ‖(κ : ℂ)‖ * ‖J - S‖ + ‖Complex.log (1 + w)‖ := by rw [norm_mul]
    _ ≤ ‖(κ : ℂ)‖ * E + 3 / 2 * ‖w‖ :=
        add_le_add (mul_le_mul_of_nonneg_left hJ (norm_nonneg _))
          (Complex.norm_log_one_add_half_le_self hw)

/-- **Independent-`v` branch identity on the discriminant.** Under the same hypotheses as `cxDisc_eq_monodromy`
and `‖exp(izL - 2κJ_v)‖ < 1`: `exp(κJ_v + log(1 + exp(izL - 2κJ_v))) = exp(izL/2) · cxDisc κ u v z`. -/
theorem logS_eq_cxDisc {L κ : ℝ} [Fact (0 < L)] {u v : L2T L} {z : ℂ} {r : ℝ → ℂ}
    (hκ : 0 < κ) (hu : Continuous (L2SpatialTransfer.profile u))
    (hv : Continuous (L2SpatialTransfer.profile v))
    (hr : ∀ x, HasDerivAt r (Complex.I * z * r x + L2SpatialTransfer.profile u x
      - (κ : ℂ) * L2SpatialTransfer.profile v x * r x ^ 2) x)
    (hper : r L = r 0)
    (hw : ‖Complex.exp (Complex.I * z * (L : ℂ)
      - 2 * (κ : ℂ) * JV (L2SpatialTransfer.profile v) r L)‖ < 1) :
    Complex.exp ((κ : ℂ) * JV (L2SpatialTransfer.profile v) r L + Complex.log
        (1 + Complex.exp (Complex.I * z * (L : ℂ) - 2 * (κ : ℂ) * JV (L2SpatialTransfer.profile v) r L)))
      = Complex.exp (Complex.I * z * (L : ℂ) / 2) * ComplexifiedDiscriminant.cxDisc κ u v z := by
  have hrc : Continuous r := continuous_iff_continuousAt.2 fun y => (hr y).continuousAt
  rw [cxDisc_eq_monodromy hκ hu hv hr hper, psiV_at_L κ z L hv hrc]
  exact exp_log_cx L κ z _ hw

end QuantumNLS.RiccatiIndependentV

#print axioms QuantumNLS.RiccatiIndependentV.cxCoef_eq_gauge
#print axioms QuantumNLS.RiccatiIndependentV.isFundamental_cxCoef
#print axioms QuantumNLS.RiccatiIndependentV.transfer_eq_of_fundamental
#print axioms QuantumNLS.RiccatiIndependentV.trace_transfer_cxCoef
#print axioms QuantumNLS.RiccatiIndependentV.cxDisc_eq_monodromy
#print axioms QuantumNLS.RiccatiIndependentV.psiV_at_L
#print axioms QuantumNLS.RiccatiIndependentV.exp_log_cx
#print axioms QuantumNLS.RiccatiIndependentV.norm_exp_logArg_le
#print axioms QuantumNLS.RiccatiIndependentV.logS_sub_bound_gen
#print axioms QuantumNLS.RiccatiIndependentV.logS_eq_cxDisc
