import QuantumNLS.ComplexifiedSeriesLift
import QuantumNLS.DEF014VolterraAnalytic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Complexified analytic infrastructure, stage X2: complex analyticity of the DEF-014 Volterra transfer

Generic, unconditional. Let `A : Family E 𝔸 L` be a DEF-014 coefficient family (frozen `DEF014VolterraOperator`)
on a complex normed space `E`, with values in a complex normed algebra `𝔸`, whose coefficient is complex-homogeneous
almost everywhere: `A.coef (c • e) = c • A.coef e` a.e. on `(0, L]` for `c : ℂ` (`CHomFamily`). Then:
* every actual Volterra iterate `DEF014VolterraAnalytic.iterates hL A n` is homogeneous under complex scalars in each
  slot (`iterates_isCHom`);
* the frozen polarized real series `RealAnalyticDef.symSeries (iterates hL A)` of the actual transfer is termwise
  complex multilinear, so `cSeries` is a complex power series of `transferPath hL A` at `0` on every ball
  (`powerSeriesC`), and the transfer path is complex analytic at every point (`analyticAt_transferPathC`,
  `analyticOnNhd_transferPathC`): it is an entire function of the complex parameter;
* `norm_transferPath_le`: `‖transferPath e‖ ≤ ‖1‖ exp(bound ‖e‖)` (uniform on bounded sets).
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Interval NNReal ENNReal

namespace QuantumNLS.ComplexifiedVolterra

open DEF014VolterraOperator DEF014VolterraAnalytic ComplexifiedSeriesLift

-- Keep the real structures given as hypotheses (those used by the frozen DEF-014 modules); do not derive real
-- structures from the complex ones in this file.
attribute [-instance] NormedSpace.complexToReal NormedAlgebra.complexToReal Module.complexToReal
  Algebra.complexToReal

variable {E 𝔸 : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [NormedAlgebra ℂ 𝔸] [IsScalarTower ℝ ℂ 𝔸] [CompleteSpace 𝔸]
variable {L : ℝ} (hL : 0 ≤ L) (A : Family E 𝔸 L)

/-- Complex homogeneity of the coefficient, almost everywhere on the period. -/
def CHomFamily : Prop :=
  ∀ (c : ℂ) (e : E), A.coef (c • e) =ᵐ[volume.restrict (Ioc 0 L)] fun t => c • A.coef e t

omit [NormedAlgebra ℝ 𝔸] [IsScalarTower ℝ ℂ 𝔸] [CompleteSpace 𝔸] in
theorem extend_smul (c : ℂ) (f : Path L 𝔸) (t : ℝ) : extend hL (c • f) t = c • extend hL f t := rfl

omit [IsScalarTower ℝ ℂ E] in
/-- Every actual Volterra iterate is homogeneous under complex scalars in each slot. -/
theorem iterates_isCHom (hA : CHomFamily A) (n : ℕ) : IsCHom (iterates hL A n) := by
  induction n with
  | zero => exact fun _ i _ _ => i.elim0
  | succ n ih =>
    intro m i c y
    ext x
    rw [iterates_succ, ContinuousMap.smul_apply, iterates_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Function.update_self, Function.update_self, Fin.tail_update_zero, Fin.tail_update_zero,
        intervalIntegral.integral_of_le x.2.1, intervalIntegral.integral_of_le x.2.1, ← integral_smul]
      have hae := ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right x.2.2) (hA c y)
      exact integral_congr_ae (hae.mono fun t ht => by simp only [ht, smul_mul_assoc])
    · have h0 : ∀ z : E, Function.update m j.succ z 0 = m 0 := fun z =>
        Function.update_of_ne (Fin.succ_ne_zero j).symm _ _
      rw [h0, h0, Fin.tail_update_succ, Fin.tail_update_succ, ih (Fin.tail m) j c y,
        ← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [extend_smul, mul_smul_comm]

/-- The complex power series of the transfer path (the frozen polarized series, read as complex multilinear). -/
def cSeries (hA : CHomFamily A) : FormalMultilinearSeries ℂ E (Path L 𝔸) :=
  fun n => liftC (RealAnalyticDef.symC (iterates hL A n)) (symC_isCHom _ (iterates_isCHom hL A hA n))

omit [IsScalarTower ℝ ℂ E] in
/-- Complex power series of the actual transfer path at `0`, on every ball. -/
theorem powerSeriesC (hA : CHomFamily A) (R : ℝ) (hR : 0 < R) :
    HasFPowerSeriesOnBall (transferPath hL A) (cSeries hL A hA) 0 (ENNReal.ofReal (R / Real.exp 1)) :=
  hasFPowerSeriesOnBall_of_coe_eq _ _ (fun _ _ => rfl) (powerSeries hL A R hR)

omit [IsScalarTower ℝ ℂ E] in
/-- The transfer path is complex analytic at every point. -/
theorem analyticAt_transferPathC (hA : CHomFamily A) (e : E) : AnalyticAt ℂ (transferPath hL A) e := by
  let R := (‖e‖ + 1) * Real.exp 1
  have hR : 0 < R := by dsimp [R]; positivity
  apply (powerSeriesC hL A hA R hR).analyticAt_of_mem
  rw [Metric.mem_eball, edist_lt_ofReal, dist_zero_right]
  dsimp [R]
  rw [mul_div_cancel_right₀ _ (Real.exp_ne_zero 1)]
  linarith

omit [IsScalarTower ℝ ℂ E] in
theorem analyticOnNhd_transferPathC (hA : CHomFamily A) : AnalyticOnNhd ℂ (transferPath hL A) univ :=
  fun e _ => analyticAt_transferPathC hL A hA e

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [NormedAlgebra ℂ 𝔸] [IsScalarTower ℝ ℂ 𝔸] in
/-- `‖transferPath e‖ ≤ ‖1‖ exp(bound ‖e‖)`. -/
theorem norm_transferPath_le (e : E) :
    ‖transferPath hL A e‖ ≤ ‖(1 : 𝔸)‖ * Real.exp (A.bound * ‖e‖) := by
  have hs : HasSum (fun n : ℕ => ‖(1 : 𝔸)‖ * ((A.bound * ‖e‖) ^ n / (n.factorial : ℝ)))
      (‖(1 : 𝔸)‖ * Real.exp (A.bound * ‖e‖)) := by
    have := (NormedSpace.expSeries_div_hasSum_exp (A.bound * ‖e‖)).mul_left ‖(1 : 𝔸)‖
    rwa [← Real.exp_eq_exp_ℝ] at this
  rw [← (hasSum_iterates hL A e).tsum_eq]
  refine tsum_of_norm_bounded hs fun n => ?_
  have := norm_iterates_diag_le hL A n e
  rwa [mul_div_assoc] at this

end QuantumNLS.ComplexifiedVolterra

#print axioms QuantumNLS.ComplexifiedVolterra.iterates_isCHom
#print axioms QuantumNLS.ComplexifiedVolterra.powerSeriesC
#print axioms QuantumNLS.ComplexifiedVolterra.analyticAt_transferPathC
#print axioms QuantumNLS.ComplexifiedVolterra.analyticOnNhd_transferPathC
#print axioms QuantumNLS.ComplexifiedVolterra.norm_transferPath_le
