import QuantumNLS.LOCAL009R23OperatorContour

/-! The genuine zero-particle sector: the transfer is scalar, its selected
inverse and total derivative vanish, and the printed contour is zero. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
noncomputable section
open Complex Set Metric Filter Topology
namespace QuantumNLS.LOCAL009R23Vacuum
open QuantumNLS.LOCAL009R23PhysicalInverse QuantumNLS.LOCAL009R23OperatorContour
  QuantumNLS.LOCAL009R22LiteralScalar QuantumNLS.LOCAL009R22Geometry
  QuantumNLS.Ext025A7 QuantumNLS.PeriodReconstruction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem zero_smul_id : (0 : ℂ) • ContinuousLinearMap.id ℂ H = 0 := by simp

theorem correction_zero (c : ℂ) (Q : H →L[ℂ] H) :
    (0 : H →L[ℂ] H) + c • (Q * 0) = 0 := by simp

theorem normalCalc_scalar (f : ℂ → ℂ) (c : ℂ) :
    normalCalc f (c • ContinuousLinearMap.id ℂ H) = f c • ContinuousLinearMap.id ℂ H := by
  change cfc f (algebraMap ℂ (H →L[ℂ] H) c) = algebraMap ℂ (H →L[ℂ] H) (f c)
  exact cfc_algebraMap c f

variable {L κ M ε : ℝ} [Fact (0 < L)]

theorem transfer_vacuum (z : ℂ) :
    transfer L κ ε 0 z = (1+Complex.exp (I*z*L)) • ContinuousLinearMap.id ℂ (Sector L 0) := by
  simp [transfer,QuantumNLS.NormalizedTransfer.normalizedTransfer]

theorem inverse_vacuum (hκ : 0 < κ) (hM : 0 < M)
    (hsmall : κ*L*M ≤ 1/1000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ band (momentum L n) (halfWidth L)) : inverseOp L κ M ε 0 z = 0 := by
  have hL : 0 < L := Fact.out
  have hR : 0 < radius L M := by unfold radius halfWidth; positivity
  have hr : κ*radius L M ≤ 1/1000 := by
    have hs := source_small hsmall
    calc
      κ*radius L M = 2*(κ*M/(halfWidth L/2)) := by unfold radius; ring
      _ ≤ 1/1000 := by linarith
  unfold inverseOp
  rw [transfer_vacuum,normalCalc_scalar]
  have hc := local009_inverse_center κ L hκ hR hr (band_open (momentum L n) (halfWidth L))
    (fun w hw => source_phase_bound hL n hw) (fun w hw => source_gap_bound hL n hw) hz
  have hc' : spectralInverse κ L (radius L M) z (1+Complex.exp (I*z*L)) = 0 := by
    simpa [spectralMap] using hc
  rw [hc']
  exact zero_smul_id

theorem derivative_vacuum (hκ : 0 < κ) (hM : 0 < M)
    (hsmall : κ*L*M ≤ 1/1000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ band (momentum L n) (halfWidth L)) :
    deriv (inverseOp L κ M ε 0) z = 0 := by
  have he : inverseOp L κ M ε 0 =ᶠ[𝓝 z] (fun _ => 0) := by
    filter_upwards [(band_open _ _).mem_nhds hz] with w hw
    exact inverse_vacuum hκ hM hsmall n hw
  rw [he.deriv_eq,deriv_const]

theorem integrand_vacuum (hκ : 0 < κ) (hM : 0 < M)
    (hsmall : κ*L*M ≤ 1/1000000) (n : ℤ) {z : ℂ}
    (hz : z ∈ band (momentum L n) (halfWidth L)) : integrand L κ M ε 0 z = 0 := by
  unfold integrand
  rw [inverse_vacuum hκ hM hsmall n hz,derivative_vacuum hκ hM hsmall n hz]
  exact correction_zero _ _

/-- The printed operator integral is zero, with its norm integrability
proved by the locally constant integrand, in the actual vacuum space. -/
theorem approximation_vacuum (hκ : 0 < κ) (hM : 0 < M)
    (hsmall : κ*L*M ≤ 1/1000000) (n : ℤ) : approximation L κ M ε n 0 = 0 := by
  have hL : 0 < L := Fact.out
  have ha : 0 < halfWidth L := by unfold halfWidth; positivity
  have hb {z : ℂ} (hz : z ∈ Gam (momentum L n-halfWidth L) (momentum L n+halfWidth L) (halfWidth L)) :
      z ∈ band (momentum L n) (halfWidth L) :=
    contour_ball_subset_band ha hz (mem_closedBall_self (by positivity))
  have hc {z : ℂ} (hz : z ∈ band (momentum L n) (halfWidth L)) :
      ContinuousAt (integrand L κ M ε 0) z := by
    have he : integrand L κ M ε 0 =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [(band_open _ _).mem_nhds hz] with w hw
      exact integrand_vacuum hκ hM hsmall n hw
    exact continuousAt_const.congr he.symm
  ext v
  unfold approximation
  rw [smul_apply,rectIntegral_eigen _ (fun _ => 0) v (by linarith) ha.le
    (fun z hz => hc (hb hz)) (fun z hz => by simp [integrand_vacuum hκ hM hsmall n (hb hz)])]
  simp [QuantumNLS.LabelExactPeriod.rectIntegral]

end QuantumNLS.LOCAL009R23Vacuum
