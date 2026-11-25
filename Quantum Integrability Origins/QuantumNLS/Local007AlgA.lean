import Mathlib
import QuantumNLS.Local007Lift
import QuantumNLS.Local007Zeros
import QuantumNLS.DEF014DiscriminantAnalytic

/-! LOCAL-007 stage A1: the discriminant on a contour as a real-analytic map into the Banach algebra
`ℝ →ᵇ ℂ` of bounded continuous functions of the angle.

`Fh v θ = Δ_v(c e^{iθ})` for `‖v‖ < 1`, and `Fh : L2T → (ℝ →ᵇ ℂ)` is real analytic at `0`.
(Pointwise lift `Local007Lift` of the accepted power series of the DEF-014 transfer path.) -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open BoundedContinuousFunction Metric Filter Topology
open scoped ENNReal NNReal
namespace QuantumNLS.Local007AlgA
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Zeros (Dl)
open QuantumNLS.DEF014VolterraAnalytic QuantumNLS.DEF014VolterraOperator
open QuantumNLS.DEF014DiscriminantAnalytic QuantumNLS.SpatialTransfer
attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid
variable {L : ℝ} [Fact (0 < L)]

theorem disc_series (κ R : ℝ) (hR : 0 < R) :
    ∃ q : FormalMultilinearSeries ℝ (L2T L × ℂ) ℂ,
      HasFPowerSeriesOnBall (fun e : L2T L × ℂ => Dl κ e.1 e.2) q 0 (ENNReal.ofReal (R / Real.exp 1)) := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  let ev := ContinuousMap.evalCLM ℝ (⟨L, hL, le_rfl⟩ : Set.Icc (0 : ℝ) L) (M := Mat2)
  let Λ : Path L Mat2 →L[ℝ] ℂ := (entryCLM 0 0).comp ev + (entryCLM 1 1).comp ev
  have hfun : (fun e : L2T L × ℂ => Dl κ e.1 e.2) = Λ ∘ transferPath hL (physicalFamily κ) := by
    funext e
    simp only [Dl, L2SpatialTransfer.discriminant, L2SpatialTransfer.spatialTransfer,
      Matrix.trace_fin_two, Function.comp, Λ, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
    rfl
  have h := Λ.comp_hasFPowerSeriesOnBall (powerSeries hL (physicalFamily κ) R hR)
  exact ⟨_, by rw [hfun]; exact h⟩

/-- The contour point as a pair. -/
def ehat (c : ℝ) (v : L2T L) : ℝ →ᵇ (L2T L × ℂ) :=
  ofNormedAddCommGroup (fun θ : ℝ => (v, (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
    (by fun_prop) (‖v‖ + |c|) (fun θ => by
      rw [Prod.norm_def]
      refine max_le ?_ ?_
      · linarith [abs_nonneg c]
      · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs]
        linarith [norm_nonneg v])

theorem norm_ehat_le (c : ℝ) (v : L2T L) : ‖ehat c v‖ ≤ ‖v‖ + |c| := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun θ => ?_
  change ‖(v, (c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤ _
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · linarith [abs_nonneg c]
  · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs]
    linarith [norm_nonneg v]

/-- Constant embedding `v ↦ (θ ↦ (v,0))`. -/
def Jc : L2T L →L[ℝ] (ℝ →ᵇ (L2T L × ℂ)) :=
  LinearMap.mkContinuous
    { toFun := fun v => BoundedContinuousFunction.const ℝ ((v, (0 : ℂ)) : L2T L × ℂ)
      map_add' := fun v w => by ext θ <;> simp [BoundedContinuousFunction.add_apply]
      map_smul' := fun a v => by ext θ <;> simp [BoundedContinuousFunction.smul_apply] }
    1 (fun v => by
      refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun θ => ?_
      simp [Prod.norm_def])

theorem ehat_eq (c : ℝ) (v : L2T L) : ehat c v = ehat c 0 + Jc v := by
  ext θ <;> simp [ehat, Jc, BoundedContinuousFunction.add_apply]

theorem ehat_analytic (c : ℝ) : AnalyticAt ℝ (fun v : L2T L => ehat c v) 0 := by
  have : (fun v : L2T L => ehat c v) = fun v => ehat c 0 + Jc v := funext (ehat_eq c)
  rw [this]
  exact analyticAt_const.add (Jc.analyticAt _)

theorem Fhat_pkg (κ c : ℝ) :
    ∃ (Fh : L2T L → (ℝ →ᵇ ℂ)), AnalyticAt ℝ Fh 0 ∧
      ∀ v : L2T L, ‖v‖ < 1 → ∀ θ : ℝ,
        Fh v θ = Dl κ v ((c : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
  obtain ⟨q, hq⟩ := disc_series (L := L) κ ((2 * |c| + 2) * Real.exp 1) (by positivity)
  have hr : ENNReal.ofReal (((2 * |c| + 2) * Real.exp 1) / Real.exp 1) = ENNReal.ofReal (2 * |c| + 2) := by
    rw [mul_div_cancel_right₀ _ (Real.exp_ne_zero 1)]
  rw [hr] at hq
  have hl := Local007Lift.hasFPowerSeriesOnBall_lift (T := ℝ) hq
  refine ⟨fun v => (Local007Lift.liftSeries (T := ℝ) q).sum (ehat c v), ?_, ?_⟩
  · have h0 : ehat c (0 : L2T L) ∈ Metric.eball (0 : ℝ →ᵇ (L2T L × ℂ)) (ENNReal.ofReal (2 * |c| + 2)) := by
      rw [Metric.mem_eball, edist_zero_right]
      have := norm_ehat_le c (0 : L2T L)
      rw [norm_zero, zero_add] at this
      have h2 : ((‖ehat c (0 : L2T L)‖₊ : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal (2 * |c| + 2) := by
        rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith [abs_nonneg c])
      exact h2
    have ha := hl.analyticAt_of_mem h0
    exact ha.comp (ehat_analytic c)
  · intro v hv θ
    have hlt : ((‖ehat c v‖₊ : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal (2 * |c| + 2) := by
      rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
        (by linarith [norm_ehat_le c v, abs_nonneg c])
    have := Local007Lift.lift_sum_apply hq (ehat c v) hlt θ
    exact this

end QuantumNLS.Local007AlgA
#print axioms QuantumNLS.Local007AlgA.Fhat_pkg
