import QuantumNLS.HolomorphicStageD4
import QuantumNLS.GP05ConsumerBoundsR14

/-! Same-universe instantiation of the accepted D3/D4 Banach bridge.
The frozen r14 interfaces are used without a bridge application premise. -/
noncomputable section
set_option autoImplicit false
open Set Metric
namespace QuantumNLS.GP05AcceptedBridgeR16
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem banachHolomorphicBridge : GP05CauchyMajorantsR14.BanachHolomorphicBridge E F := by
  intro U f hU hf
  exact (HolomorphicStageD4.analyticOnNhd_bridge hU hf).1

/-- The canonical expansion of the original function with a common smaller
radius. No named bridge remains among the hypotheses. -/
theorem canonical_expansion {f : E → F} {a : E} {R M : ℝ}
    (hR : 0 < R) (hM : 0 ≤ M) (hf : DifferentiableOn ℂ f (ball a R))
    (hb : ∀ x ∈ ball a R, ‖f x‖ ≤ M) :
    HasFPowerSeriesOnBall f (GP05CauchyMajorantsR14.coefficients f a) a
      (ENNReal.ofReal (GP05CauchyMajorantsR14.commonRadius R)) :=
  GP05CauchyMajorantsR14.canonical_expansion hR hM
    (banachHolomorphicBridge _ _ isOpen_ball hf) hb

variable {I : Type*}

theorem uniform_derivatives {f : I → E → F} {a : E} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball a R))
    (hb : ∀ i z, z ∈ ball a R → ‖f i z‖ ≤ C*weight i) (n : ℕ) :
    ∀ i z, z ∈ ball a (R/2) →
      ‖iteratedFDeriv ℂ n (f i) z‖ ≤ ((4*(n+1 : ℕ)/R)^n*C)*weight i :=
  GP05ConsumerBoundsR14.uniform_derivatives banachHolomorphicBridge hR hC weight hw hf hb n

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]

theorem uniform_real_derivatives {f : I → E → F} {a : E} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (weight : I → ℝ) (hw : ∀ i, 0 ≤ weight i)
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball a R))
    (hb : ∀ i z, z ∈ ball a R → ‖f i z‖ ≤ C*weight i) (n : ℕ) :
    ∀ i z, z ∈ ball a (R/2) →
      ‖iteratedFDeriv ℝ n (f i) z‖ ≤ ((4*(n+1 : ℕ)/R)^n*C)*weight i :=
  GP05ConsumerBoundsR14.uniform_real_derivatives banachHolomorphicBridge hR hC weight hw hf hb n

end QuantumNLS.GP05AcceptedBridgeR16
