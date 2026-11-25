import QuantumNLS.Ext025A4ProductDischarge
/-! integrator-authored trusted spec for R-4C2E4AC7 thm:global-product-torus (Terra r175 FULL ACCEPT): headline statement(s) copied verbatim from Ext025A4ProductDischarge (QuantumNLS.Ext025A4ProductDischarge). -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open Filter Topology Set Metric
open scoped InnerProductSpace NNReal ENNReal
noncomputable section
namespace QuantumNLS.R4C2ESpec
open QuantumNLS.Ext025A4ProductDischarge
open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusContinuity
  QuantumNLS.ProductTorusAction QuantumNLS.ProductTorusPrimitive QuantumNLS.ProductTorusPrimitiveExterior
  QuantumNLS.ProductTorusAnalytic QuantumNLS.ProductTorusSymmetry QuantumNLS.ProductTorusPrimitiveAnalytic
  QuantumNLS.ProductTorusAllOrders QuantumNLS.ProductTorusMain QuantumNLS.ProductTorusCommute
  QuantumNLS.ProductTorusMainB QuantumNLS.ProductTorusComplexification QuantumNLS.ProductTorusHolomorphicExtension
open QuantumNLS.Ext025B6TorusCoordinates (Torus)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

set_option maxHeartbeats 8000000 in
theorem thm_global_product_torus_ext_spec {I : E → L1 ℝ} (hI : AnalyticOnNhd ℝ I univ)
    (hpos : Nonneg I) (hmass : ∀ u, ∑' n, (I u : ℤ → ℝ) n = ‖u‖ ^ 2)
    (hinv : Involutive (fderiv ℝ I)) (hprop : Proper I) (hper : Periodic (fderiv ℝ I))
    :
    -- everything in T8b
    ((((∀ ψ ψ' u, act (fderiv ℝ I) (ψ * ψ') u = act (fderiv ℝ I) ψ (act (fderiv ℝ I) ψ' u)) ∧
      (∀ u, act (fderiv ℝ I) 1 u = u) ∧
      Continuous (fun p : Torus × E => act (fderiv ℝ I) p.1 p.2) ∧
      (∀ n t u, act (fderiv ℝ I) (Pi.mulSingle n (Circle.exp t)) u = flow (fderiv ℝ I) (e n) t u)) ∧
    (∀ ψ u, AnalyticAt ℝ (act (fderiv ℝ I) ψ) u ∧ AnalyticAt ℝ (act (fderiv ℝ I) ψ⁻¹) u ∧
      (∀ v, act (fderiv ℝ I) ψ⁻¹ (act (fderiv ℝ I) ψ v) = v) ∧
      (∀ v, act (fderiv ℝ I) ψ (act (fderiv ℝ I) ψ⁻¹ v) = v) ∧
      ∀ a b, omega (fderiv ℝ (act (fderiv ℝ I) ψ) u a) (fderiv ℝ (act (fderiv ℝ I) ψ) u b) = omega a b) ∧
    (∀ u, ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ ψ : Torus, ∃ p : FormalMultilinearSeries ℝ E E,
      HasFPowerSeriesOnBall (act (fderiv ℝ I) ψ) p u (ENNReal.ofReal r) ∧ ∀ n, ‖p n‖ * r ^ n ≤ C) ∧
    (∀ u, ∃ ρ > (0 : ℝ), ∃ C1 C2 : ℝ, ∀ x ∈ ball u ρ, ∀ ψ : Torus,
      ‖fderiv ℝ (act (fderiv ℝ I) ψ) x‖ ≤ C1 ∧ ‖fderiv ℝ (fderiv ℝ (act (fderiv ℝ I) ψ)) x‖ ≤ C2) ∧
    (∀ u h, Continuous (fun ψ : Torus => fderiv ℝ (act (fderiv ℝ I) ψ) u h)) ∧
    (∀ u h, Continuous (fun ψ : Torus => alpha (act (fderiv ℝ I) ψ u) (fderiv ℝ (act (fderiv ℝ I) ψ) u h))) ∧
    (∀ u h k, alphaBar (fderiv ℝ I) u (h + k) = alphaBar (fderiv ℝ I) u h + alphaBar (fderiv ℝ I) u k) ∧
    (∀ (c : ℝ) u h, alphaBar (fderiv ℝ I) u (c • h) = c * alphaBar (fderiv ℝ I) u h) ∧
    (∀ u, ∃ C : ℝ, ∀ h, ‖alphaBar (fderiv ℝ I) u h‖ ≤ C * ‖h‖) ∧
    (∀ u (A₂ : ℝ), (∀ w ∈ I ⁻¹' {I u}, ‖fderiv ℝ (fderiv ℝ I) w‖ ≤ A₂) →
      ∀ h, |alphaBar (fderiv ℝ I) u h| ≤ ‖u‖ * Real.exp (Real.pi / 2 * A₂) * ‖h‖) ∧
    (∀ u a b, HasDerivAt (fun s : ℝ => alphaBar (fderiv ℝ I) (u + s • a) b) (dAlpha (fderiv ℝ I) u a b) 0 ∧
      dAlpha (fderiv ℝ I) u a b - dAlpha (fderiv ℝ I) u b a = omega a b) ∧
    (∀ ψ u h, alphaBar (fderiv ℝ I) (act (fderiv ℝ I) ψ u) (fderiv ℝ (act (fderiv ℝ I) ψ) u h) =
      alphaBar (fderiv ℝ I) u h) ∧
    (∀ n u, alphaBar (fderiv ℝ I) u (Xn (fderiv ℝ I) n u) = -(I u : ℤ → ℝ) n) ∧
    (∀ C : E →L[ℝ] E, (∀ v, C (C v) = v) → (∀ a b, omega (C a) (C b) = -omega a b) → (∀ v, I (C v) = I v) →
      ∀ u h, alphaBar (fderiv ℝ I) (C u) (C h) = -alphaBar (fderiv ℝ I) u h) ∧
    (∀ (U V : E →L[ℝ] E) (σ : ℤ ≃ ℤ) (ε : ℝ), (∀ v, U (V v) = v) → (∀ a b, omega (U a) (U b) = ε * omega a b) →
      (ε = 1 ∨ ε = -1) → (∀ v n, (I (U v) : ℤ → ℝ) n = (I v : ℤ → ℝ) (σ n)) →
      ∀ u h, alphaBar (fderiv ℝ I) (U u) (U h) = ε * alphaBar (fderiv ℝ I) u h)) ∧
    -- (a) uniform local operator bounds of all orders
    (∀ u, ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ (ψ : Torus) (k : ℕ), ∀ x ∈ ball u (r / 2),
      ‖iteratedFDeriv ℝ k (act (fderiv ℝ I) ψ) x‖ ≤ k.factorial * (C * 2 ^ (k + 1) / r ^ k)) ∧
    -- (b) fixed-vector strong continuity of all orders in the group parameter
    (∀ (n : ℕ) (u : E) (v : Fin n → E), Continuous (fun ψ : Torus => iteratedFDeriv ℝ n (act (fderiv ℝ I) ψ) u v)) ∧
    -- `ᾱ` real analytic in the full dual norm
    (∃ Φ : E → E →L[ℝ] ℝ, AnalyticOnNhd ℝ Φ univ ∧ ∀ u h, Φ u h = alphaBar (fderiv ℝ I) u h)) ∧
    -- (c) the common bounded holomorphic extension in the complexified initial variable
    (∀ u, ∃ R > (0 : ℝ), ∃ M : ℝ, ∀ ψ : Torus, ∃ Tc : Cx E → Cx E,
      DifferentiableOn ℂ Tc (ball (Cx.ι u) R) ∧ AnalyticOnNhd ℂ Tc (ball (Cx.ι u) R) ∧
      (∀ z ∈ ball (Cx.ι u) R, ‖Tc z‖ ≤ M) ∧ ∀ x ∈ ball u R, Tc (Cx.ι x) = Cx.ι (act (fderiv ℝ I) ψ x)) := by
  exact QuantumNLS.Ext025A4ProductDischarge.thm_global_product_torus_ext hI hpos hmass hinv hprop hper

end QuantumNLS.R4C2ESpec
#print axioms QuantumNLS.R4C2ESpec.thm_global_product_torus_ext_spec
