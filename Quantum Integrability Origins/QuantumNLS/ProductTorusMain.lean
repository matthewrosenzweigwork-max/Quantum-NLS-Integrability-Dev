import QuantumNLS.ProductTorusAnalytic
import QuantumNLS.ProductTorusSymmetry

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T8 (CONDITIONAL assembly)

Source: `chapters/global/product_torus.tex`, Theorem `thm:global-product-torus` (lines 22–66).

`thm_global_product_torus` takes the printed hypotheses:
* `𝓘 : 𝓗 → ℓ¹(ℤ;ℝ)` real analytic as a map between these Banach spaces (`AnalyticOnNhd ℝ I univ`, `𝓗` a complex
  Hilbert space regarded as a real one);
* (1) `I_n(u) ≥ 0` and `Σ_n I_n(u) = ‖u‖²`;
* (2) `{I_n, I_j} = dI_n[X_{I_j}] = 0` with `X_F = W⁻¹dF` (`Involutive (fderiv ℝ I)`);
* (3) `𝓘⁻¹(K)` norm compact for norm compact `K ⊂ ℓ¹_+` (`Proper I`);
* (4) the complete flow of each `I_n` has time `2π` equal to the identity (`Periodic (fderiv ℝ I)`);
and, for the analytic-initial-dependence clauses only, the named held hypothesis
`HeldGP04AnalyticInitialDependence` (Terra r8 GP-04 remainder; stage T6). Separability of `𝓗` is not used.

Conclusions (each a frozen T1–T7 result, bound to the printed hypotheses):
* a continuous action of `𝕋^ℤ = ℤ → Circle` on `𝓗` extending the individual flows (T4b);
* each `T_ψ` is a strong symplectic map with inverse `T_{ψ⁻¹}` (T5a); real analytic with real-analytic inverse, and,
  near each `u`, one common radius and majorant for the power series of all `T_ψ` (T6, conditional on GP-04);
* uniform local operator bounds for the first and second derivatives over the whole group (T7a/T7b);
* fixed-vector strong continuity of the derivatives in the group parameter (T5b; no operator-norm continuity);
* eq:global-averaged-primitive `ᾱ` (normalized product Haar): continuous (hence measurable) integrand, a bounded
  one-form with the printed bound, `dᾱ = ω`, `T_ψ^*ᾱ = ᾱ`, `ᾱ(X_{I_n}) = −I_n`, and `C^*ᾱ = −ᾱ` for a bounded
  real-linear involution with `C^*ω = −ω` and `I_n(Cu) = I_n(u)` (T7a/T7b).
* the general covariance `ᾱ_{Uu}(Uh) = ε ᾱ_u(h)` for unitary/antiunitary symmetries permuting the actions (T7c).
NOT included (see the hand-back): analyticity of `ᾱ` in the full dual norm (the clause where the GP-05 bridge would
enter; `GP05BanachAnalyticityBridge` is therefore not a hypothesis here), and fixed-vector continuity in the group
parameter of derivatives of order `≥ 2`. GP-14 is not used.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal ENNReal

noncomputable section

namespace QuantumNLS.ProductTorusMain

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusVariational
  QuantumNLS.ProductTorusCommute QuantumNLS.ProductTorusContinuity QuantumNLS.ProductTorusAction
  QuantumNLS.ProductTorusFixedVector QuantumNLS.ProductTorusSymplectic QuantumNLS.ProductTorusPrimitive
  QuantumNLS.ProductTorusPrimitiveExterior QuantumNLS.ProductTorusAnalytic QuantumNLS.ProductTorusSymmetry
open QuantumNLS.Ext025B6TorusCoordinates (Torus)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- The printed hypotheses give the stage hypotheses `PHyp I (fderiv ℝ I)`. -/
theorem phyp_of_source {I : E → L1 ℝ} (hI : AnalyticOnNhd ℝ I univ) (hpos : Nonneg I)
    (hinv : Involutive (fderiv ℝ I)) (hprop : Proper I) (hper : Periodic (fderiv ℝ I)) :
    PHyp I (fderiv ℝ I) where
  hyp :=
    { hasFDerivAt := fun u => ((hI u (mem_univ u)).differentiableAt).hasFDerivAt
      contDiff := hI.fderiv.contDiff
      involutive := hinv
      fibre_compact := fibre_compact_of_source hpos hprop }
  nonneg := hpos
  proper := hprop
  periodic := hper
  contDiff2 := hI.fderiv.contDiff

/-- **Theorem `thm:global-product-torus`** (R-4C2E4AC7), assembled from stages T1–T7; the analytic-initial-dependence
clauses are conditional on the named held hypothesis `HeldGP04AnalyticInitialDependence`. -/
theorem thm_global_product_torus {I : E → L1 ℝ} (hI : AnalyticOnNhd ℝ I univ)
    (hpos : Nonneg I) (hmass : ∀ u, ∑' n, (I u : ℤ → ℝ) n = ‖u‖ ^ 2)
    (hinv : Involutive (fderiv ℝ I)) (hprop : Proper I) (hper : Periodic (fderiv ℝ I))
    (hGP04 : HeldGP04AnalyticInitialDependence E (E →L[ℝ] L1 ℝ)) :
    -- a continuous action of the product group extending the individual flows
    ((∀ ψ ψ' u, act (fderiv ℝ I) (ψ * ψ') u = act (fderiv ℝ I) ψ (act (fderiv ℝ I) ψ' u)) ∧
      (∀ u, act (fderiv ℝ I) 1 u = u) ∧
      Continuous (fun p : Torus × E => act (fderiv ℝ I) p.1 p.2) ∧
      (∀ n t u, act (fderiv ℝ I) (Pi.mulSingle n (Circle.exp t)) u = flow (fderiv ℝ I) (e n) t u)) ∧
    -- each `T_ψ`: real analytic strong symplectic map with real-analytic inverse `T_{ψ⁻¹}`
    (∀ ψ u, AnalyticAt ℝ (act (fderiv ℝ I) ψ) u ∧ AnalyticAt ℝ (act (fderiv ℝ I) ψ⁻¹) u ∧
      (∀ v, act (fderiv ℝ I) ψ⁻¹ (act (fderiv ℝ I) ψ v) = v) ∧
      (∀ v, act (fderiv ℝ I) ψ (act (fderiv ℝ I) ψ⁻¹ v) = v) ∧
      ∀ a b, omega (fderiv ℝ (act (fderiv ℝ I) ψ) u a) (fderiv ℝ (act (fderiv ℝ I) ψ) u b) = omega a b) ∧
    -- one common analytic neighbourhood and majorant near each `u`, uniformly over the whole group
    (∀ u, ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ ψ : Torus, ∃ p : FormalMultilinearSeries ℝ E E,
      HasFPowerSeriesOnBall (act (fderiv ℝ I) ψ) p u (ENNReal.ofReal r) ∧ ∀ n, ‖p n‖ * r ^ n ≤ C) ∧
    -- uniform local operator bounds of the derivatives over the whole group
    (∀ u, ∃ ρ > (0 : ℝ), ∃ C1 C2 : ℝ, ∀ x ∈ ball u ρ, ∀ ψ : Torus,
      ‖fderiv ℝ (act (fderiv ℝ I) ψ) x‖ ≤ C1 ∧ ‖fderiv ℝ (fderiv ℝ (act (fderiv ℝ I) ψ)) x‖ ≤ C2) ∧
    -- fixed tangent vectors: strong continuity in the group parameter
    (∀ u h, Continuous (fun ψ : Torus => fderiv ℝ (act (fderiv ℝ I) ψ) u h)) ∧
    -- the averaged primitive: continuous integrand, bounded one-form, printed bound
    (∀ u h, Continuous (fun ψ : Torus => alpha (act (fderiv ℝ I) ψ u) (fderiv ℝ (act (fderiv ℝ I) ψ) u h))) ∧
    (∀ u h k, alphaBar (fderiv ℝ I) u (h + k) = alphaBar (fderiv ℝ I) u h + alphaBar (fderiv ℝ I) u k) ∧
    (∀ (c : ℝ) u h, alphaBar (fderiv ℝ I) u (c • h) = c * alphaBar (fderiv ℝ I) u h) ∧
    (∀ u, ∃ C : ℝ, ∀ h, ‖alphaBar (fderiv ℝ I) u h‖ ≤ C * ‖h‖) ∧
    (∀ u (A₂ : ℝ), (∀ w ∈ I ⁻¹' {I u}, ‖fderiv ℝ (fderiv ℝ I) w‖ ≤ A₂) →
      ∀ h, |alphaBar (fderiv ℝ I) u h| ≤ ‖u‖ * Real.exp (Real.pi / 2 * A₂) * ‖h‖) ∧
    -- `dᾱ = ω`
    (∀ u a b, HasDerivAt (fun s : ℝ => alphaBar (fderiv ℝ I) (u + s • a) b) (dAlpha (fderiv ℝ I) u a b) 0 ∧
      dAlpha (fderiv ℝ I) u a b - dAlpha (fderiv ℝ I) u b a = omega a b) ∧
    -- `T_ψ^*ᾱ = ᾱ`
    (∀ ψ u h, alphaBar (fderiv ℝ I) (act (fderiv ℝ I) ψ u) (fderiv ℝ (act (fderiv ℝ I) ψ) u h) =
      alphaBar (fderiv ℝ I) u h) ∧
    -- `ᾱ(X_{I_n}) = −I_n`
    (∀ n u, alphaBar (fderiv ℝ I) u (Xn (fderiv ℝ I) n u) = -(I u : ℤ → ℝ) n) ∧
    -- `C^*ᾱ = −ᾱ`
    (∀ C : E →L[ℝ] E, (∀ v, C (C v) = v) → (∀ a b, omega (C a) (C b) = -omega a b) → (∀ v, I (C v) = I v) →
      ∀ u h, alphaBar (fderiv ℝ I) (C u) (C h) = -alphaBar (fderiv ℝ I) u h) ∧
    -- unitary (`ε = 1`) / antiunitary (`ε = −1`) symmetries permuting the actions
    (∀ (U V : E →L[ℝ] E) (σ : ℤ ≃ ℤ) (ε : ℝ), (∀ v, U (V v) = v) → (∀ a b, omega (U a) (U b) = ε * omega a b) →
      (ε = 1 ∨ ε = -1) → (∀ v n, (I (U v) : ℤ → ℝ) n = (I v : ℤ → ℝ) (σ n)) →
      ∀ u h, alphaBar (fderiv ℝ I) (U u) (U h) = ε * alphaBar (fderiv ℝ I) u h) := by
  have H := phyp_of_source hI hpos hinv hprop hper
  have hDI : AnalyticOnNhd ℝ (fderiv ℝ I) univ := hI.fderiv
  refine ⟨⟨act_mul H.hyp hpos hprop hper, act_one H.hyp hpos hprop hper, act_continuous H.hyp hpos hprop hper,
    act_single H.hyp hpos hprop hper⟩, fun ψ u => ?_, act_uniform_analytic H hDI hGP04, fun u => ?_,
    fun u h => act_fderiv_continuous H.hyp hpos hprop hper u h, fun u h => continuous_integrand H u h,
    fun u h k => alphaBar_add H u h k, fun c u h => alphaBar_smul c u h, fun u => alphaBar_bound_exists H u,
    fun u A₂ hA h => alphaBar_bound H hmass u hA h, fun u a b => d_alphaBar H u a b,
    fun ψ u h => alphaBar_invariant H ψ u h, fun n u => alphaBar_Xn H hmass n u,
    fun C hCC hCω hCI u h => alphaBar_C H hCC hCω hCI u h,
    fun U V σ ε hUV hUω hε hUI u h => alphaBar_U H hUV hUω hε hUI u h⟩
  · obtain ⟨hinvA, hl, hr⟩ := act_inv_analyticAt H hDI hGP04 ψ u
    refine ⟨act_analyticAt H hDI hGP04 ψ u, hinvA, hl, hr, fun a b => ?_⟩
    rw [act_def]
    exact symplectic H.hyp (lift ψ) 1 u a b
  · obtain ⟨ρ, hρ, M, C1, C2, -, -, -, hb⟩ := uniform_local H u
    exact ⟨ρ, hρ, C1, C2, fun x hx ψ => ⟨(hb x hx ψ).2.1, (hb x hx ψ).2.2⟩⟩

end QuantumNLS.ProductTorusMain

#print axioms QuantumNLS.ProductTorusMain.phyp_of_source
#print axioms QuantumNLS.ProductTorusMain.thm_global_product_torus
