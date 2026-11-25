import QuantumNLS.ProductTorusPrimitiveExterior

/-!
# R-4C2E4AC7 (`thm:global-product-torus`), stage T6 (CONDITIONAL): uniform analytic initial dependence

Source: `chapters/global/product_torus.tex`, proof, "The product topology and full initial-point regularity",
paragraphs 4–5 ("We next justify the uniform analytic initial-point statement ... Real analyticity of `𝓘` gives, near
each point of `𝒞`, a holomorphic extension ... A finite subcover gives common positive lower radii and common finite
upper bounds. ... The Picard integral map on a short complex time interval is a contraction with constants determined
by those bounds. The constants are uniform in `θ`, since the generator depends boundedly linearly on `θ`. ... This
gives a common complex initial neighborhood at every fixed `u ∈ 𝒞`, on which all `T_θ` are holomorphic and uniformly
bounded.").

The analytic-initial-dependence clause of GP-04 is HELD by Terra (round 8: "Prove analytic initial dependence using
holomorphic Picard iterates and their limit on a smaller ball and the reversed-time inverse differential"). It is
carried here as the named hypothesis `HeldGP04AnalyticInitialDependence`, stated for an arbitrary real Banach space,
an arbitrary parameter family of autonomous fields `f_i = L_i ∘ g` with `g` real analytic near a compact set and
`‖L_i‖ ≤ B` (the source's "generator depends boundedly linearly on `θ`"), and an arbitrary reference trajectory
staying in that compact set on `[0,1]`. Its conclusion is the uniform-in-`i` Taylor majorant of the time-one maps
at the initial point: a common radius `r` and a common bound `‖p_i n‖ rⁿ ≤ C`. (A series with such a majorant is
exactly the Taylor series of a holomorphic extension to a complexified ball, bounded uniformly in `i`; the Lean
statement uses the real power series.) This module does NOT prove that clause.

`GP05BanachAnalyticityBridge` (the GP-05 holomorphic-to-analytic bridge being built by the the auxiliary construction role,
HolomorphicStage*) is recorded with its statement only; nothing in this module depends on it.

Proved here from `HeldGP04AnalyticInitialDependence` (instantiated with `g = D𝓘`, `L_ψ = W⁻¹ ∘ pair(lift ψ)`,
`‖L_ψ‖ ≤ π/2`, the compact fibre of `u`):
* **`act_uniform_analytic`**: near each `u`, all `T_ψ` (`ψ ∈ 𝕋^ℤ`) have power series at `u` with one common radius
  and one common majorant;
* `act_analyticAt`, `act_inv_analyticAt`: each `T_ψ` is real analytic at every point, and so is its inverse
  `T_{ψ⁻¹}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open Filter Topology Set Metric
open scoped InnerProductSpace NNReal ENNReal

noncomputable section

namespace QuantumNLS.ProductTorusAnalytic

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusFlow QuantumNLS.ProductTorusVariational
  QuantumNLS.ProductTorusCommute QuantumNLS.ProductTorusContinuity QuantumNLS.ProductTorusAction
  QuantumNLS.ProductTorusPrimitive
open QuantumNLS.Ext025B6TorusCoordinates (Torus)

/-- **Named held hypothesis (GP-04, Terra r8 HELD clause): analytic initial dependence**, uniform over a parameter
family of autonomous fields depending boundedly linearly on the parameter. -/
def HeldGP04AnalyticInitialDependence (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] : Prop :=
  ∀ (ι : Type) (g : V → W) (L : ι → W →L[ℝ] V) (B : ℝ) (φ : ι → ℝ → V → V) (S : Set V) (u : V),
    IsCompact S → AnalyticOnNhd ℝ g S → (∀ i, ‖L i‖ ≤ B) →
    (∀ i x t, HasDerivAt (fun t => φ i t x) (L i (g (φ i t x))) t) → (∀ i x, φ i 0 x = x) →
    (∀ i, ∀ t ∈ Icc (0 : ℝ) 1, φ i t u ∈ S) →
    ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ i, ∃ p : FormalMultilinearSeries ℝ V V,
      HasFPowerSeriesOnBall (φ i 1) p u (ENNReal.ofReal r) ∧ ∀ n, ‖p n‖ * r ^ n ≤ C

/-- **Named hypothesis (GP-05 Banach analyticity bridge, the auxiliary construction HolomorphicStage*)**: complex differentiability on an
open subset of a complex Banach space implies analyticity there. Recorded only; not used in this module. -/
def GP05BanachAnalyticityBridge (V W : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] : Prop :=
  ∀ (U : Set V) (f : V → W), IsOpen U → DifferentiableOn ℂ f U → AnalyticOnNhd ℂ f U

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

variable {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)}

/-- The generator as a bounded linear image of `D𝓘`: `X_θ(u) = L_θ(D𝓘(u))`. -/
def Lgen (θ : Linf) : (E →L[ℝ] L1 ℝ) →L[ℝ] E := WinvL.comp (ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ))

theorem X_eq_Lgen (θ : Linf) (u : E) : X DI θ u = Lgen θ (DI u) := by
  rw [X_eq_comp]
  rfl

theorem norm_Lgen_le (θ : Linf) : ‖(Lgen θ : (E →L[ℝ] L1 ℝ) →L[ℝ] E)‖ ≤ ‖θ‖ / 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun D => ?_
  show ‖WinvL (ContinuousLinearMap.compL ℝ E (L1 ℝ) ℝ (pair θ) D)‖ ≤ ‖θ‖ / 2 * ‖D‖
  rw [ContinuousLinearMap.compL_apply, WinvL_apply, norm_Winv]
  have := (ContinuousLinearMap.opNorm_comp_le (pair θ) D).trans
    (mul_le_mul_of_nonneg_right (norm_pair_le θ) (norm_nonneg _))
  linarith

/-- **Uniform analytic initial dependence of the product action (conditional on the held GP-04 clause).** Near each
`u`, all `T_ψ` have power series at `u` with a common radius and a common majorant over the whole product group. -/
theorem act_uniform_analytic (H : PHyp I DI) (hDI : AnalyticOnNhd ℝ DI univ)
    (hGP04 : HeldGP04AnalyticInitialDependence E (E →L[ℝ] L1 ℝ)) (u : E) :
    ∃ r > (0 : ℝ), ∃ C : ℝ, ∀ ψ : Torus, ∃ p : FormalMultilinearSeries ℝ E E,
      HasFPowerSeriesOnBall (act DI ψ) p u (ENNReal.ofReal r) ∧ ∀ n, ‖p n‖ * r ^ n ≤ C :=
  hGP04 Torus DI (fun ψ => Lgen (lift ψ)) (Real.pi / 2) (fun ψ => flow DI (lift ψ)) (I ⁻¹' {I u}) u
    (H.hyp.fibre_compact u) (hDI.mono (subset_univ _))
    (fun ψ => (norm_Lgen_le (lift ψ)).trans (by linarith [norm_lift_le ψ]))
    (fun ψ x t => by
      show HasDerivAt (fun t => flow DI (lift ψ) t x) (Lgen (lift ψ) (DI (flow DI (lift ψ) t x))) t
      rw [← X_eq_Lgen]
      exact hasDerivAt_flow H.hyp (lift ψ) x t)
    (fun ψ x => flow_zero H.hyp (lift ψ) x)
    (fun ψ t _ => QuantumNLS.ProductTorusVariational.mem_fibre_flow H.hyp (lift ψ) (Set.mem_singleton (I u)) t)

/-- Each `T_ψ` is real analytic at every point (conditional on the held GP-04 clause). -/
theorem act_analyticAt (H : PHyp I DI) (hDI : AnalyticOnNhd ℝ DI univ)
    (hGP04 : HeldGP04AnalyticInitialDependence E (E →L[ℝ] L1 ℝ)) (ψ : Torus) (u : E) :
    AnalyticAt ℝ (act DI ψ) u := by
  obtain ⟨r, hr, C, hp⟩ := act_uniform_analytic H hDI hGP04 u
  obtain ⟨p, hp, -⟩ := hp ψ
  exact hp.analyticAt

/-- The inverse `T_{ψ⁻¹}` of `T_ψ` is real analytic as well (conditional on the held GP-04 clause). -/
theorem act_inv_analyticAt (H : PHyp I DI) (hDI : AnalyticOnNhd ℝ DI univ)
    (hGP04 : HeldGP04AnalyticInitialDependence E (E →L[ℝ] L1 ℝ)) (ψ : Torus) (u : E) :
    AnalyticAt ℝ (act DI ψ⁻¹) u ∧ (∀ v, act DI ψ⁻¹ (act DI ψ v) = v) ∧ (∀ v, act DI ψ (act DI ψ⁻¹ v) = v) := by
  refine ⟨act_analyticAt H hDI hGP04 ψ⁻¹ u, fun v => ?_, fun v => ?_⟩
  · rw [← act_mul H.hyp H.nonneg H.proper H.periodic, inv_mul_cancel, act_one H.hyp H.nonneg H.proper H.periodic]
  · rw [← act_mul H.hyp H.nonneg H.proper H.periodic, mul_inv_cancel, act_one H.hyp H.nonneg H.proper H.periodic]

end QuantumNLS.ProductTorusAnalytic

#print axioms QuantumNLS.ProductTorusAnalytic.act_uniform_analytic
#print axioms QuantumNLS.ProductTorusAnalytic.act_analyticAt
#print axioms QuantumNLS.ProductTorusAnalytic.act_inv_analyticAt
