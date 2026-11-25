import QuantumNLS.ProductTorusComplexMultilinear
import QuantumNLS.ProductTorusAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# R-4C2E4AC7, stage C3 (Terra r167 item (c), part 3): the common bounded holomorphic extension

Source: `chapters/global/product_torus.tex`, theorem, lines 39–41 ("Near each fixed `u`, the maps `T_θ` have
holomorphic extensions in the complexified initial variable to one common neighborhood, bounded there uniformly over
the whole product group"), and the proof, "The product topology and full initial-point regularity", paragraphs 4–5.

Generic part (unconditional): let `F` be a real Hilbert space, `T : F → F` with a power series `p` at `u` on the real
ball of radius `r` and the Taylor majorant `‖p n‖ rⁿ ≤ C`. With the complexified coefficients `q n = cxSeries p n`
of stage C2 (`‖q n‖ ≤ 2ⁿ ‖p n‖`), the map `T̃ z = Σ q n ((z − ι u)ⁿ)` (`cxExt`)
* has the power series `q` at `ι u` on the complex ball of radius `r/2` (`hasFPowerSeriesOnBall_cxExt`), hence is
  complex differentiable and complex analytic there;
* is bounded by `2C` on the complex ball of radius `r/4` (`norm_cxExt_le`);
* extends `T`: `T̃ (ι x) = ι (T x)` for `‖x − u‖ < r` (`cxExt_ι`).
`holomorphic_extension_of_majorant` packages this uniformly over any family with a common radius and majorant.

Application (conditional, only through T6 on `HeldGP04AnalyticInitialDependence`): `act_holomorphic_extension`,
the printed clause for the product action: near each `u` there are `R > 0` and `M` such that every `T_ψ`
(`ψ ∈ 𝕋^ℤ`) has an extension `T̃_ψ : Cx 𝓗 → Cx 𝓗` that is complex differentiable (and complex analytic) on the
complex ball `B(ι u, R)`, bounded there by `M`, with `T̃_ψ (ι x) = ι (T_ψ x)` for `x ∈ B(u, R)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3

open Filter Topology Set Metric
open scoped NNReal ENNReal

noncomputable section

namespace QuantumNLS.ProductTorusHolomorphicExtension

open QuantumNLS.ProductTorusComplexification QuantumNLS.ProductTorusComplexMultilinear

section Generic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The complexified series extension `T̃ z = Σ q n ((z − ι u)ⁿ)`. -/
def cxExt (p : FormalMultilinearSeries ℝ F F) (u : F) (z : Cx F) : Cx F := (cxSeries p).sum (z - Cx.ι u)

omit [CompleteSpace F] in
theorem cxSeries_bound (p : FormalMultilinearSeries ℝ F F) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) (n : ℕ) : ‖cxSeries p n‖ * (r / 2) ^ n ≤ C := by
  have e : (2 : ℝ) ^ n * (r / 2) ^ n = r ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  calc ‖cxSeries p n‖ * (r / 2) ^ n ≤ (2 ^ n * ‖p n‖) * (r / 2) ^ n :=
        mul_le_mul_of_nonneg_right (norm_cxSeries_le p n) (by positivity)
    _ = ‖p n‖ * r ^ n := by rw [← e]; ring
    _ ≤ C := hC n

omit [CompleteSpace F] in
theorem radius_cxSeries (p : FormalMultilinearSeries ℝ F F) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) : ENNReal.ofReal (r / 2) ≤ (cxSeries p).radius := by
  have h := (cxSeries p).le_radius_of_bound C (r := (r / 2).toNNReal) (fun n => by
    rw [Real.coe_toNNReal _ (by positivity)]
    exact cxSeries_bound p hr hC n)
  exact h

/-- `T̃` has the power series `q = cxSeries p` at `ι u` on the complex ball of radius `r/2`. -/
theorem hasFPowerSeriesOnBall_cxExt (p : FormalMultilinearSeries ℝ F F) (u : F) {r C : ℝ} (hr : 0 < r)
    (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) :
    HasFPowerSeriesOnBall (cxExt p u) (cxSeries p) (Cx.ι u) (ENNReal.ofReal (r / 2)) := by
  have hrad := radius_cxSeries p hr hC
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (r / 2) := ENNReal.ofReal_pos.2 (by positivity)
  have H0 := ((cxSeries p).hasFPowerSeriesOnBall (hpos.trans_le hrad)).mono hpos hrad
  have H1 := H0.comp_sub (Cx.ι u)
  rw [zero_add] at H1
  exact H1

omit [CompleteSpace F] in
/-- `T̃` is bounded by `2C` on the complex ball of radius `r/4`. -/
theorem norm_cxExt_le (p : FormalMultilinearSeries ℝ F F) (u : F) {r C : ℝ}
    (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) (z : Cx F) (hz : z ∈ ball (Cx.ι u) (r / 4)) : ‖cxExt p u z‖ ≤ 2 * C := by
  have hy : ‖z - Cx.ι u‖ < r / 4 := mem_ball_iff_norm.1 hz
  have hb : ∀ n : ℕ, ‖cxSeries p n (fun _ => z - Cx.ι u)‖ ≤ C * (1 / 2) ^ n := fun n => by
    have e : (2 : ℝ) ^ n * (r / 4) ^ n = r ^ n * (1 / 2) ^ n := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      ring
    calc ‖cxSeries p n (fun _ => z - Cx.ι u)‖ ≤ ‖cxSeries p n‖ * ∏ _i : Fin n, ‖z - Cx.ι u‖ :=
          (cxSeries p n).le_opNorm _
      _ = ‖cxSeries p n‖ * ‖z - Cx.ι u‖ ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ (2 ^ n * ‖p n‖) * (r / 4) ^ n :=
          mul_le_mul (norm_cxSeries_le p n) (pow_le_pow_left₀ (norm_nonneg _) hy.le n)
            (by positivity) (by positivity)
      _ = (‖p n‖ * r ^ n) * (1 / 2) ^ n := by
          rw [show (2 : ℝ) ^ n * ‖p n‖ * (r / 4) ^ n = ‖p n‖ * (2 ^ n * (r / 4) ^ n) by ring, e]
          ring
      _ ≤ C * (1 / 2) ^ n := mul_le_mul_of_nonneg_right (hC n) (by positivity)
  have h := tsum_of_norm_bounded (hasSum_geometric_two.mul_left C) hb
  calc ‖cxExt p u z‖ = ‖∑' n, cxSeries p n (fun _ => z - Cx.ι u)‖ := rfl
    _ ≤ C * 2 := h
    _ = 2 * C := mul_comm _ _

omit [CompleteSpace F] in
/-- `T̃` extends `T`: `T̃ (ι x) = ι (T x)` on the real ball of radius `r`. -/
theorem cxExt_ι {T : F → F} {p : FormalMultilinearSeries ℝ F F} {u : F} {r : ℝ}
    (hT : HasFPowerSeriesOnBall T p u (ENNReal.ofReal r)) (x : F) (hx : x ∈ ball u r) :
    cxExt p u (Cx.ι x) = Cx.ι (T x) := by
  have hy : x - u ∈ Metric.eball (0 : F) (ENNReal.ofReal r) := by
    rw [Metric.eball_ofReal, mem_ball_zero_iff, ← dist_eq_norm]
    exact hx
  have h2 := ContinuousLinearMap.hasSum (ιL : F →L[ℝ] Cx F) (hT.hasSum hy)
  have hux : u + (x - u) = x := by abel
  rw [hux] at h2
  have e : (fun n => cxSeries p n (fun _ => Cx.ι x - Cx.ι u)) = fun n => Cx.ι (p n (fun _ => x - u)) := by
    funext n
    rw [← ι_sub, cxSeries_ι]
  have h3 : HasSum (fun n => cxSeries p n (fun _ => Cx.ι x - Cx.ι u)) (Cx.ι (T x)) := by
    rw [e]
    exact h2
  exact h3.tsum_eq

/-- **Common bounded holomorphic extension from a uniform Taylor majorant** (generic, unconditional). -/
theorem holomorphic_extension_of_majorant {ι : Type*} (T : ι → F → F) (u : F) {r C : ℝ} (hr : 0 < r)
    (hT : ∀ i, ∃ p : FormalMultilinearSeries ℝ F F,
      HasFPowerSeriesOnBall (T i) p u (ENNReal.ofReal r) ∧ ∀ n, ‖p n‖ * r ^ n ≤ C) :
    ∃ R > (0 : ℝ), ∃ M : ℝ, ∀ i, ∃ Tc : Cx F → Cx F,
      DifferentiableOn ℂ Tc (ball (Cx.ι u) R) ∧ AnalyticOnNhd ℂ Tc (ball (Cx.ι u) R) ∧
      (∀ z ∈ ball (Cx.ι u) R, ‖Tc z‖ ≤ M) ∧ ∀ x ∈ ball u R, Tc (Cx.ι x) = Cx.ι (T i x) := by
  refine ⟨r / 4, by positivity, 2 * C, fun i => ?_⟩
  obtain ⟨p, hp, hC⟩ := hT i
  have H := hasFPowerSeriesOnBall_cxExt p u hr hC
  have hsub : ball (Cx.ι u) (r / 4) ⊆ Metric.eball (Cx.ι u) (ENNReal.ofReal (r / 2)) := by
    rw [Metric.eball_ofReal]
    exact ball_subset_ball (by linarith)
  refine ⟨cxExt p u, H.differentiableOn.mono hsub, fun z hz => H.analyticOnNhd z (hsub hz),
    fun z hz => norm_cxExt_le p u hC z hz, fun x hx => cxExt_ι hp x (ball_subset_ball (by linarith) hx)⟩

end Generic

section Application

open _root_.HilbertL1Compact (L1)
open QuantumNLS.ProductTorusGenerator QuantumNLS.ProductTorusAction QuantumNLS.ProductTorusPrimitive
  QuantumNLS.ProductTorusAnalytic
open QuantumNLS.Ext025B6TorusCoordinates (Torus)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
attribute [local instance] InnerProductSpace.complexToReal

/-- **The printed common bounded holomorphic extension** (conditional on the held GP-04 clause, through T6): near
each `u`, every `T_ψ`, `ψ ∈ 𝕋^ℤ`, extends to `T̃_ψ : Cx 𝓗 → Cx 𝓗`, complex differentiable and complex analytic on
one common complex ball `B(ι u, R)`, bounded there by one `M` uniformly in `ψ`, with `T̃_ψ (ι x) = ι (T_ψ x)`. -/
theorem act_holomorphic_extension {I : E → L1 ℝ} {DI : E → (E →L[ℝ] L1 ℝ)} (H : PHyp I DI)
    (hDI : AnalyticOnNhd ℝ DI univ) (hGP04 : HeldGP04AnalyticInitialDependence E (E →L[ℝ] L1 ℝ)) (u : E) :
    ∃ R > (0 : ℝ), ∃ M : ℝ, ∀ ψ : Torus, ∃ Tc : Cx E → Cx E,
      DifferentiableOn ℂ Tc (ball (Cx.ι u) R) ∧ AnalyticOnNhd ℂ Tc (ball (Cx.ι u) R) ∧
      (∀ z ∈ ball (Cx.ι u) R, ‖Tc z‖ ≤ M) ∧ ∀ x ∈ ball u R, Tc (Cx.ι x) = Cx.ι (act DI ψ x) := by
  obtain ⟨r, hr, C, hp⟩ := act_uniform_analytic H hDI hGP04 u
  exact holomorphic_extension_of_majorant (fun ψ : Torus => act DI ψ) u hr hp

end Application

end QuantumNLS.ProductTorusHolomorphicExtension

#print axioms QuantumNLS.ProductTorusHolomorphicExtension.hasFPowerSeriesOnBall_cxExt
#print axioms QuantumNLS.ProductTorusHolomorphicExtension.norm_cxExt_le
#print axioms QuantumNLS.ProductTorusHolomorphicExtension.cxExt_ι
#print axioms QuantumNLS.ProductTorusHolomorphicExtension.holomorphic_extension_of_majorant
#print axioms QuantumNLS.ProductTorusHolomorphicExtension.act_holomorphic_extension
