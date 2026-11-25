import Mathlib
import QuantumNLS.Local002Discharge

/-! LOCAL-002 Limit 1 bridge: the printed `u` is the DEF-001 profile `u ∈ L²(𝕋_L)` entering `𝓛_u` through its interval
representative `circleRep u : x ↦ u(x mod L)` (`LocalSpectralOperator`).  `Local002Discharge.reset_analytic_projections`
ranges over `u ∈ Lp ℂ 2 (μI L) = L²(0,L)`.

Bridge.  `toInterval L : L²(𝕋_L) ≃ₗᵢ[ℂ] L²(0,L)` is the inverse of the accepted LOCAL-001 isometry `intervalToCircleIso`
(`Local001TransportB`), `toInterval v = circleToInterval v = Lp.compMeasurePreserving (x ↦ (x : 𝕋_L)) v`; it satisfies
`⇑(toInterval v) =ᵐ[μI L] circleRep v`.  The operator `𝓛_u`, its resolvent, the Riesz projections depend on `u` only through
its a.e.-class on `(0,L]` (`resolvent_congr`).  Hence every conclusion transfers to `u ∈ L²(𝕋_L)` with the same `ρ`, `C`
(`‖toInterval v‖ = ‖v‖`), and the profile map into the interval ball is a continuous (indeed isometric) real-linear map
(`toIntervalR : L²(𝕋_L) →L[ℝ] L²(0,L)`) so real-analyticity transfers by composition. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local002Bridge
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.PhysicalTensor

variable {L κ : ℝ}

/-- The profile-to-interval isometry (inverse of the accepted LOCAL-001 `intervalToCircleIso`). -/
def toInterval (L : ℝ) [Fact (0 < L)] : L2T L ≃ₗᵢ[ℂ] Lp ℂ 2 (μI L) :=
  (QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.intervalToCircleIso L).symm

/-- The same map as a continuous real-linear map. -/
def toIntervalR (L : ℝ) [Fact (0 < L)] : L2T L →L[ℝ] Lp ℂ 2 (μI L) :=
  ((toInterval L).toLinearIsometry.toContinuousLinearMap).restrictScalars ℝ

lemma toIntervalR_apply (L : ℝ) [Fact (0 < L)] (v : L2T L) : toIntervalR L v = toInterval L v := rfl

lemma norm_toInterval (L : ℝ) [Fact (0 < L)] (v : L2T L) : ‖toInterval L v‖ = ‖v‖ :=
  LinearIsometryEquiv.norm_map _ v

lemma toInterval_eq (L : ℝ) [Fact (0 < L)] (v : L2T L) :
    toInterval L v = QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.circleToInterval L v := by
  unfold toInterval
  refine (QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.intervalToCircleIso L).symm_apply_eq.mpr ?_
  exact (QuantumNLS.ResetFreeResolventLOCAL001.CompletionB.intervalToCircle_circleToInterval L v).symm

/-- The interval class of the profile is the DEF-001 representative `x ↦ u(x mod L)`. -/
lemma toInterval_coe (L : ℝ) [Fact (0 < L)] (v : L2T L) :
    ((toInterval L v : Lp ℂ 2 (μI L)) : ℝ → ℂ) =ᵐ[μI L] circleRep v := by
  rw [toInterval_eq]
  exact Lp.coeFn_compMeasurePreserving v _

/-! ### Dependence on the a.e.-class only -/

lemma LuGraph_congr {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (σ : ℤˣ) :
    LuGraph L κ u σ = LuGraph L κ u' σ := by
  ext p
  simp only [LuGraph, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hh, hrep, hb, hac⟩
    refine ⟨g, hh, hrep, hb, ?_⟩
    filter_upwards [hac, h] with x hx hx'
    rw [hx, hx']
  · rintro ⟨g, hh, hrep, hb, hac⟩
    refine ⟨g, hh, hrep, hb, ?_⟩
    filter_upwards [hac, h] with x hx hx'
    rw [hx, hx']

lemma isResolvent_congr {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (σ : ℤˣ) (z : ℂ)
    (R : H2 L →L[ℂ] H2 L) : IsResolvent L κ u σ z R ↔ IsResolvent L κ u' σ z R := by
  unfold IsResolvent
  rw [LuGraph_congr h σ]

lemma resolvent_congr {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (σ : ℤˣ) (z : ℂ) :
    LocalSpectral.resolvent L κ u σ z = LocalSpectral.resolvent L κ u' σ z := by
  by_cases hex : ∃ R, IsResolvent L κ u σ z R
  · obtain ⟨R, hR⟩ := hex
    rw [resolvent_eq hR, resolvent_eq ((isResolvent_congr h σ z R).mp hR)]
  · have hex' : ¬ ∃ R, IsResolvent L κ u' σ z R := fun ⟨R, hR⟩ => hex ⟨R, (isResolvent_congr h σ z R).mpr hR⟩
    unfold LocalSpectral.resolvent
    rw [dif_neg hex, dif_neg hex']

lemma perturbedProj_congr {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) :
    perturbedProj L κ u n r = perturbedProj L κ u' n r := by
  unfold perturbedProj rieszProj
  simp only [resolvent_congr h]

lemma reducedMatrix_congr {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) :
    reducedMatrix L κ u n r = reducedMatrix L κ u' n r := by
  have h1 : perturbedProj L κ u n r = perturbedProj L κ u' n r := perturbedProj_congr h n r
  have h2 : dressedIntegral L κ u n r = dressedIntegral L κ u' n r := by
    unfold dressedIntegral
    simp only [resolvent_congr h]
  unfold reducedMatrix normalizedIsometry compression
  rw [h1, h2]

/-- **LOCAL-002 `lem:reset-analytic-projections` for the DEF-001 profile `u ∈ L²(𝕋_L)`** entering through
`circleRep u`, with no hypothesis beyond `0 < L` and the contour radius: same `ρ`, `C` as the interval statement. -/
theorem reset_analytic_projections_profile [Fact (0 < L)] (hL : 0 < L) {r : ℝ}
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, ∀ n : ℤ,
      (∀ u : L2T L, ‖u‖ < ρ →
        IsSelfAdjointGraph (LuGraph L κ (circleRep u) (parity n)) ∧
        (∀ z : ℂ, ‖z - (pm L n : ℂ)‖ = r →
          ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (circleRep u) (parity n) z R) ∧
        Module.finrank ℂ (LinearMap.range
          (perturbedProj L κ (circleRep u) n r : H2 L →ₗ[ℂ] H2 L)) = 2 ∧
        ‖perturbedProj L κ (circleRep u) n r - freeProj L κ n r‖ ≤ C * ‖u‖) ∧
      AnalyticOnNhd ℝ (fun u : L2T L => perturbedProj L κ (circleRep u) n r) (ball 0 ρ) := by
  obtain ⟨ρ, hρ, C, h⟩ := QuantumNLS.Local002Discharge.reset_analytic_projections (κ := κ) hL hr hr2
  refine ⟨ρ, hρ, C, fun n => ⟨fun v hv => ?_, ?_⟩⟩
  · have hv' : ‖toInterval L v‖ < ρ := by rw [norm_toInterval]; exact hv
    obtain ⟨a, b, c, d⟩ := (h n).1 (toInterval L v) hv'
    have e := (toInterval_coe L v).symm
    rw [norm_toInterval] at d
    refine ⟨?_, fun z hz => ?_, ?_, ?_⟩
    · rw [LuGraph_congr e]; exact a
    · obtain ⟨R, hR⟩ := b z hz
      exact ⟨R, (isResolvent_congr e _ _ R).mpr hR⟩
    · rw [perturbedProj_congr (κ := κ) e]; exact c
    · rw [perturbedProj_congr (κ := κ) e]; exact d
  · have hcomp : AnalyticOnNhd ℝ
        ((fun w : Lp ℂ 2 (μI L) => perturbedProj L κ (w : ℝ → ℂ) n r) ∘ toIntervalR L) (ball 0 ρ) := by
      refine AnalyticOnNhd.comp (t := ball (0 : Lp ℂ 2 (μI L)) ρ) (h n).2
        ((toIntervalR L).analyticOnNhd _) ?_
      intro v hv
      rw [mem_ball_zero_iff] at hv ⊢
      rw [toIntervalR_apply, norm_toInterval]; exact hv
    convert hcomp using 1
    funext v
    exact (perturbedProj_congr (κ := κ) (toInterval_coe L v).symm n r)

end QuantumNLS.Local002Bridge
#print axioms QuantumNLS.Local002Bridge.reset_analytic_projections_profile
#print axioms QuantumNLS.Local002Bridge.toInterval_coe
#print axioms QuantumNLS.Local002Bridge.reducedMatrix_congr
