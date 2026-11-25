import Mathlib
import NlsGge.Atomic.LIB.LIB079
import NlsGge.Atomic.Support.ContourCycleCauchy

/- G2-037 CONJUNCT (5) PACKET B2 (proof development, AUTHOR; not self-reviewed; SUPPORTING, not the head).
   Path -> Cycle bridge. A closed LIB042-piecewise-C1 loop `γ` has a single finite chain `c` with
   `c.path = γ` (exists_chain_of_piecewiseC1). Its Riesz-normalized chain index off the trace equals the
   LIB015 `indexIntegral γ`, so the landed Cauchy theorem `Cycle.integral_eq_zero` applies to `γ`.
   The gap ellipse `gapCycle D` is one C1 leaf, hence LIB042-piecewise-C1. No hypothesis is added. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open scoped unitInterval
open NlsGge.GK38.Lib.SlitContours

namespace NlsGge.GKDefinitionDesign
noncomputable section

namespace G2037B2Aux

/-- The toSpanSingleton integrand and the LIB015 `complexForm` integrand agree (commutativity). -/
theorem complexForm_eq_toSpanSingleton (g : ℂ → ℂ) :
    (fun z : ℂ => ContinuousLinearMap.toSpanSingleton ℂ (g z)) = complexForm g := by
  funext z
  ext t
  simp [complexForm, mul_comm]

end G2037B2Aux

open G2037B2Aux

/-- Chain index equals the LIB015 index off the trace of a closed chain. -/
theorem g2037b2_chain_index_eq_indexIntegral {a : ℂ}
    (c : NlsGge.Atomic.ContourChain.Chain a a) {w : ℂ} (hw : w ∉ c.trace) :
    c.index w = indexIntegral c.path w := by
  have hω : (fun z : ℂ => ContinuousLinearMap.toSpanSingleton ℂ ((z - w)⁻¹)) =
      complexForm (fun z : ℂ => (z - w)⁻¹) := complexForm_eq_toSpanSingleton _
  unfold indexIntegral
  rw [NlsGge.Atomic.ContourChain.Chain.index,
    NlsGge.Atomic.ContourChain.Chain.integral_eq_curveIntegral (c.integrable_sub_inv hw), hω]

/-- A closed piecewise-C1 path in the LIB042 sense has a chain with the same path. -/
theorem g2037b2_exists_chain {a : ℂ} (γ : Path a a) (hγ : NlsGge.Atomic.LIB042.PiecewiseC1 γ) :
    ∃ c : NlsGge.Atomic.ContourChain.Chain a a, c.path = γ :=
  NlsGge.Atomic.ContourChain.exists_chain_of_piecewiseC1 hγ

/-- The gap ellipse `gapCycle D` is LIB042-piecewise-C1 (a single C1 leaf). -/
theorem g2037b2_gapCycle_piecewiseC1 (D : DiscWithSegment) :
    NlsGge.Atomic.LIB042.PiecewiseC1 (gapCycle D) := by
  apply NlsGge.Atomic.LIB042.PiecewiseC1.ofC1
  have hd : ContDiff ℝ 1 (fun t : ℝ => ellipseParam D (2 * Real.pi * t)) := by
    simpa using ellipse_contDiff D 0 1
  refine (hd.contDiffOn).congr ?_
  intro t ht
  exact Path.extend_extends' (gapCycle D) ⟨t, ht.1, ht.2⟩

/-- Gap-cycle chain: a chain whose path is `gapCycle D`, with the same trace and the LIB015 index off it. -/
theorem g2037b2_gapCycle_chain (D : DiscWithSegment) :
    ∃ c : NlsGge.Atomic.ContourChain.Chain (ellipseParam D 0) (ellipseParam D 0),
      c.path = gapCycle D ∧ c.trace = Set.range (gapCycle D) ∧
      ∀ w : ℂ, w ∉ Set.range (gapCycle D) → c.index w = indexIntegral (gapCycle D) w := by
  obtain ⟨c, hc⟩ := g2037b2_exists_chain (gapCycle D) (g2037b2_gapCycle_piecewiseC1 D)
  refine ⟨c, hc, ?_, ?_⟩
  · unfold NlsGge.Atomic.ContourChain.Chain.trace
    rw [hc]
  · intro w hw
    have hw' : w ∉ c.trace := by
      unfold NlsGge.Atomic.ContourChain.Chain.trace
      rw [hc]
      exact hw
    rw [g2037b2_chain_index_eq_indexIntegral c hw', hc]

/-- Cauchy's theorem for one closed loop through the landed cycle theorem: if the loop lies in an
open set `U`, its index vanishes off `U`, and `f` is holomorphic on `U`, then its complex-form
integral vanishes. The single cycle is `Cycle.single ⟨a, c⟩`, whose index is the chain index. -/
theorem g2037b2_curveIntegral_eq_zero_of_index {a : ℂ} (γ : Path a a)
    (hγ : NlsGge.Atomic.LIB042.PiecewiseC1 γ)
    {U : Set ℂ} (hU : IsOpen U) (hγU : Set.range γ ⊆ U)
    (hind : ∀ w : ℂ, w ∉ U → indexIntegral γ w = 0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    curveIntegral (complexForm f) γ = 0 := by
  obtain ⟨c, hc⟩ := g2037b2_exists_chain γ hγ
  have hcU : c.trace ⊆ U := by
    unfold NlsGge.Atomic.ContourChain.Chain.trace
    rw [hc]
    exact hγU
  have hΓU : (NlsGge.Atomic.ContourChain.Cycle.single ⟨a, c⟩).range ⊆ U := by
    show (⋃ _ : Fin 1, c.trace) ⊆ U
    rw [Set.iUnion_const]
    exact hcU
  have hind' : ∀ w : ℂ, w ∉ U → (NlsGge.Atomic.ContourChain.Cycle.single ⟨a, c⟩).index w = 0 := by
    intro w hw
    have hwc : w ∉ c.trace := fun h => hw (hcU h)
    show ∑ _i : Fin 1, c.index w = 0
    rw [Fin.sum_univ_one, g2037b2_chain_index_eq_indexIntegral c hwc, hc]
    exact hind w hw
  have hcyc := (NlsGge.Atomic.ContourChain.Cycle.single ⟨a, c⟩).integral_eq_zero hU hΓU hind' hf
  have hsum : (NlsGge.Atomic.ContourChain.Cycle.single ⟨a, c⟩).integral
      (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) = curveIntegral (complexForm f) γ := by
    show ∑ _i : Fin 1, c.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (f w)) =
      curveIntegral (complexForm f) γ
    rw [Fin.sum_univ_one, NlsGge.Atomic.ContourChain.Chain.integral_eq_curveIntegral
      (c.integrable_toSpanSingleton_of_continuousOn hf.continuousOn hcU), hc,
      ← complexForm_eq_toSpanSingleton f]
  rw [← hsum]
  exact hcyc

end
end NlsGge.GKDefinitionDesign
