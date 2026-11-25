import Mathlib
import NlsGge.Atomic.Support.ContourCycleCauchy
import NlsGge.ThirdConsultation.G2.G2037P4M1
import NlsGge.ThirdConsultation.G2.G2037P4M2
import NlsGge.ThirdConsultation.G2.G2037P4M4
import NlsGge.ThirdConsultation.G2.G2037P5A
import NlsGge.ThirdConsultation.G2.G2037P5B
import NlsGge.ThirdConsultation.G2.G2037P4A
import NlsGge.ThirdConsultation.G2.G2037C5P1
import NlsGge.ThirdConsultation.G2.G2037Conj14
import NlsGge.ThirdConsultation.G2.G2037P4Gap

/- G2-037 HEAD ASSEMBLY (proof development, AUTHOR; not self-reviewed; semantic fidelity gate open).
   Head `G2_037`, verbatim from root/gpt6pro_followup5/handoff/definitions_design_20261027/STATEMENTS/G2.md
   section G2-037 (no later Pro round restates it).
   Conjuncts (1)-(4): `g2037_conj_1_to_4` (proof development).
   Conjunct (5): `g2037_conj5` := `conjunct5_of_primitive` (proof development P5B) applied to the primitive
   `g2037p4_primitive`. The primitive is `NlsGge.G2037P4M4.exists_primitive_of_zero_periods` (M4) with
   * polygonal connectedness of `(finiteGapCuts u S)ᶜ`: M2 (`polygonal_connected_compl_M2`; the cuts are
     real by `lamPlus_real` and bounded by `cuts_bounded_M2`),
   * vanishing closed-chain periods: the homology cancellation `cancel_integral_zero` (M1) applied to the
     gap-cycle package `g2037p4_hgap` (index 1 on the own cut, 0 on other cuts, zero period).
   `hQ` is `product_expansion` (the unfolding of `standardRoot`/`stdRoot38` is definitional).
   No hypothesis is added. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory SummationFilter
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

/-- **P4.** The finite-gap differential has a single-valued primitive off the cuts. -/
theorem g2037p4_primitive (u : PhysicalL2) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n) :
    ∃ F : ℂ → ℂ, ∀ z : ℂ, z ∉ finiteGapCuts u S →
      HasDerivAt F (finiteGapDifferential u S z) z := by
  classical
  obtain ⟨G, hGU, hGpat, hG0⟩ := g2037p4_hgap u S hS
  have hclosed : IsClosed (finiteGapCuts u S) :=
    NlsGge.G2037P5.cuts_isClosed_G2037P5 (lamMinus (realSlice u)) (lamPlus (realSlice u)) S
  have hf : DifferentiableOn ℂ (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ :=
    (g2037s1_fgd_analyticOn u S).differentiableOn
  have hpre : ∀ k ∈ S, IsPreconnected (gapSegment (realSlice u) k) := fun k _ =>
    (convex_segment (lamMinus (realSlice u) k) (lamPlus (realSlice u) k)).isPreconnected
  have hc : ∀ k ∈ S, lamMinus (realSlice u) k ∈ gapSegment (realSlice u) k := fun k _ =>
    left_mem_segment ℝ _ _
  have hper : ∀ {a : ℂ} (L : NlsGge.Atomic.ContourChain.Chain a a),
      L.trace ⊆ (finiteGapCuts u S)ᶜ →
      L.integral (fun w => ContinuousLinearMap.toSpanSingleton ℂ (finiteGapDifferential u S w))
        = 0 := by
    intro a L hL
    have hΓ : (NlsGge.Atomic.ContourChain.Cycle.single ⟨a, L⟩).range ⊆ (finiteGapCuts u S)ᶜ := by
      rw [NlsGge.Atomic.ContourChain.Cycle.range_single]
      exact hL
    have h0 := NlsGge.G2037P4M1.cancel_integral_zero
      (cut := fun k => gapSegment (realSlice u) k) (S := S) (U := (finiteGapCuts u S)ᶜ)
      rfl hclosed hpre hc G hGU hGpat hf hG0 (NlsGge.Atomic.ContourChain.Cycle.single ⟨a, L⟩) hΓ
    rwa [G2037P4GapAux.cycle_integral_single] at h0
  have hreal : ∀ z ∈ finiteGapCuts u S, z.im = 0 := by
    intro z hz
    obtain ⟨j, _, hj⟩ := Set.mem_iUnion₂.1 hz
    obtain ⟨hp, hm⟩ := lamPlus_real u j
    exact NlsGge.G2037P4M2.segment_im_zero_M2 (by rw [hm]; exact Complex.ofReal_im _)
      (by rw [hp]; exact Complex.ofReal_im _) z hj
  have hbdd : Bornology.IsBounded (finiteGapCuts u S) :=
    NlsGge.G2037P4M2.cuts_bounded_M2 (lamMinus (realSlice u)) (lamPlus (realSlice u)) S
  have hconn : ∀ z ∈ (finiteGapCuts u S)ᶜ, ∀ w ∈ (finiteGapCuts u S)ᶜ,
      Relation.ReflTransGen (fun a b : ℂ => segment ℝ a b ⊆ (finiteGapCuts u S)ᶜ) z w :=
    fun z hz w hw => NlsGge.G2037P4M2.polygonal_connected_compl_M2 _ hreal hbdd z w hz hw
  exact NlsGge.G2037P4M4.exists_primitive_of_zero_periods hclosed.isOpen_compl hf hconn hper

/-- **Conjunct (5) of `G2_037`.** -/
theorem g2037_conj5 (u : PhysicalL2) (S : Finset ℤ)
    (hS : ∀ n : ℤ, n ∈ S ↔ actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n) :
    ∃ R : ℝ, 0 < R ∧ finiteGapCuts u S ⊆ Metric.closedBall (0 : ℂ) R ∧
      ∃ f g : ℂ → ℂ,
        AnalyticOnNhd ℂ f (finiteGapCuts u S)ᶜ ∧
        (∀ z : ℂ, z ∉ finiteGapCuts u S →
          HasDerivAt f (finiteGapDifferential u S z) z) ∧
        AnalyticAt ℂ g 0 ∧
        (∀ z : ℂ, R < ‖z‖ → f z = -Complex.I*z + g z⁻¹) := by
  obtain ⟨F, hF⟩ := g2037p4_primitive u S hS
  obtain ⟨R0, hR0, hcut⟩ := g2037c5_cuts_bounded u S
  have hclosed : IsClosed (finiteGapCuts u S) :=
    NlsGge.G2037P5.cuts_isClosed_G2037P5 (lamMinus (realSlice u)) (lamPlus (realSlice u)) S
  obtain ⟨Q, hQa, hQ0, R1, hR1, hid⟩ := NlsGge.G2037P5.product_expansion S
    (fun n => tauN (realSlice u) n) (fun n => gamma2 (realSlice u) n)
    (fun n => lamDot (realSlice u) n)
  exact NlsGge.G2037P5.conjunct5_of_primitive (finiteGapDifferential u S) F (finiteGapCuts u S)
    hR0 hcut hclosed ⟨Q, hQa, hQ0, R1, hR1, fun z hz => hid z hz⟩ hF

/-- **G2-037.** -/
theorem G2_037 (u : PhysicalL2) (hfg : NlsGge.ThirdConsultation.finiteGap u) :
    ∃ S : Finset ℤ,
      (∀ n : ℤ, n ∈ S ↔
        actualGapLowerAllE02_38 u n ≠ actualGapUpperAllE02_38 u n) ∧
      AnalyticOnNhd ℂ (finiteGapDifferential u S) (finiteGapCuts u S)ᶜ ∧
      (∀ z : ℂ, (realSlice u,z) ∈ rootDomain38 →
        deriv (discrim (realSlice u)) z / canonRoot38 (realSlice u) z =
          finiteGapDifferential u S z) ∧
      (∀ (C : ℤ → ℂ) (R : ℤ → ℝ), IsolatingFamily38 (realSlice u) C R →
        ∀ n : ℤ, CircleIntegrable (finiteGapDifferential u S) (C n) (R n) ∧
          circleIntegral (finiteGapDifferential u S) (C n) (R n) = 0) ∧
      ∃ R : ℝ, 0 < R ∧ finiteGapCuts u S ⊆ Metric.closedBall (0 : ℂ) R ∧
        ∃ f g : ℂ → ℂ,
          AnalyticOnNhd ℂ f (finiteGapCuts u S)ᶜ ∧
          (∀ z : ℂ, z ∉ finiteGapCuts u S →
            HasDerivAt f (finiteGapDifferential u S z) z) ∧
          AnalyticAt ℂ g 0 ∧
          (∀ z : ℂ, R < ‖z‖ → f z = -Complex.I*z + g z⁻¹) := by
  obtain ⟨S, hS, h2, h3, h4⟩ := g2037_conj_1_to_4 u hfg
  exact ⟨S, hS, h2, h3, h4, g2037_conj5 u S hS⟩

end
end NlsGge.GKDefinitionDesign
