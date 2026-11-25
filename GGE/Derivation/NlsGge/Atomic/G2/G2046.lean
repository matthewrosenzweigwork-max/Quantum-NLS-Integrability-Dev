import NlsGge.GK38.AbelianZeroGap
import NlsGge.GK38.ContourAction
import NlsGge.GK38.StdRootBranchesProducts
import NlsGge.GK38.TauGammaCircleMoments
import NlsGge.GK38.RealTypeSpectrum

/- G2-046 production kit (proof development; target NlsGge/Atomic/G2/G2046.lean). Proof from G2046_PROOF01 (req 79822242-69e4-4a3b-bd47-cafa50c76354, exit 0). Gap defs hosted here until G2-028 lands.
   Statement: STATEMENTS/G2.md "## G2-046" (verbatim). Gap definitions copied byte-identically from
   DEFINITIONS/G2.lean.md (to be hosted by G2-028; this file hosts them until then).
   Route: thicken the closed-ball analyticity to an open ball (compactness), then the production
   p2Abelian_zero_in_gap38 (AbelianZeroGap.lean:12) with the omitted index n := m+1 (its _hmn is unused),
   and CircleIntegrable from continuity on the sphere (sphere ⊆ actionCutDomain38, canonRoot38 analytic and nonzero). -/

set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

def gapSegment (φ : PotPair) (n : ℤ) : Set ℂ :=
  segment ℝ (lamMinus φ n) (lamPlus φ n)

def gap (φ : PotPair) (n : ℤ) : ℂ := lamPlus φ n - lamMinus φ n

namespace G2046Aux

/-- Analyticity on a closed ball is inherited by a slightly larger open ball (compactness). -/
theorem thick_analytic (c : ℂ) (r : ℝ) (hr : 0 ≤ r) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) :
    ∃ δ : ℝ, 0 < δ ∧ AnalyticOnNhd ℂ f (ball c (r + δ)) := by
  have hV : IsOpen {x : ℂ | AnalyticAt ℂ f x} := isOpen_analyticAt ℂ f
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall c r).exists_cthickening_subset_open hV
    (fun z hz => hf z hz)
  refine ⟨δ, hδ, fun z hz => ?_⟩
  have hz' : z ∈ cthickening δ (closedBall c r) := by
    rw [cthickening_closedBall hδ.le hr]
    rw [mem_ball] at hz
    exact mem_closedBall.mpr (by linarith)
  exact hsub hz'

end G2046Aux

open G2046Aux

theorem G2_046 (u : PhysicalL2) (m : ℤ)
    (C : ℤ → ℂ) (R : ℤ → ℝ) (hCR : IsolatingFamily38 (realSlice u) C R)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (C m) (R m)))
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ gapSegment (realSlice u) m → (f (x : ℂ)).im=0)
    (hperiod : circleIntegral (fun z => f z/canonRoot38 (realSlice u) z)
      (C m) (R m) = 0) :
    CircleIntegrable (fun z => f z/canonRoot38 (realSlice u) z) (C m) (R m) ∧
    ∃ x : ℝ, (x : ℂ) ∈ gapSegment (realSlice u) m ∧ f (x : ℂ)=0 := by
  have hr : 0 < R m := isolating_radius_pos38 hCR m
  obtain ⟨δ, hδ, hfU⟩ := thick_analytic (C m) (R m) hr.le f hf
  have hsph : sphere (C m) (R m) ⊆ ball (C m) (R m + δ) :=
    sphere_subset_ball (by linarith)
  obtain ⟨x, hx, hfx⟩ := p2Abelian_zero_in_gap38 m (m + 1) (by omega) u C R hCR
    (ball (C m) (R m + δ)) f isOpen_ball (convex_ball _ _) hsph hfU
    (fun x hx => hreal x hx) hperiod
  refine ⟨?_, x, hx, hfx⟩
  apply ContinuousOn.circleIntegrable hr.le
  intro z hz
  have hzc : z ∈ closedBall (C m) (R m) := sphere_subset_closedBall hz
  have hzgap : z ∉ gapSegments38 (realSlice u) := fixed_sphere_subset (realSlice u) C R hCR m hz
  have hdom : (realSlice u, z) ∈ rootDomain38 := ⟨realSlice_mem_gkW u, hzgap⟩
  have hca : AnalyticAt ℂ (fun w : ℂ => canonRoot38 (realSlice u) w) z :=
    ((canonRoot_analytic38 (realSlice u, z) hdom).comp
      (analyticAt_const.prod analyticAt_id) : AnalyticAt ℂ _ z)
  have hfa : AnalyticAt ℂ f z := hf z hzc
  exact ((hfa.continuousAt.div hca.continuousAt
    (canonRoot_ne_zero38 (realSlice u) (realSlice_mem_gkW u) z hzgap)).continuousWithinAt)

end
end NlsGge.GKDefinitionDesign
