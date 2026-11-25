import Mathlib
import NlsGge.Atomic.G1.G1102
import NlsGge.Atomic.G5.G5029Host

/- G5-029 SUPPORT 2 (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5029Sup2.lean, namespace NlsGge.GKDefinitionDesign.
   Head `allDirichletLeft_isospectral_unique` VERBATIM from PRO_DEFINITION_RESPONSE_FP80_14.md "G5029: all-left density".
   Route: Pro asks for the norming-Dirichlet map injectivity (G1-100); the landed G1-102 packages this as
   signedDirichletData_injOn on a fixed isospectral set.  At a left endpoint antiDiscrim vanishes (perChar = antiDiscrim^2 and the
   endpoint is a periodic root), so the signed datum of every all-left point of Iso(u) is (lower endpoint, 0), the same for u and v. -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem antiDiscrim_zero_of_left (u : PhysicalL2) (n : ℤ)
    (h : gkMu u n = actualGapLowerAllE02_38 u n) :
    antiDiscrim (realSlice u) (gkMu u n : ℂ) = 0 := by
  have hsq := dirichlet_perChar_eq_anti_sq38 (realSlice u) (gkMu u n : ℂ) (gkMu_root38 u n)
  have hr : perChar (realSlice u) (gkMu u n : ℂ) = 0 := by
    rw [h]; exact (gap_endpoint_roots38 u n).1
  rw [hr] at hsq
  exact (pow_eq_zero_iff two_ne_zero).mp hsq.symm

theorem allDirichletLeft_isospectral_unique
    (u v : PhysicalL2) (hu : AllDirichletLeft u)
    (hv : AllDirichletLeft v) (hiso : isospectral u v) : u = v := by
  have huS : u ∈ isospectralSet u := fun z => rfl
  have hvS : v ∈ isospectralSet u := hiso
  refine signedDirichletData_injOn u huS hvS ?_
  funext n
  have hl := isospectral_gapLower_eq hiso n
  have e1 : gkMu u n = gkMu v n := by rw [hu n, hv n, hl]
  have e2 : (antiDiscrim (realSlice u) (gkMu u n : ℂ)).re =
      (antiDiscrim (realSlice v) (gkMu v n : ℂ)).re := by
    rw [antiDiscrim_zero_of_left u n (hu n), antiDiscrim_zero_of_left v n (hv n)]
  exact Prod.ext e1 e2

end
end NlsGge.GKDefinitionDesign
