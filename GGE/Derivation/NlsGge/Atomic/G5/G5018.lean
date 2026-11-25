import Mathlib
import NlsGge.Atomic.G5.G5018Asm
import NlsGge.Atomic.G5.G5018M4
import NlsGge.Atomic.G5.G5018M5b

/- G5-018 PACKET (proof development, AUTHOR; not self-reviewed, not accepted).
   Target NlsGge/Atomic/G5/G5018.lean, namespace NlsGge.GKDefinitionDesign.
   Head `G5018` VERBATIM from Pro round 13 section 6 "Preserved final G5-018 head" except the lexical repair of the binder name `λ` (Lean keyword) to `lam`.
   Proof: `g5018_assembly` (G5018Asm) with hM4 := landed `g5018_offDiagonal_endpoint_fderiv` and
   hM5b := `g5018_diagonal_endpoint_fderiv` (G5018M5b; the diagonal hypothesis hn is the head's own hn). -/
set_option autoImplicit false

open Set Filter Topology Metric MeasureTheory
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.GK38.GradEigen38


namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5018 (u : PhysicalL2) (m n : ℤ) (lam : ℂ)
    (hm : InteriorRealDirichletGap m u) (hn : gamma2 (realSlice u) n ≠ 0) :
  2 * pairPoissonCLM (fderiv ℂ (fun φ => discrim φ lam) (realSlice u))
    (angleIntegralDerivative m n (realSlice u)) =
    psiAt n (muSeq (realSlice u) m) (realSlice u) *
      PoissonMixed38.dirInterpolation38 (realSlice u) (muSeq (realSlice u) m) lam :=
  g5018_assembly u m n lam hm hn
    (fun hmn => g5018_offDiagonal_endpoint_fderiv u m n lam hmn hm)
    (fun hmn => by subst hmn; exact g5018_diagonal_endpoint_fderiv u m lam hm hn)

end
end NlsGge.GKDefinitionDesign
