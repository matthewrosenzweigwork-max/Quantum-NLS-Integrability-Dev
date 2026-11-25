import Mathlib
import NlsGge.ThirdConsultation.G5.G5033Support1
import NlsGge.ThirdConsultation.G5033Host
import NlsGge.Atomic.G5.G5024
import NlsGge.ThirdConsultation.G2.G2071Support1
import NlsGge.ThirdConsultation.G2.SourceFamilyBasic
-- MODULE: NlsGge.Atomic.G5.G5033

/- G5-033 PRODUCTION (proof development, AUTHOR; not self-reviewed). Differentiate the normalized psi product along an angle field.
   REPAIR 1 (PRODUCTION02): qualified the support call as NlsGge.ThirdConsultation.G5033Support1.assembly (unknown identifier
   G5033Support1.assembly from namespace NlsGge.GKDefinitionDesign; qualification only).
   REPAIR 2 (PRODUCTION03, proof development): the support module is LANDED as module
   NlsGge.ThirdConsultation.G5.G5033Support1 (NlsGge/ThirdConsultation/G5/G5033Support1.lean, root ruling).
   The import line now names that module. Declarations stay in namespace NlsGge.ThirdConsultation.G5033Support1,
   so the call NlsGge.ThirdConsultation.G5033Support1.assembly is unchanged.
   Head: STATEMENTS/G5.md (followup4) lines 827-857, verbatim except the lexical repair lambda -> z (Lean keyword;
   same repair as landed G5-024) and the hypothesis name hλ -> hz (same lexical repair).
   Premise source: hF is taken from the LANDED G2071S1.structural conjuncts 2 and 4 (no G2-064 or G2-071 hypothesis).
   Proof: G5033Support1.assembly at F := sourceF n, φ := realSlice u, z := z, with H the pairPoissonCLM vector
   (-I • (pairGradientCLM M).2, I • (pairGradientCLM M).1), M := angleDerivative m φ. hm is unused. -/
set_option autoImplicit false

open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.GKDefinitionDesign
noncomputable section

theorem G5033 (u : PhysicalL2) (m n : ℤ)
    (hm : gamma2 (realSlice u) m ≠ 0) (z : ℂ)
    (hz : ∀ k : ℤ, k ≠ n → z ≠ psiRootAt n k (realSlice u)) :
  let φ := realSlice u
  Memℓp (fun k : ℤ => if k = n then 0 else
    pairPoissonCLM (fderiv ℂ (psiRootAt n k) φ) (angleDerivative m φ)) 2 ∧
  Summable (fun k : ℤ => if k = n then 0 else
    pairPoissonCLM (fderiv ℂ (psiRootAt n k) φ) (angleDerivative m φ) /
      (psiRootAt n k φ - z)) ∧
  pairPoissonCLM (fderiv ℂ (psiAt n z) φ) (angleDerivative m φ) =
    psiAt n z φ * ∑' k : ℤ, if k = n then 0 else
      pairPoissonCLM (fderiv ℂ (psiRootAt n k) φ) (angleDerivative m φ) /
        (psiRootAt n k φ - z) := by
  intro φ
  have hF : DifferentiableAt ℂ (sourceF n) (realSlice u) :=
    (G2071S1.structural.2.2.2.1 n (realSlice u)
      (G2071S1.structural.2.1 (Set.mem_range_self u))).differentiableAt
  obtain ⟨h1, h2, h3⟩ := NlsGge.ThirdConsultation.G5033Support1.assembly n (sourceF n) (realSlice u) hF z hz
    (-Complex.I • (pairGradientCLM (angleDerivative m (realSlice u))).2,
      Complex.I • (pairGradientCLM (angleDerivative m (realSlice u))).1)
  exact ⟨h1, h2, h3⟩

end
end NlsGge.GKDefinitionDesign
