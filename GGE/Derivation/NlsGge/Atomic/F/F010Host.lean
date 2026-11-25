import Mathlib
import NlsGge.Birkhoff.F08Bare38b
import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import NlsGge.ThirdConsultation.G6.SobolevBirkhoff

/- F010 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/F/F010Host.lean. Hosts ONCE the F-010 design names (R14_AUDIT_F2 row F-010: "HOSTABLE |
   finiteDensity, finiteNormalizer, finiteGapLaw, finiteGapApprox, finiteGapNormalizer, finiteGapField,
   inverseOnSequence"), plus their literal dependencies finiteTInv and inverseOnSobolev. Bodies byte-identical to
   followup13 definitions_design_20261027/DEFINITIONS/F.lean.md:145-178 (sha256 b429288d...), namespace
   NlsGge.ThirdConsultation.F, block opens (F.lean.md:46-50 header + `open NlsGge.GKDefinitionDesign`).
   grep NlsGge/ (2026-11-02): none of these names exists. birkhoffSobolev/inverseBirkhoffSobolev are imported from
   the landed G6 SobolevBirkhoff host, PN38 from Birkhoff/F08Bare38b, gammaM38/gaussianRealization38 from
   FiniteOrderGaussianTail38, Hm1/Rm38/FinvH38 from Birkhoff/F05Identity38; none is redeclared.
   LEXICAL REPAIR (recorded): the block's Lean-3 line `local attribute [instance] Classical.propDecidable`
   (F.lean.md:137) is not Lean 4 syntax; it is omitted (no hosted body uses decidability). Not hosted here:
   sobolevCoe, finiteT, finiteA, finiteD (consumers F-012/F-013/F-014 own them). -/
set_option autoImplicit false

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.HierarchyRiccati.Core
open NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Measure
open NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.F
noncomputable section
open NlsGge.GKDefinitionDesign

def finiteTInv (m : ℕ) (z : Hm1 m) : Hm1 m :=
  ofCarrier38 _ (physicalSobolevFourierEquiv38 ((m - 1 : ℕ) : ℝ)
    (inverseBirkhoffSobolev (m - 1) (toCarrier38 _ z)))

def inverseOnSobolev (m : ℕ) (z : Hm1 m) : Hm1 m :=
  FinvH38 m (finiteTInv m z)

def inverseOnSequence (m : ℕ) (z : ℤ → ℂ) : Hm1 m :=
  inverseOnSobolev m (gaussianRealization38 m z)

def finiteDensity (m : ℕ) (β : ℕ → ℝ) (z : ℤ → ℂ) : ℝ :=
  Real.exp (-Rm38 m β (inverseOnSequence m z))

def finiteNormalizer (m : ℕ) (β : ℕ → ℝ) : ℝ :=
  ∫ z, finiteDensity m β z ∂gammaM38 m β

def finiteGapLaw (m : ℕ) (β : ℕ → ℝ) : Measure (Hm1 m) :=
  ((ENNReal.ofReal (finiteNormalizer m β))⁻¹ •
    (gammaM38 m β).withDensity
      (fun z => ENNReal.ofReal (finiteDensity m β z))).map
        (inverseOnSequence m)

def finiteGapField (m N : ℕ) (z : ℤ → ℂ) : Hm1 m :=
  inverseOnSobolev m (PN38 m N z)

def finiteGapNormalizer (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∫ z, Real.exp (-Rm38 m β (finiteGapField m N z)) ∂gammaM38 m β

def finiteGapApprox (m : ℕ) (β : ℕ → ℝ) (N : ℕ) : Measure (Hm1 m) :=
  ((ENNReal.ofReal (finiteGapNormalizer m β N))⁻¹ •
    (gammaM38 m β).withDensity
      (fun z => ENNReal.ofReal
        (Real.exp (-Rm38 m β (finiteGapField m N z))))).map
          (finiteGapField m N)

end
end NlsGge.ThirdConsultation.F
