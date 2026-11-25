import Mathlib
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.ThirdConsultation.R.R110Host
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.Birkhoff.W07Probability38e
import NlsGge.Ramer.RamerFiniteChainRule

/- R115 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/R/R115.lean.
   Packet R-115 (REUSE/EXTRACT). HEAD VERBATIM (block with opens/local notations) from followup13 STATEMENTS/R.md
   "## R-115"; owner-approved LEXICAL REPAIR 24 only: (B).ZW38 (1 use).
   Proof = Pro's route: W07_38 at the fixed (B, O) gives an existential δK with Integrable / ∫ = ZW38 / TendstoInMeasure
   for fW06_38 … δK; fW06_ae_unique_W07 with R.canonicalDelta_spec (R109Host) gives fW06_38 … δK =ᵐ
   R.actualRamerDensity (R110Host; weightedK = B.KW06_38 O by definition, R100Host); all three facts transfer along
   that a.e. equality (Integrable.congr, integral_congr_ae, TendstoInMeasure.congr_right).  Integrability is
   established (by W07_38) before the integral identity is transferred.
   canonicalDelta is used at the single actual pair (c, s, hs, hs1) only (r16 Q2(iii)); δK is the W07 witness, compared
   only through the a.e. uniqueness theorem, never chosen across potentials.
   Own imports declare both notation RHSs (B1).  RamerFiniteChainRule import-only.
   Generic replica R115_REPLICA01 lane cb4a441f.  MAIN-ONLY: needs ROOT MAIN PROBE (R115_RECEIVER01). -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Ramer
open NlsGge.Analysis.RegularizedDeterminant
namespace NlsGge.ThirdConsultation.R
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem actual_fN_tendstoInMeasure {lo up : ℝ}
    (c : BoundedCoefficients lo up) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    let hs1 : s ≤ 1 := by linarith
    Integrable (actualRamerDensity c s hs hs1) (fullWeightedSequenceGaussian c s) ∧
    (∫ x : ECarrier38 c s, actualRamerDensity c s hs hs1 x
      ∂(fullWeightedSequenceGaussian c s)) = (B).ZW38 c.val ∧
    TendstoInMeasure (fullWeightedSequenceGaussian c s)
      (fun N : ℕ => fN38 c s N) atTop (actualRamerDensity c s hs hs1) := by
  intro hs1
  obtain ⟨δK, hδ, -, hInt, hZ, hT, -⟩ := NlsGge.Birkhoff.W07_38 B O c s hs hs'
  have hae : fW06_38 c s hs ((B).KW06_38 O c hs1) δK =ᵐ[fullWeightedSequenceGaussian c s]
      actualRamerDensity c s hs hs1 :=
    NlsGge.Birkhoff.fW06_ae_unique_W07 c s B O hs hs1 δK (canonicalDelta c s hs hs1) hδ
      (canonicalDelta_spec c s hs hs1)
  refine ⟨hInt.congr hae, ?_, hT.congr_right hae⟩
  exact (integral_congr_ae hae).symm.trans hZ

end NlsGge.ThirdConsultation.R
