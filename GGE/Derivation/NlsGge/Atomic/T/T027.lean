import Mathlib
import NlsGge.ThirdConsultation.T.T027Host
import NlsGge.Birkhoff.W12Tilt38f
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing

/- T-027 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted; needs ROOT MAIN PROBE). Proposed target
   NlsGge/Atomic/T/T027.lean. Head `lowerEnergy_finite_continuous` VERBATIM from followup13 STATEMENTS/T.md §T-027
   (l.353–359), namespace NlsGge.ThirdConsultation.T with the DEFINITIONS/T.lean.md common opens.
   Imports declare both notation right-hand sides (PDE.BirkhoffRealization, PDE.OneSmoothing; B1 lesson), the host
   T027Host (lowerEnergy; via T026Host physicalInclusion) and the producer module W12Tilt38f.
   Proof (printed route, landed W12Tilt38f): EB_finite_continuous_W12_38 at the actual pair B =
   PDE.actualBirkhoffInput38, O = PDE.actualOneSmoothingInput38 and `hs' : s < 3/4`. That producer proves finiteness
   in ENNReal first (EB_identity_physOfE38: EB38 = ofReal(β-series) + remainder, both finite) and only then the
   continuity of the real `.toReal`, on FinvE38 c s with the topology induced by toE38. Here it is transported to
   ECarrier38 c s along x ↦ ⟨physOfE38 c s x, _⟩, whose composite with toE38 is the identity (eExt38,
   fourierSeq38_physOfE38), hence continuous into the induced topology. No hypothesis added; `hs` (1/2 < s) is part
   of the printed head and is not needed by the proof. Prerequisites KEEP-E03/KEEP-E03-CONT/KEEP-GAP-LOWER are
   inherited KEEP ids, realized by the landed W12Tilt38f/W05 producers imported here. -/
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.T
local notation "B" => PDE.actualBirkhoffInput38
local notation "O" => PDE.actualOneSmoothingInput38

theorem t027_physOfE38_mem {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s) :
    fourierSeq38 (physOfE38 c s x) ∈ seqE38 c s := by
  rw [fourierSeq38_physOfE38]
  exact eCoe38_mem c s x

theorem t027_toE38_incl {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) (x : ECarrier38 c s) :
    toE38 c s (⟨physOfE38 c s x, t027_physOfE38_mem c s x⟩ : FinvE38 c s) = x := by
  apply eExt38 c s
  exact (eCoe38_toE38 c s _).trans (fourierSeq38_physOfE38 c s x)

theorem t027_incl_continuous {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) :
    @Continuous (ECarrier38 c s) (FinvE38 c s) _ (topFinvE38 c s)
      (fun x => (⟨physOfE38 c s x, t027_physOfE38_mem c s x⟩ : FinvE38 c s)) := by
  letI : TopologicalSpace (FinvE38 c s) := topFinvE38 c s
  refine continuous_induced_rng.2 ?_
  have hid : (toE38 c s ∘ fun x => (⟨physOfE38 c s x, t027_physOfE38_mem c s x⟩ : FinvE38 c s)) = id :=
    funext (t027_toE38_incl c s)
  rw [hid]
  exact continuous_id

theorem t027_lowerEnergy_eq_comp {lo up : ℝ} (c : BoundedCoefficients lo up) (s : ℝ) :
    lowerEnergy c s = (fun u : FinvE38 c s => (EB38 c.val u.1).toReal) ∘
      (fun x => (⟨physOfE38 c s x, t027_physOfE38_mem c s x⟩ : FinvE38 c s)) := rfl

theorem lowerEnergy_finite_continuous
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (∀ x : ECarrier38 c s, EB38 c.val (physicalInclusion c s x) ≠ ⊤) ∧
    Continuous (lowerEnergy c s) := by
  obtain ⟨hfin, hcont⟩ := (B).EB_finite_continuous_W12_38 O c hs'
  refine ⟨fun x => hfin ⟨physOfE38 c s x, t027_physOfE38_mem c s x⟩, ?_⟩
  rw [t027_lowerEnergy_eq_comp c s]
  exact @Continuous.comp _ _ _ _ (topFinvE38 c s) _ _ _ hcont (t027_incl_continuous c s)

end NlsGge.ThirdConsultation.T
