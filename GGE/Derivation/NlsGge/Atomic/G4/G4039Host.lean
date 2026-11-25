import Mathlib
import NlsGge.GK38.Defs
import NlsGge.ThirdConsultation.G5033Host

/- G4039 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G4/G4039Host.lean.
   Hosts the three design names `CartesianComplex`, `cartesianSequence`, `birkhoffCartesian`. Bodies byte-identical
   to Pro round 8 (PRO_DEFINITION_RESPONSE_FP80_07_08.md section 29, G4-039) and DEFINITIONS/G4.lean.md lines 142-148
   (unchanged in rounds 9-12). Round 10 ruling: they use the landed public `cartesianX` / `cartesianY`
   (NlsGge/ThirdConsultation/G5033Host.lean). Names checked absent from NlsGge/ (grep 2026-11-01); no lexical edits. -/
set_option autoImplicit false

open Classical Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38
open scoped ENNReal BigOperators

namespace NlsGge.GKDefinitionDesign
noncomputable section

abbrev CartesianComplex := lp (fun _ : Bool × ℤ => ℂ) 2

def cartesianSequence (φ : PotPair) (j : Bool × ℤ) : ℂ :=
  if j.1 then cartesianX j.2 φ else cartesianY j.2 φ

def birkhoffCartesian (φ : PotPair) : CartesianComplex :=
  if h : Memℓp (cartesianSequence φ) 2 then
    ⟨cartesianSequence φ, h⟩
  else 0

end
end NlsGge.GKDefinitionDesign
