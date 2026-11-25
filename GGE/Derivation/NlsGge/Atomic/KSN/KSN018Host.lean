import Mathlib
import NlsGge.Atomic.KSN.KSN012Host

/- KSN018 HOST PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN018Host.lean.
   Hosts ONCE the two KSN-018 design names not yet in NlsGge (proof development KSN001Host note: "NOT hosted ... KSN-012/018/019:
   smoothingCoefficient, complexSmoothing"; rawCoefficient/pairPotential/complexDomain/IsRealPair are landed in KSN012Host).
   Bodies byte-identical to followup13 DEFINITIONS/KSN.lean.md (smoothingCoefficient, complexSmoothing).
   grep NlsGge/ (2026-11-02): neither name exists. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open scoped ENNReal
open NlsGge.Pilot NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.KSN
noncomputable section

def smoothingCoefficient (N : ℕ) (x : PairScale (N : ℝ)) (b : Bool) (n : ℤ) : ℂ :=
  scalarBirkhoff b n (pairPotential (N : ℝ) (Nat.cast_nonneg N) x) +
    rawCoefficient (N : ℝ) x b (if b then -n else n)

def complexSmoothing (N : ℕ) (x : PairScale (N : ℝ)) : PairScale ((N : ℝ) + 1) :=
  sequenceLift ((N : ℝ) + 1) (smoothingCoefficient N x)

end
end NlsGge.ThirdConsultation.KSN
