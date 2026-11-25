import Mathlib
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.Atomic.KSN.KSN006Host

/- KSN007 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN007Host.lean.
   Hosts the design objects `collapsedIntegral`, `constantIntegrand`, `constantPart`
   (design DEFINITIONS/KSN.lean.md, byte-identical in followup1..10; bodies verbatim, no lexical edit).
   `collapsedDD`, `nearSegment`, `nearRoot`, `dividedIntegrand`, `dividedPart` are in KSN006Host (imported, not redeclared);
   `normalizedZeta` is in G4NormalizedHost. grep NlsGge, Armstrong, Work/isolated_20261027 (2026-11-01): these three names
   are declared nowhere else. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.KSN
noncomputable section
open NlsGge.GKDefinitionDesign

def collapsedIntegral (n : ℤ) (φ : PotPair) : ℂ :=
  (muSeq φ n - tauN φ n) * ∫ t : ℝ in (0 : ℝ)..1,
    collapsedDD n φ (tauN φ n + (t : ℂ) * (muSeq φ n - tauN φ n))

def constantIntegrand (n : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  (normalizedZeta n φ (tauN φ n) - 1) *
    (muSeq φ n - lamMinus φ n) / nearRoot n φ t

def constantPart (n : ℤ) (φ : PotPair) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1, constantIntegrand n φ t

end
end NlsGge.ThirdConsultation.KSN
