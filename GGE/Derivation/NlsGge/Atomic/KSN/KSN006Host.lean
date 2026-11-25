import Mathlib
import NlsGge.GK38.TauGammaDefs
import NlsGge.GK38.DirichletLabels
import NlsGge.GK38.PeriodicLabellingCanonical
import NlsGge.Atomic.G4.G4NormalizedHost
import NlsGge.Atomic.KSN.KSN002

/- KSN006 HOST01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/KSN/KSN006Host.lean.
   Hosts the design objects `collapsedDD`, `nearSegment`, `nearRoot`, `dividedIntegrand`, `dividedPart`
   (design DEFINITIONS/KSN.lean.md, byte-identical in followup1..10; bodies verbatim, no lexical edit; only the
   five definitions needed by KSN-006 are hosted here; `collapsedIntegral`, `constantIntegrand`, `constantPart` are left
   to the packets that need them (KSN-007/KSN-008), which should import this host for `collapsedDD`).
   grep NlsGge, Armstrong, Work/isolated_20261027 (2026-11-01): none of these names is declared elsewhere.
   `terminalRoot` (KSN namespace abbrev) is landed in KSN002; `normalizedZeta` in G4NormalizedHost. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.KSN
noncomputable section
open NlsGge.GKDefinitionDesign

def collapsedDD (n : ℤ) (φ : PotPair) (z : ℂ) : ℂ :=
  if z = tauN φ n then -deriv (normalizedZeta n φ) (tauN φ n)
  else (normalizedZeta n φ z - normalizedZeta n φ (tauN φ n)) / (tauN φ n - z)

def nearSegment (n : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  lamMinus φ n + (t : ℂ) * (muSeq φ n - lamMinus φ n)

/-- On the nearer-minus-endpoint segment the principal square root of this
ratio has no cut crossing. The terminal root fixes its overall sign. -/
def nearRoot (n : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  (Real.sqrt t : ℂ) * terminalRoot n φ *
    Complex.sqrt ((lamPlus φ n - nearSegment n φ t) / (lamPlus φ n - muSeq φ n))

def dividedIntegrand (n : ℤ) (φ : PotPair) (t : ℝ) : ℂ :=
  (muSeq φ n - lamMinus φ n) * collapsedDD n φ (nearSegment n φ t) *
    (tauN φ n - nearSegment n φ t) / nearRoot n φ t

def dividedPart (n : ℤ) (φ : PotPair) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..1, dividedIntegrand n φ t

end
end NlsGge.ThirdConsultation.KSN
