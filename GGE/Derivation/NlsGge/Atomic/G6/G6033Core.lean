import Mathlib
import NlsGge.Atomic.G6.G6033Host
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.Atomic.G6.G6015

/- G6033 CORE PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Target NlsGge/Atomic/G6/G6033Core.lean,
   namespace NlsGge.ThirdConsultation.G6033S.  SUPPORT (no packet increment).
   G6033_of = the G6-033 head body (followup13 STATEMENTS/G6.md, verbatim) from hypotheses with EXACT producer types:
   h31 = G6031.1, hinvA = (G6027 1 le_rfl).2.1, hemb = inverseBirkhoffSobolev_embed 1 (landed SobolevBirkhoffCompat),
   hleft / hright = G6013 conjuncts 5 / 6, h21 = (G6021 u).2, h32 = the G6-032 head (packet prerequisite).
   Route (Pro r15 Q5 row G6-033: "Real analyticity is supplied by the actual inverse and energy; constancy is a
   pointwise equality of action fibres"):  analyticity = composition nlsHamiltonian ∘ inverseBirkhoffSobolev 1;
   constancy: for a = inverseBirkhoffSobolev 1 z, b = ... w, Φ(embed a) = seqEmbed z and Φ(embed b) = seqEmbed w have
   equal moduli, so Φ(embed b) lies on the action torus of embed a (G6-021 MapsTo at embed a), G6-021 SurjOn and
   Φ-injectivity put embed b in the isospectral set of embed a, and G6-032 gives equal Hamiltonians.
   LEXICAL/ELABORATION REPAIR (same as landed G6-034, round-14 cluster 12): `carrierCoe38 1 z` ->
   `carrierCoe38 ((1 : ℕ) : ℝ) z` (and w); the printed form does not elaborate against z : SobolevCarrier38 ((1 : ℕ) : ℝ)
   (worker-lane request b99703e3).  No mathematical change. -/
set_option autoImplicit false

open Set Filter Topology MeasureTheory
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Atomic.Common
open scoped ENNReal InnerProductSpace
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.G6033S
noncomputable section

theorem iso_of_moduli
    (hleft : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (hright : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (h21 : ∀ u : PhysicalL2,
      Set.BijOn physicalBirkhoff (isospectralSet u) (physicalActionTorus (actionSequence u)))
    (a b : Lib.L2Z) (hab : ∀ n : ℤ, ‖a n‖ ^ 2 = ‖b n‖ ^ 2) :
    physicalInverseBirkhoff b ∈ isospectralSet (physicalInverseBirkhoff a) := by
  set ua := physicalInverseBirkhoff a
  have hua : ua ∈ isospectralSet ua := fun z => rfl
  have htor : physicalBirkhoff ua ∈ physicalActionTorus (actionSequence ua) := (h21 ua).mapsTo hua
  have hΦa : physicalBirkhoff ua = a := hright a
  have hb : b ∈ physicalActionTorus (actionSequence ua) := by
    intro n
    have := htor n
    rw [hΦa] at this
    rw [← hab n, this]
  obtain ⟨x, hx, hxb⟩ := (h21 ua).surjOn hb
  have : x = physicalInverseBirkhoff b := by rw [← hxb, hleft x]
  rw [← this]
  exact hx

theorem G6033_of
    (h31 : AnalyticOnNhd ℝ nlsHamiltonian Set.univ)
    (hinvA : AnalyticOnNhd ℝ (inverseBirkhoffSobolev 1) Set.univ)
    (hemb : ∀ z : SobolevCarrier38 ((1 : ℕ) : ℝ),
      physicalSobolevEmbed 1 (inverseBirkhoffSobolev 1 z) =
        physicalInverseBirkhoff (sequenceSobolevEmbed 1 z))
    (hleft : Function.LeftInverse physicalInverseBirkhoff physicalBirkhoff)
    (hright : Function.RightInverse physicalInverseBirkhoff physicalBirkhoff)
    (h21 : ∀ u : PhysicalL2,
      Set.BijOn physicalBirkhoff (isospectralSet u) (physicalActionTorus (actionSequence u)))
    (h32 : ∀ u v : PhysicalSobolev38 ((1 : ℕ) : ℝ),
      physicalSobolevEmbed 1 v ∈ isospectralSet (physicalSobolevEmbed 1 u) →
        nlsHamiltonian u = nlsHamiltonian v) :
  AnalyticOnNhd ℝ transformedNLSHamiltonian Set.univ ∧
  ∀ z w : SobolevCarrier38 ((1 : ℕ) : ℝ),
    (∀ n : ℤ, ‖carrierCoe38 ((1 : ℕ) : ℝ) z n‖^2 = ‖carrierCoe38 ((1 : ℕ) : ℝ) w n‖^2) →
    transformedNLSHamiltonian z = transformedNLSHamiltonian w := by
  refine ⟨fun z _ => ?_, fun z w hzw => ?_⟩
  · exact (h31 _ (Set.mem_univ _)).comp (hinvA z (Set.mem_univ _))
  · unfold transformedNLSHamiltonian
    apply h32
    rw [hemb, hemb]
    apply iso_of_moduli hleft hright h21
    intro n
    have ez := congrFun (sequenceSobolevEmbed_coe 1 z) n
    have ew := congrFun (sequenceSobolevEmbed_coe 1 w) n
    rw [ez, ew]
    exact hzw n

end
end NlsGge.ThirdConsultation.G6033S
