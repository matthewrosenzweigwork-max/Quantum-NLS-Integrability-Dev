import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK0
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK6

/-! # Trunk C final commands C-ACTION and C-PERSIST (verbatim approved texts)

Author: Claude Opus 5.5 (preparatory author P2, trunk C).  Not self-reviewed, not accepted.
Statements copied verbatim from STATEMENTS_TRUNK_C.md
(sha256 787e9e7720d7c2e81cdb1cc782c404513873ff307c3608311b7227bfbd09bff2), owner approval recorded in
campaign/llfp/rehabilitation/pro-20261031/all-s-planning-20261110/OWNER_APPROVAL_TRUNK_C_CORE_20261112.md.
Opens and namespace as listed there: opens NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
NlsGge.Atomic.Common NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.PDE
LiebLiniger.FixedPeriod.ALLS.PdeB; namespace NlsGge.ALLS.TransC.
C-MAIN (`allS_birkhoff_conjugacy`) and C-ANALYTIC are NOT in this file.

ADMISSION GATE: this file is NOT admitted.  Admission is gated on the independent Sol proof reviews
of TransCPrepK0 (SOL-TRANSC-K0-20261112) and TransCPrepK6 (SOL-TRANSC-K6-20261112), on lane-1
qualification, and on admission by the sole integrator.

Binders and conclusions (one line each):
* `allS_action_invariant (u) (t) (n)`: for every `u ∈ L²(ℝ/ℤ)`, every real `t` and every mode `n`,
  `‖Φ_n(l2Flow t u)‖ = ‖Φ_n(u)‖` with `Φ = physicalBirkhoff`.  Proof: `prep_action_invariant` (K0).
* `allS_flow_persistence (s) (hs : 0 ≤ s)`: there is a proved witness `hS` (for every `t` and every
  `x ∈ h⁰ ∩ h^s`, `𝓕(l2Flow t (𝓕⁻¹x)) ∈ h^s`) such that `(t, x) ↦ 𝓕(l2Flow t (𝓕⁻¹x))` is jointly
  continuous `ℝ × h^s → h^s`.  Proof: `prep_flow_persistence` (K6).
-/

set_option autoImplicit false
noncomputable section

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.PDE LiebLiniger.FixedPeriod.ALLS.PdeB

namespace NlsGge.ALLS.TransC

/-- (C-PERSIST) Persistence and joint continuity of the genuine flow on every `h^s`, read in
reflected Fourier coordinates. -/
theorem allS_flow_persistence (s : ℝ) (hs : 0 ≤ s) :
    ∃ hS : (∀ (t : ℝ) (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 0), x ∈ seqSobolev38 s →
        fourierSeq38 (l2Flow t (physInv38 x hx)) ∈ seqSobolev38 s),
      Continuous fun p : ℝ × SobolevCarrier38 s =>
        carrierMk38 s (fourierSeq38 (l2Flow p.1 (physInv38 (carrierCoe38 s p.2)
          (seqSobolev38_mono hs (carrierCoe38_mem s p.2)))))
          (hS p.1 _ _ (carrierCoe38_mem s p.2)) := by
  exact NlsGge.ALLS.TransCPrep.prep_flow_persistence s hs

/-- (C-ACTION) Action invariance of the genuine flow, every datum and time. -/
theorem allS_action_invariant (u : PhysicalL2) (t : ℝ) (n : ℤ) :
    ‖(physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n‖ = ‖(physicalBirkhoff u : ℤ → ℂ) n‖ := by
  exact NlsGge.ALLS.TransCPrep.prep_action_invariant u t n

end NlsGge.ALLS.TransC
