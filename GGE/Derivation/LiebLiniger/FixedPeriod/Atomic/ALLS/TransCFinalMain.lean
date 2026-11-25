import Mathlib
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK5
import LiebLiniger.FixedPeriod.Atomic.ALLS.TransCPrepK2Full

/-! # Trunk C FINAL: C-MAIN `allS_birkhoff_conjugacy` (owner-approved exact command)

Author: Claude Opus 5.5 (preparatory author P3, final assembly).  NOT self-reviewed, NOT accepted,
NOT admitted, NOT rooted.  The theorem command is copied character-for-character from
STATEMENTS_TRUNK_C.md (sha256 787e9e7720d7c2e81cdb1cc782c404513873ff307c3608311b7227bfbd09bff2,
lines 18-29; owner approval OWNER_APPROVAL_TRUNK_C_CORE_20261112.md).  C-ANALYTIC is deferred and
not stated here.  ADMISSION IS GATED ON: independent Sol proof review (K2 chain review
SOL-TRANSC-K2-20261112, K3/K4 review SOL-TRANSC-K3K4-20261112), lane-1 qualification, and the sole
integrator.

Binders / conclusions: no hypotheses.  There is `Ω : ℤ → (ℤ → ℝ) → ℝ` with (1) `Ω n I = 0` off
`ℓ¹₊`; (2) each `Ω n` product-Borel measurable; (3) each `Ω n` ε–δ `ℓ¹`-continuous on `ℓ¹₊`;
(4) `Ω n = actualOmega n` on `positiveActionCone`; (5) for every `u : PhysicalL2`, `t : ℝ`, `n : ℤ`,
`Φ_n(l2Flow t u) = exp(−(t Ω_n(k ↦ ‖Φ_k u‖²)) i) Φ_n u`, with `Φ = physicalBirkhoff`.
Proof: `prep_allS_birkhoff_conjugacy_of_K2` (K5, from K3/K4) applied to P1's `prep_K2`. -/

set_option autoImplicit false
noncomputable section

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
  NlsGge.ThirdConsultation.PDE LiebLiniger.FixedPeriod.ALLS.PdeB

namespace NlsGge.ALLS.TransC

/-- (C-MAIN) Scalar action frequencies on `ℓ¹₊` and global conjugacy of the genuine `L²` flow. -/
theorem allS_birkhoff_conjugacy :
    ∃ Ω : ℤ → (ℤ → ℝ) → ℝ,
      (∀ (n : ℤ) (I : ℤ → ℝ), ¬ ((∀ k, 0 ≤ I k) ∧ Summable I) → Ω n I = 0) ∧
      (∀ n : ℤ, Measurable (Ω n)) ∧
      (∀ (n : ℤ) (I : ℤ → ℝ), ((∀ k, 0 ≤ I k) ∧ Summable I) →
        ∀ ε > 0, ∃ δ > 0, ∀ J : ℤ → ℝ, ((∀ k, 0 ≤ J k) ∧ Summable J) →
          ∑' k, |J k - I k| < δ → |Ω n J - Ω n I| < ε) ∧
      (∀ (n : ℤ) (I : ℤ → ℝ), I ∈ positiveActionCone → Ω n I = actualOmega n I) ∧
      (∀ (u : PhysicalL2) (t : ℝ) (n : ℤ),
        (physicalBirkhoff (l2Flow t u) : ℤ → ℂ) n =
          Complex.exp (-(((t * Ω n (fun k => ‖(physicalBirkhoff u : ℤ → ℂ) k‖ ^ 2)) : ℝ) : ℂ) *
            Complex.I) * (physicalBirkhoff u : ℤ → ℂ) n) := by
  exact NlsGge.ALLS.TransCPrep.prep_allS_birkhoff_conjugacy_of_K2
    (fun n => NlsGge.ALLS.TransCPrep.prep_K2 n)

end NlsGge.ALLS.TransC
