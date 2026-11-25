import Mathlib
import NlsGge.ThirdConsultation.KSPS.Round5
import NlsGge.Atomic.LIB.LIB008

/- KSPS-011 SUPPORT4 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS011Support4.lean.
   Step M2 (i): the H^N -> H^1 inclusion (N >= 1) commutes with the physical embeddings, hence every
   generic-N physical pair is the PotPair of an H^1 pair: exists phi' : SobolevC 1, toPair phi' = toPotPair phi.
   Uses the landed LIB008.physicalSobolevSequenceInclusion (identity on Fourier coefficients) and
   Fourier injectivity on PhysicalL2. No hypotheses beyond 1 <= N. -/
set_option autoImplicit false
noncomputable section
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.KSPS011Support4

theorem embed_inclusion {N : ℕ} (hN : 1 ≤ N) (u : PhysicalSobolev38 (N : ℝ)) :
    NlsGge.GKDefinitionDesign.physicalSobolevEmbed 1
        (NlsGge.Atomic.LIB008.physicalSobolevSequenceInclusion (N : ℝ) ((1 : ℕ) : ℝ)
          (by exact_mod_cast hN) u) =
      NlsGge.GKDefinitionDesign.physicalSobolevEmbed N u := by
  apply fourierSeq38_injective
  funext n
  rw [NlsGge.GKDefinitionDesign.physicalSobolevEmbed_fourier,
    NlsGge.GKDefinitionDesign.physicalSobolevEmbed_fourier,
    NlsGge.Atomic.LIB008.physicalSobolevSequenceInclusion_fourier,
    NlsGge.Atomic.LIB008.sobolevSequenceInclusion_apply]

theorem exists_toPair_eq {N : ℕ} (hN : 1 ≤ N) (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) :
    ∃ φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1,
      NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ := by
  refine ⟨(NlsGge.Atomic.LIB008.physicalSobolevSequenceInclusion (N : ℝ) ((1 : ℕ) : ℝ)
      (by exact_mod_cast hN) φ.1,
    NlsGge.Atomic.LIB008.physicalSobolevSequenceInclusion (N : ℝ) ((1 : ℕ) : ℝ)
      (by exact_mod_cast hN) φ.2), ?_⟩
  unfold NlsGge.ThirdConsultation.KSPSVolterra.toPair NlsGge.ThirdConsultation.KSPS.toPotPair
  simp only [embed_inclusion hN]

end NlsGge.ThirdConsultation.KSPS011Support4
