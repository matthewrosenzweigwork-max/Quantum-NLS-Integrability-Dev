import Mathlib
import NlsGge.Atomic.M.M042SeedCore
import NlsGge.Atomic.M.M001
import NlsGge.ThirdConsultation.M.H1SourceSeed
import NlsGge.ThirdConsultation.M.Round5b
import NlsGge.ThirdConsultation.G6.SobolevBirkhoffCompatCore
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.Schur.ActualSchurBallMap38V1

/- M042 SEED PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M042Seed.lean. Needs ROOT MAIN PROBE (M001, H1SourceSeed, Round5b absent from mirror).
   * sobolevR_one_fourierSummable: u ∈ SobolevR 1 has H¹-summable physical Fourier coefficients (pattern of
     M018Tails.hH1).
   * inverse_H1_source_action_seed: Pro r16 support head VERBATIM (PRO_DEFINITION_RESPONSE_FP80_16.md L479-481).
     Proof: `MH1Seed.H1Norm_sq_eq` (Q² = 2 Σ srcW·rcoef) + the lane-checked `M042Seed.seed_core`.
   * house_H1_norm_sq_le_source: ‖u‖² ≤ (MTwoMode.H1Norm u)², the house/source H1 comparison (r14 l.7311, r16 L429),
     with constant 1 (in fact ‖u‖² ≤ Q²/2): house weight 1+n² (sobolevModeWeight 1) ≤ (1+|2πn|)².
   * inverse_H1_action_seed: the M-042 printed head (followup13 STATEMENTS/M.md L1242-1245) VERBATIM, as a corollary
     with its 1/3 constant unchanged. Packet ownership of this name is root's decision (M-042 owner); it no longer
     needs M-041: the landed GK38 `molnar_inverse_base_pair38` already contains the Molnar Lemma 15 step. -/

set_option autoImplicit false
open MeasureTheory
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations NlsGge.Birkhoff NlsGge.Atomic.Common

namespace NlsGge.ThirdConsultation.M

theorem sobolevR_one_fourierSummable (u : SobolevR 1) :
    SobolevSquareSummable 1 (physicalFourier (physicalOfSobolev u)) := by
  rw [← NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M]
  simpa using (fourierSeq38_mem_iff ((1 : ℕ) : ℝ) _).1
    (NlsGge.GKDefinitionDesign.physicalSobolevEmbed_mem 1 u)

theorem inverse_H1_source_action_seed (u : SobolevR 1) :
    (1 / 3 : ℝ) * MTwoMode.H1Norm u ^ 2 ≤
      actionWeightedSum 1 (physicalOfSobolev u) +
        actionWeightedSum 0 (physicalOfSobolev u) ^ 2 := by
  rw [MH1Seed.H1Norm_sq_eq]
  exact M042Seed.seed_core (physicalOfSobolev u) (sobolevR_one_fourierSummable u)

theorem house_H1_norm_sq_le_source (u : SobolevR 1) :
    ‖u‖ ^ 2 ≤ MTwoMode.H1Norm u ^ 2 := by
  have hn : ‖u‖ ^ 2 = ∑' n : ℤ, (1 + (n : ℝ) ^ 2) * MH1Seed.rcoef (physicalOfSobolev u) n := by
    have hu : ‖u‖ = ‖physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ) u‖ :=
      ((physicalSobolevFourierEquiv38 ((1 : ℕ) : ℝ)).norm_map u).symm
    rw [hu, ← (carrier_hasSum_norm_sq38 _ _).tsum_eq]
    refine tsum_congr fun n => ?_
    have hc := NlsGge.GKDefinitionDesign.physicalSobolevEmbed_fourier 1 u n
    rw [NlsGge.GKDefinitionDesign.physicalSobolevEmbed_eq_M] at hc
    rw [← hc, Nat.cast_one, NlsGge.Schur.sobolevModeWeight_one38]
    try rfl
  rw [hn, MH1Seed.H1Norm_sq_eq]
  exact M042Seed.house_le_source_sum _ (fun p => sq_nonneg _) (MH1Seed.summable_rcoef_weights u).2.2

theorem inverse_H1_action_seed (u : SobolevR 1) :
  (1/3:ℝ) * ‖u‖^2 ≤
    actionWeightedSum 1 (physicalOfSobolev u) +
      actionWeightedSum 0 (physicalOfSobolev u)^2 := by
  have h := house_H1_norm_sq_le_source u
  have hs := inverse_H1_source_action_seed u
  linarith

end NlsGge.ThirdConsultation.M
