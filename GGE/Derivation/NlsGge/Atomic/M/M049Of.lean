import Mathlib
import NlsGge.Atomic.M.M001
import NlsGge.Atomic.M.M049Core
import NlsGge.Atomic.M.M049Coef
import NlsGge.ThirdConsultation.M.BirkhoffInverseHost
import NlsGge.ThirdConsultation.M.Round5b
import NlsGge.ThirdConsultation.Sobolev.Round5
import NlsGge.Atomic.G6.G6013
import NlsGge.Atomic.G6.G6027

/- M049 OF PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). Proposed target
   NlsGge/Atomic/M/M049Of.lean. Needs ROOT MAIN PROBE (M001, G6013/G6027, Round5b, the h782 host
   `BirkhoffInverseHost` (RealSobolevSequence, birkhoffInverse) are main-only).
   M-049 `molnar_inverse_birkhoff`, conclusion VERBATIM (followup13 STATEMENTS/M.md §M-049 = r14 l.2447), CONDITIONAL on
   `h48` of EXACTLY the printed M-048 `molnar_inverse_actions` conclusion (r14 l.2498) — M-048 is not landed.
   Route (r16 L609-614): u = birkhoffInverse m z; the action of u at n equals |z_n|² (G6-027 inverse/embedding
   compatibility, G6-013 right inverse, X-006 `Phi_action`, `carrierCoe38_incl38`); the Molnar weight is ≤ (1+2π)^{2r}
   times the house weight ⟨n⟩^{2r} (M-002 class comparison, proved here in M049Coef), so
   A_m ≤ (1+2π)^{2m}‖z‖², A_1 ≤ (1+2π)²‖z‖_{h¹}², A_0 ≤ ‖z‖_{h⁰}²; M049Aux.inverse_bound_of then gives ONE D before z. -/

set_option autoImplicit false
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.GKDefinitionDesign NlsGge.Atomic.Common NlsGge.SpectralFoundations

namespace NlsGge.ThirdConsultation.M

theorem action_birkhoffInverse (m : ℕ) (hm : 1 ≤ m) (z : RealSobolevSequence m) (n : ℤ) :
    action (physicalOfSobolev (birkhoffInverse m z)) n = ‖carrierCoe38 (m : ℝ) z n‖ ^ 2 := by
  have h27 := ((G6027 m hm).2.2.2.2.2 z).2
  have hv : physicalOfSobolev (birkhoffInverse m z) =
      physicalInverseBirkhoff (sequenceSobolevEmbed m z) := by
    rw [← physicalSobolevEmbed_eq_M]
    exact h27
  have hR := G6013.2.2.2.2.2 (sequenceSobolevEmbed m z)
  rw [hv]
  show actualGapActionAllE02_38 _ n = _
  rw [← sourceFamily.Phi_action]
  change ‖physicalBirkhoff (physicalInverseBirkhoff (sequenceSobolevEmbed m z)) n‖ ^ 2 = _
  rw [hR]
  change ‖carrierCoe38 0 (carrierIncl38 (r := 0) (s := (m : ℝ)) (Nat.cast_nonneg m) z) n‖ ^ 2 = _
  rw [carrierCoe38_incl38]

theorem actionWeightedSum_birkhoffInverse (m : ℕ) (hm : 1 ≤ m) (z : RealSobolevSequence m) (r : ℕ) :
    actionWeightedSum r (physicalOfSobolev (birkhoffInverse m z)) =
      ∑' n : ℤ, ((1 + |2 * Real.pi * (n : ℝ)|) ^ r) ^ 2 * ‖carrierCoe38 (m : ℝ) z n‖ ^ 2 := by
  unfold actionWeightedSum molnarWeight
  refine tsum_congr fun n => ?_
  rw [action_birkhoffInverse m hm z n]

theorem molnar_inverse_birkhoff_of_actions (m : ℕ) (hm : 1 ≤ m)
    (h48 : ∃ d : ℝ, 0 < d ∧ ∀ u : SobolevR m,
      ‖u‖^2 ≤
        d^2 * (actionWeightedSum m (physicalOfSobolev u) +
          (1+actionWeightedSum 1 (physicalOfSobolev u))^(4*m-3) *
            actionWeightedSum 0 (physicalOfSobolev u))) :
    ∃ D : ℝ, 0 < D ∧ ∀ z : RealSobolevSequence m,
      ‖birkhoffInverse m z‖ ≤
        D * (‖z‖ +
          (1 + ‖NlsGge.Birkhoff.carrierIncl38
            (r := 1) (s := (m : ℝ)) (by exact_mod_cast hm) z‖) ^ (4 * m - 3) *
            ‖NlsGge.Birkhoff.carrierIncl38
              (r := 0) (s := (m : ℝ)) (by positivity) z‖) := by
  have hwn : ∀ r : ℕ, ∀ n : ℤ, 0 ≤ ((1 + |2 * Real.pi * (n : ℝ)|) ^ r) ^ 2 := fun r n => sq_nonneg _
  have hnn : ∀ r : ℕ, ∀ z : RealSobolevSequence m,
      0 ≤ actionWeightedSum r (physicalOfSobolev (birkhoffInverse m z)) := fun r z => by
    rw [actionWeightedSum_birkhoffInverse m hm z r]
    exact tsum_nonneg fun n => mul_nonneg (hwn r n) (sq_nonneg _)
  refine M049Aux.inverse_bound_of (4 * m - 3) (birkhoffInverse m)
    (fun r u => actionWeightedSum r (physicalOfSobolev u)) m
    (fun z => ‖z‖)
    (fun z => ‖NlsGge.Birkhoff.carrierIncl38 (r := 1) (s := (m : ℝ)) (by exact_mod_cast hm) z‖)
    (fun z => ‖NlsGge.Birkhoff.carrierIncl38 (r := 0) (s := (m : ℝ)) (by positivity) z‖)
    (fun z => norm_nonneg _) (fun z => norm_nonneg _) (fun z => norm_nonneg _)
    ((1 + 2 * Real.pi) ^ (2 * m)) ((1 + 2 * Real.pi) ^ 2) (by positivity)
    (one_le_pow₀ (by linarith [Real.pi_pos])) h48 ?_ ?_ ?_ (fun z => hnn 1 z) (fun z => hnn 0 z)
  · intro z
    show actionWeightedSum m (physicalOfSobolev (birkhoffInverse m z)) ≤ _
    rw [actionWeightedSum_birkhoffInverse m hm z m]
    exact (M049Aux.weighted_le_norm (m : ℝ) z _ _ (hwn m) (M049Aux.molnar_weight_le_nat m)).2
  · intro z
    show actionWeightedSum 1 (physicalOfSobolev (birkhoffInverse m z)) ≤ _
    rw [actionWeightedSum_birkhoffInverse m hm z 1]
    exact (M049Aux.weighted_le_incl (r := 1) (s := (m : ℝ)) (by exact_mod_cast hm) z _ _ (hwn 1)
      M049Aux.molnar_weight_le_one).2
  · intro z
    show actionWeightedSum 0 (physicalOfSobolev (birkhoffInverse m z)) ≤ _
    rw [actionWeightedSum_birkhoffInverse m hm z 0]
    have h := (M049Aux.weighted_le_incl (r := 0) (s := (m : ℝ)) (by positivity) z _ _ (hwn 0)
      M049Aux.molnar_weight_le_zero).2
    rwa [one_mul] at h

end NlsGge.ThirdConsultation.M
