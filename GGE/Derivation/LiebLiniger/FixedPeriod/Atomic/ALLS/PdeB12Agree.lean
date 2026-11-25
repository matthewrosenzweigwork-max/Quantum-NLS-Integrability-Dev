import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB11Group

/-! # Track B: agreement with the higher-regularity flows (approved contracts 20–23)

Statements copied verbatim from the owner-approved `TRACK_B_EXACT_STATEMENTS_FOR_APPROVAL.txt`
(sha256 943a37c24a40c74b1e025c9f243c49372b9e071c313bebf28cda3ace2f3ca056).
* contract 20 `l2Flow_eq_nlsFlowL2`: for `H¹` data the trajectory of `nlsFlowL2` has Fourier
  coefficients `nlsFlowSeq t (û₀)`, an `h¹` solution (`flow_isNLSSolM38`); approved contract 25
  identifies it with `l2Flow`;
* contracts 21–23: rewrite with contract 20 and use the existing `nlsFlowL2` facts
  `physicalFourier_nlsFlowL2`, `physH38_nlsFlowL2`, `nlsFlowL2_mem`.
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory NlsGge.Pilot NlsGge.NLS38 NlsGge.Birkhoff NlsGge.Sobolev38
open scoped ContDiff
set_option autoImplicit false
noncomputable section

/-! ### Approved contract 20 -/

theorem l2Flow_eq_nlsFlowL2 (u₀ : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u₀)) (t : ℝ) :
    l2Flow t u₀ = nlsFlowL2 t u₀ := by
  have hsol : IsNLSSolM 1 (fun r => physicalFourier (nlsFlowL2 r u₀)) := by
    have e : (fun r => physicalFourier (nlsFlowL2 r u₀)) =
        fun r => nlsFlowSeq r (physicalFourier u₀) := by
      funext r
      exact physicalFourier_nlsFlowL2 hu r
    rw [e]
    exact flow_isNLSSolM38 1 le_rfl (physicalFourier_mem_one38 hu)
  have h := l2Flow_of_isNLSSolM 1 le_rfl (fun r => nlsFlowL2 r u₀) hsol t
  rw [nlsFlowL2_zero] at h
  exact h.symm

/-! ### Approved contract 21 -/

theorem physicalFourier_l2Flow (u₀ : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u₀)) (t : ℝ) :
    physicalFourier (l2Flow t u₀) = nlsFlowSeq t (physicalFourier u₀) := by
  rw [l2Flow_eq_nlsFlowL2 u₀ hu t]
  exact physicalFourier_nlsFlowL2 hu t

/-! ### Approved contract 22 -/

theorem physH38_l2Flow (m : ℕ) (hm : 1 ≤ m) (u₀ : PhysicalL2)
    (hu : fourierSeq38 u₀ ∈ seqSobolev38 (m : ℝ)) (t : ℝ) :
    physH38 m (l2Flow t u₀) = nlsFlowC m hm t (physH38 m u₀) := by
  have hu1 : SobolevSquareSummable 1 (physicalFourier u₀) := by
    have := seqSobolev38_mono (by exact_mod_cast hm : (1 : ℝ) ≤ m) hu
    simpa using (fourierSeq38_mem_iff 1 u₀).1 this
  rw [l2Flow_eq_nlsFlowL2 u₀ hu1 t]
  exact physH38_nlsFlowL2 m hm hu t

/-! ### Approved contract 23 -/

theorem l2Flow_mem_sobolev (m : ℕ) (hm : 1 ≤ m) (u₀ : PhysicalL2)
    (hu : SobolevSquareSummable (m : ℝ) (physicalFourier u₀)) (t : ℝ) :
    SobolevSquareSummable (m : ℝ) (physicalFourier (l2Flow t u₀)) := by
  have hu1 : SobolevSquareSummable 1 (physicalFourier u₀) := by
    have := (mem_seqSobolev38_iff ((m : ℕ) : ℝ) _).2 hu
    have h1 := seqSobolev38_mono (by exact_mod_cast hm : (1 : ℝ) ≤ m) this
    exact (mem_seqSobolev38_iff _ _).1 h1
  rw [l2Flow_eq_nlsFlowL2 u₀ hu1 t]
  exact nlsFlowL2_mem m hm hu t

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
