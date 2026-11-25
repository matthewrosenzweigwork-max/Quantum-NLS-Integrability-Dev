import NlsGge.ThirdConsultation.PDE.OneSmoothing

/-! # E04.04: boundedness of the actual one-smoothing maps

The bounds are transported from `KSN019_main` and `KSN021_main`; pointwise
analyticity is not used to infer boundedness on an infinite-dimensional ball.
-/

set_option autoImplicit false
noncomputable section

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.Atomic.Common NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSN NlsGge.ThirdConsultation.G6024S
open NlsGge.ThirdConsultation.PDE NlsGge.ThirdConsultation.Common

namespace LiebLiniger.FixedPeriod.EXT

/-- E04.04 for the same actual Birkhoff map and inverse used in
`actualOneSmoothingInput38`. For every natural Sobolev level `r` and proof `hr`
that `1 ≤ r`, each of the two conclusions says: for every real radius `R ≥ 0`
there is a real constant `C ≥ 0`, chosen before the input, such that every
`x : h^r` with `‖x‖ ≤ R` has smoothing difference of `h^(r+1)` norm at most `C`.
The first conclusion concerns `T - Id`, the second `Tinv - Id`; their constants
may differ. The carrier norms are the genuine real Sobolev Hilbert norms.
There are no free map, smoothing, boundedness, or analyticity assumptions. -/
theorem actual_one_smoothing_bounded_on_balls (r : ℕ) (hr : 1 ≤ r) :
    (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : SobolevCarrier38 (r : ℝ), ‖x‖ ≤ R →
        ‖carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
          (fun y => actualBirkhoffInput38.T y - y)
          (actualOneSmoothingInput38.smooth_T r hr) x‖ ≤ C) ∧
    (∀ R : ℝ, 0 ≤ R → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : SobolevCarrier38 (r : ℝ), ‖x‖ ≤ R →
        ‖carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
          (fun y => actualBirkhoffInput38.Tinv y - y)
          (actualOneSmoothingInput38.smooth_Tinv r hr) x‖ ≤ C) := by
  constructor
  · intro R hR
    obtain ⟨C, hC, hbound⟩ := (KSN019_main r hr).2.2.2
      (‖toPair r‖ * R) (mul_nonneg (norm_nonneg _) hR)
    refine ⟨‖fromPairEq (r + 1)‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
    intro x hx
    have heq : carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun y => actualBirkhoffInput38.T y - y)
        (actualOneSmoothingInput38.smooth_T r hr) x =
        fromPairEq (r + 1) (complexSmoothing r (toPair r x)) := by
      apply carrierExt38
      funext n
      change actualT38 (carrierCoe38 (r : ℝ) x) n - carrierCoe38 (r : ℝ) x n = _
      have hmk : carrierMk38 (r : ℝ) (carrierCoe38 (r : ℝ) x)
          (carrierCoe38_mem (r : ℝ) x) = x := carrierExt38 rfl
      have hc := smooth_coord r hr (carrierCoe38 (r : ℝ) x)
        (carrierCoe38_mem (r : ℝ) x) n
      rwa [hmk] at hc
    rw [heq]
    have hpair : ‖toPair r x‖ ≤ ‖toPair r‖ * R :=
      ((toPair r).le_opNorm x).trans
        (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
    have hcs := hbound (toPair r x)
      (NlsGge.ThirdConsultation.KSN022S.toPair_isReal r x) hpair
    exact ((fromPairEq (r + 1)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left hcs (norm_nonneg _))
  · intro R hR
    obtain ⟨C, hC, hbound⟩ := (KSN021_main r hr).2.2 R hR
    refine ⟨C, hC, ?_⟩
    intro x hx
    have hcast : (r : ℝ) + 1 = ((r + 1 : ℕ) : ℝ) := by
      push_cast
      rfl
    have heq : carrierMap38 (r : ℝ) ((r + 1 : ℕ) : ℝ)
        (fun y => actualBirkhoffInput38.Tinv y - y)
        (actualOneSmoothingInput38.smooth_Tinv r hr) x =
        carrierMk38 ((r + 1 : ℕ) : ℝ)
          (carrierCoe38 ((r : ℝ) + 1)
            (physicalSobolevFourierEquiv38 ((r : ℝ) + 1) (inverseSmoothing r x)))
          (CarrierCastAux.carrier_cast_mem hcast _) := by
      apply carrierExt38
      rw [carrierMap38_coe, carrierCoe38_mk,
        coe_equiv_real ((r : ℝ) + 1) (by positivity), ((KSN021_main r hr).2.1 x).2]
      have hmk : carrierMk38 (r : ℝ) (carrierCoe38 (r : ℝ) x)
          (carrierCoe38_mem (r : ℝ) x) = x := carrierExt38 rfl
      change actualBirkhoffTop38.Tinv (carrierCoe38 (r : ℝ) x) -
        carrierCoe38 (r : ℝ) x = _
      rw [tinv_sub_eq r _ (carrierCoe38_mem _ x), hmk]
    have hnorm : ∀ (a b : ℝ) (hab : a = b) (y : SobolevCarrier38 a),
        ‖carrierMk38 b (carrierCoe38 a y) (CarrierCastAux.carrier_cast_mem hab y)‖ =
          ‖y‖ := by
      intro a b hab y
      subst b
      rfl
    rw [heq, hnorm _ _ hcast, LinearIsometryEquiv.norm_map]
    exact hbound x hx

end LiebLiniger.FixedPeriod.EXT
