import NlsGge.GK38.MolnarMixedMoment
import NlsGge.GK38.MolnarPreparation

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace NlsGge.GK38.MolnarBounds38

open NlsGge.Pilot NlsGge.Schur NlsGge.SpectralFoundations NlsGge.GK38
open NlsGge.HierarchyRiccati.Core

/-- Molnar Lemma 15's exact cubic trace identity, with physical mass and actual gap actions. -/
theorem molnar_cubic_trace38 (y : SobolevHilbert ((1 : ℕ) : ℝ)) :
    Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 *
      actualGapActionAllE02_38 (sobolevToL2_38 1 y) n) ∧
    Integrable (fun x : ℝ => actualGapHeightE02_38 (sobolevToL2_38 1 y) x ^ 3) ∧
    chargeSobolev38 2 1 y - 2 * (‖sobolevToL2_38 1 y‖ ^ 2) ^ 2 =
      (∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ 2 *
        actualGapActionAllE02_38 (sobolevToL2_38 1 y) n) -
      (8 / (3 * Real.pi)) * ∫ x : ℝ, actualGapHeightE02_38 (sobolevToL2_38 1 y) x ^ 3 := by
  let u := sobolevToL2_38 1 y
  let p := actualQuasimomentumRealPartE02_38 u
  let v := actualGapHeightE02_38 u
  have hu : SobolevSquareSummable 1 (physicalFourier u) := by
    simpa only [Nat.cast_one] using sobolevToL2_38_sobolev 1 y
  have hself := actual_shift_square_height38 u hu
  have hmix := actual_shift_mixed_moment38 u hu
  have htf := actualTraceFormula_Hk_all38 1 le_rfl u y
    (fun n => (sobolevToL2_38_fourier 1 y n).symm)
  have hP : Integrable (fun t : ℝ => (2 * p t) ^ 2 * v t) := by
    refine ((htf.1.add (hmix.1.const_mul 8)).add (hself.2.1.const_mul 4)).congr
      (Eventually.of_forall fun t => ?_)
    dsimp [p, v]
    ring
  have hsplit : (∫ t : ℝ, (2 * p t) ^ 2 * v t) =
      (∫ t : ℝ, (2 * t) ^ 2 * v t) +
        8 * (∫ t : ℝ, t * (p t - t) * v t) +
        4 * (∫ t : ℝ, (p t - t) ^ 2 * v t) := by
    calc
      _ = ∫ t : ℝ, ((2 * t) ^ 2 * v t + 8 * (t * (p t - t) * v t)) +
          4 * ((p t - t) ^ 2 * v t) :=
        integral_congr_ae (Eventually.of_forall fun t => by ring)
      _ = _ := by
        have hb : Integrable (fun t : ℝ => (2 * t) ^ 2 * v t) := htf.1
        have hm : Integrable (fun t : ℝ => 8 * (t * (p t - t) * v t)) :=
          hmix.1.const_mul 8
        have hs : Integrable (fun t : ℝ => 4 * ((p t - t) ^ 2 * v t)) :=
          hself.2.1.const_mul 4
        have hbm : Integrable (fun t : ℝ => (2 * t) ^ 2 * v t + 8 * (t * (p t - t) * v t)) :=
          hb.add hm
        rw [integral_add hbm hs, integral_add hb hm]
        simp only [integral_const_mul]
  have hterm : ∀ n : ℤ,
      (2 / Real.pi) * (∫ t in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (2 * p t) ^ 2 * v t) = (2 * Real.pi * (n : ℝ)) ^ 2 * actualGapActionAllE02_38 u n := by
    intro n
    have hab := actualGapLower_le_upper_F04_38 u n
    have heq : (∫ t in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
        (2 * p t) ^ 2 * v t) =
        ∫ t in (actualGapLowerAllE02_38 u n)..(actualGapUpperAllE02_38 u n),
          (2 * Real.pi * (n : ℝ)) ^ 2 * v t := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hab] at ht
      have hlevel : t ∈ actualGapLevelSetE02_38 u n := by
        rw [(actualGapLevelSet_eq_Icc_E02_38 u n).2]
        exact ht
      have hp : p t = (n : ℝ) * Real.pi := hlevel
      rw [hp]
      ring
    rw [heq, intervalIntegral.integral_const_mul]
    unfold actualGapActionAllE02_38
    dsimp [v]
    ring
  have hsum := gapMoment_hasSum38 u (fun t : ℝ => (2 * p t) ^ 2 * v t) hP
    (fun t ht => by dsimp [v]; rw [ht]; ring)
  have haction : HasSum (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 * actualGapActionAllE02_38 u n)
      ((2 / Real.pi) * ∫ t : ℝ, (2 * p t) ^ 2 * v t) := by
    simpa only [hterm] using hsum
  refine ⟨haction.summable, hself.1, ?_⟩
  rw [haction.tsum_eq, hsplit, hmix.2, hself.2.2, ← htf.2]
  dsimp only [u, p, v]
  field_simp [Real.pi_ne_zero]
  ring

end NlsGge.GK38.MolnarBounds38
