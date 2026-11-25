import NlsGge.Schur.FreeResolventPotentialColumnEnergy
import NlsGge.Analysis.PhysicalReflectedSeries

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

/-- The independent reflected potential has the same actual disk-uniform
nonresonant column energy, with its source Fourier coefficient retained. -/
theorem freeResolventReflectedPotentialColumnEnergy_bound (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (n : ℤ) (hn : n ≠ 0)
    (z : ℂ) (hz : z ∈ spectralDisk n) :
    (∑' m : {m : Sector n // m ≠ resonantIndex n},
      ‖freeResolventCoeff n z m.val‖ ^ 2 *
        ‖physicalFourier u (-(m.val.val + n) / 2)‖ ^ 2) ≤
      (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u hu‖ ^ 2 := by
  let e := freeResolventColumnModeEquiv n
  have hsourceSummable := physicalH1_reflected_column_summable u hu n hn
  have hsourceBound := physicalH1_reflected_column_tsum_bound u hu n hn
  have hpoint (p : {p : ℤ // p ≠ n}) :
      ‖freeResolventCoeff n z (e.symm p).val‖ ^ 2 *
          ‖physicalFourier u (-(((e.symm p).val.val + n) / 2))‖ ^ 2 ≤
        ‖physicalFourier u (-p.val)‖ ^ 2 * inverseSquare (n - p.val) := by
    have hmval : (e.symm p).val.val = 2 * p.val - n := by rfl
    have hfreq : ((e.symm p).val.val + n) / 2 = p.val := by
      rw [hmval]
      omega
    have hcoeff := freeResolventCoeff_bound n z hz (e.symm p).val
      (e.symm p).property
    have hden :
        |((e.symm p).val.val : ℝ) - (n : ℝ)| =
          2 * |(p.val : ℝ) - (n : ℝ)| := by
      calc
        |((e.symm p).val.val : ℝ) - (n : ℝ)| =
            |2 * ((p.val : ℝ) - (n : ℝ))| := by rw [hmval]; congr 1 <;> push_cast <;> ring
        _ = 2 * |(p.val : ℝ) - (n : ℝ)| := by rw [abs_mul]; norm_num
    have hpabs : 0 < |(p.val : ℝ) - (n : ℝ)| := by
      apply abs_pos.mpr
      have hpint : p.val - n ≠ 0 := sub_ne_zero.mpr p.property
      exact_mod_cast hpint
    have hdenle : |(p.val : ℝ) - (n : ℝ)| ≤
        |((e.symm p).val.val : ℝ) - (n : ℝ)| := by
      rw [hden]
      nlinarith
    have hcoeff' : ‖freeResolventCoeff n z (e.symm p).val‖ ≤
        1 / |(p.val : ℝ) - (n : ℝ)| :=
      hcoeff.trans (one_div_le_one_div_of_le hpabs hdenle)
    have hcoeffsq : ‖freeResolventCoeff n z (e.symm p).val‖ ^ 2 ≤
        inverseSquare (n - p.val) := by
      have hsq : ‖freeResolventCoeff n z (e.symm p).val‖ ^ 2 ≤
          (1 / |(p.val : ℝ) - (n : ℝ)|) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hcoeff'
      have habs : |(p.val : ℝ) - (n : ℝ)| ^ 2 =
          ((n - p.val : ℤ) : ℝ) ^ 2 := by
        rw [sq_abs]
        norm_cast
        ring
      calc
        _ ≤ (1 / |(p.val : ℝ) - (n : ℝ)|) ^ 2 := hsq
        _ = inverseSquare (n - p.val) := by
          simp [inverseSquare, div_pow, habs]
    rw [hfreq]
    calc
      _ ≤ inverseSquare (n - p.val) * ‖physicalFourier u (-p.val)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeffsq (sq_nonneg _)
      _ = _ := by ring
  have hactualSummable : Summable (fun p : {p : ℤ // p ≠ n} =>
      ‖freeResolventCoeff n z (e.symm p).val‖ ^ 2 *
        ‖physicalFourier u (-(((e.symm p).val.val + n) / 2))‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      hpoint hsourceSummable
  have hnegdiv (m : {m : Sector n // m ≠ resonantIndex n}) :
      -(m.val.val + n) / 2 = -((m.val.val + n) / 2) := by
    have hm := m.val.property
    have hd : 2 ∣ m.val.val + n := by omega
    exact Int.neg_ediv_of_dvd hd
  calc
    (∑' m : {m : Sector n // m ≠ resonantIndex n},
        ‖freeResolventCoeff n z m.val‖ ^ 2 *
          ‖physicalFourier u (-(m.val.val + n) / 2)‖ ^ 2) =
      ∑' p : {p : ℤ // p ≠ n},
        ‖freeResolventCoeff n z (e.symm p).val‖ ^ 2 *
          ‖physicalFourier u (-(((e.symm p).val.val + n) / 2))‖ ^ 2 := by
        symm
        calc
          _ = ∑' p : {p : ℤ // p ≠ n},
              ‖freeResolventCoeff n z (e.symm p).val‖ ^ 2 *
                ‖physicalFourier u (-( (e.symm p).val.val + n) / 2)‖ ^ 2 := by
            apply tsum_congr
            intro p
            rw [← hnegdiv (e.symm p)]
          _ = _ := e.symm.tsum_eq (fun m =>
            ‖freeResolventCoeff n z m.val‖ ^ 2 *
              ‖physicalFourier u (-(m.val.val + n) / 2)‖ ^ 2)
    _ ≤ ∑' p : {p : ℤ // p ≠ n},
        ‖physicalFourier u (-p.val)‖ ^ 2 * inverseSquare (n - p.val) :=
      hactualSummable.tsum_le_tsum hpoint hsourceSummable
    _ ≤ (2 / (n : ℝ) ^ 2) * ‖physicalSobolevL2 1 u hu‖ ^ 2 := hsourceBound

end NlsGge.Schur
