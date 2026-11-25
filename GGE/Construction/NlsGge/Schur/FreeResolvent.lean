import NlsGge.Schur.OwnModeSequence
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The concrete complementary free diagonal in the complex spectral disk

The resonant coefficient is zero. Nonresonant denominators are proved nonzero
from the signed parity gap before inverses are used. This constructs a bounded
operator on the genuine coordinate Hilbert space; identification of the free
weighted domain with the physical H¹ Dirac trace domain remains separate.
-/

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Schur

def spectralCenter (n : ℤ) : ℂ := (n : ℂ) * (Real.pi : ℂ)

def spectralDisk (n : ℤ) : Set ℂ := {z | ‖z - spectralCenter n‖ ≤ 1}

/-- The genuine parity gap covers all signed indices, including zero. -/
theorem sector_gap_two (n : ℤ) (m : Sector n) (hm : m ≠ resonantIndex n) :
    2 ≤ |(m.val : ℝ) - (n : ℝ)| := by
  have hp := m.property
  have hne : m.val ≠ n := by
    intro h
    apply hm
    exact Subtype.ext h
  rcases le_total n m.val with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
    exact_mod_cast (show 2 ≤ m.val - n by omega)
  · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    exact_mod_cast (show 2 ≤ -(m.val - n) by omega)

theorem spectralCenter_distance (n m : ℤ) :
    ‖spectralCenter n - spectralCenter m‖ =
      Real.pi * |(m : ℝ) - (n : ℝ)| := by
  have he : spectralCenter n - spectralCenter m =
      ((n : ℂ) - (m : ℂ)) * (Real.pi : ℂ) := by
    unfold spectralCenter
    ring
  have hd : ‖(n : ℂ) - (m : ℂ)‖ = |(m : ℝ) - (n : ℝ)| := by
    rw [← Int.cast_sub, Complex.norm_intCast, Int.cast_sub, abs_sub_comm]
  rw [he, norm_mul, hd, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_comm]

theorem spectral_denominator_triangle (n : ℤ) (z : ℂ)
    (hzDisk : z ∈ spectralDisk n) (m : Sector n) :
    Real.pi * |(m.val : ℝ) - (n : ℝ)| - 1 ≤ ‖z - spectralCenter m.val‖ := by
  have ht := norm_sub_le (z - spectralCenter m.val) (z - spectralCenter n)
  have he : (z - spectralCenter m.val) - (z - spectralCenter n) =
      spectralCenter n - spectralCenter m.val := by ring
  rw [he, spectralCenter_distance] at ht
  change ‖z - spectralCenter n‖ ≤ 1 at hzDisk
  linarith

theorem spectral_denominator_gap (n : ℤ) (z : ℂ)
    (hzDisk : z ∈ spectralDisk n) (m : Sector n) (hm : m ≠ resonantIndex n) :
    |(m.val : ℝ) - (n : ℝ)| ≤ ‖z - spectralCenter m.val‖ := by
  have hg := sector_gap_two n m hm
  have ht := spectral_denominator_triangle n z hzDisk m
  have hp := Real.pi_gt_three
  nlinarith

theorem spectral_denominator_ne_zero (n : ℤ) (z : ℂ)
    (hzDisk : z ∈ spectralDisk n) (m : Sector n) (hm : m ≠ resonantIndex n) :
    z - spectralCenter m.val ≠ 0 := by
  have hg := sector_gap_two n m hm
  have hd := spectral_denominator_gap n z hzDisk m hm
  intro hz
  rw [hz, norm_zero] at hd
  linarith

/-- Zero on the resonant coordinate, actual reciprocal only off resonance. -/
def freeResolventCoeff (n : ℤ) (z : ℂ) (m : Sector n) : ℂ :=
  if m = resonantIndex n then 0 else (z - spectralCenter m.val)⁻¹

@[simp] theorem freeResolventCoeff_resonant (n : ℤ) (z : ℂ) :
    freeResolventCoeff n z (resonantIndex n) = 0 := by
  simp [freeResolventCoeff]

theorem freeResolventCoeff_bound (n : ℤ) (z : ℂ)
    (hzDisk : z ∈ spectralDisk n) (m : Sector n) (hm : m ≠ resonantIndex n) :
    ‖freeResolventCoeff n z m‖ ≤ 1 / |(m.val : ℝ) - (n : ℝ)| := by
  have hg := sector_gap_two n m hm
  have hd := spectral_denominator_gap n z hzDisk m hm
  have hz := spectral_denominator_ne_zero n z hzDisk m hm
  rw [freeResolventCoeff, if_neg hm, norm_inv, ← one_div]
  exact one_div_le_one_div_of_le (by linarith) hd

theorem freeResolventCoeff_norm_le_one (n : ℤ) (z : ℂ)
    (hzDisk : z ∈ spectralDisk n) (m : Sector n) :
    ‖freeResolventCoeff n z m‖ ≤ 1 := by
  by_cases hm : m = resonantIndex n
  · subst m
    simp
  · have hb := freeResolventCoeff_bound n z hzDisk m hm
    have hg := sector_gap_two n m hm
    have hi : 1 / |(m.val : ℝ) - (n : ℝ)| ≤ 1 / (1 : ℝ) :=
      one_div_le_one_div_of_le zero_lt_one (by linarith)
    exact hb.trans (by simpa using hi)

/-- Both reflected components have free eigenvalue mπ and the same diagonal. -/
def freeResolventSquare (n : ℤ) (z : ℂ) (hzDisk : z ∈ spectralDisk n) :
    SectorSquare n →L[ℂ] SectorSquare n :=
  lp.mapCLM 2
    (fun i : Bool × Sector n => freeResolventCoeff n z i.2 • ContinuousLinearMap.id ℂ ℂ)
    zero_le_one
    (by
      intro i
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using
        freeResolventCoeff_norm_le_one n z hzDisk i.2)

@[simp] theorem freeResolventSquare_apply (n : ℤ) (z : ℂ)
    (hzDisk : z ∈ spectralDisk n) (x : SectorSquare n) (i : Bool × Sector n) :
    freeResolventSquare n z hzDisk x i = freeResolventCoeff n z i.2 * x i := rfl

theorem freeResolventSquare_norm_le_one (n : ℤ) (z : ℂ)
    (hzDisk : z ∈ spectralDisk n) : ‖freeResolventSquare n z hzDisk‖ ≤ 1 := by
  exact lp.norm_mapCLM_le 2 _ zero_le_one _

theorem freeResolventSquare_resonant_right (n : ℤ) (z : ℂ)
    (hzDisk : z ∈ spectralDisk n) :
    (freeResolventSquare n z hzDisk).comp (resonantSquare n) = 0 := by
  ext x ⟨b,m⟩
  change freeResolventCoeff n z m *
    (if m = resonantIndex n then x (b,m) else 0) = 0
  by_cases hm : m = resonantIndex n <;> simp [freeResolventCoeff, hm]

theorem freeResolventSquare_resonant_left (n : ℤ) (z : ℂ)
    (hzDisk : z ∈ spectralDisk n) :
    (resonantSquare n).comp (freeResolventSquare n z hzDisk) = 0 := by
  ext x ⟨b,m⟩
  change (if m = resonantIndex n then freeResolventCoeff n z m * x (b,m) else 0) = 0
  by_cases hm : m = resonantIndex n <;> simp [freeResolventCoeff, hm]

end NlsGge.Schur
