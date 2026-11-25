import NlsGge.Spectral.ImaginaryResolventReciprocalFinalInequalityPrerequisiteV2
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot.ImaginaryResolventSignedTsumBoundV5

open MeasureTheory Set
open NlsGge.Pilot.ImaginaryResolventKernelAPIProbeV2

/-- The complete signed-lattice scalar resolvent kernel, with its zero mode. -/
def signedKernel (y : ℝ) (m : ℤ) : ℝ := scalarKernel y (m : ℝ)

theorem scalarKernel_integrableOn_Ioi {y : ℝ} (hy : 0 < y) :
    IntegrableOn (scalarKernel y) (Ioi (0 : ℝ)) := by
  let b : ℝ := Real.pi / y
  have hb : 0 < b := by dsimp [b]; positivity
  have hbase : IntegrableOn (fun u : ℝ => (1 + u ^ 2)⁻¹) (Ioi (0 : ℝ)) :=
    integrable_inv_one_add_sq.mono_measure Measure.restrict_le_self
  have hbase' : IntegrableOn (fun u : ℝ => (1 + u ^ 2)⁻¹) (Ioi (b * 0)) := by
    simpa using hbase
  have hcomp : IntegrableOn (fun x : ℝ => (1 + (b * x) ^ 2)⁻¹) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => (1 + u ^ 2)⁻¹) 0 hb).2 hbase'
  have hscaled : IntegrableOn
      (fun x : ℝ => (y ^ 2)⁻¹ * (1 + (b * x) ^ 2)⁻¹) (Ioi (0 : ℝ)) := by
    simpa only [IntegrableOn, smul_eq_mul, mul_comm] using hcomp.smul_const ((y ^ 2)⁻¹)
  apply hscaled.congr_fun
  · intro x hx
    dsimp [scalarKernel, b]
    have hden : 1 + (Real.pi / y * x) ^ 2 ≠ 0 := by positivity
    field_simp [ne_of_gt hy, hden]
    <;> ring
  · exact measurableSet_Ioi

theorem signedKernel_summable {y : ℝ} (hy : 0 < y) :
    Summable (signedKernel y) := by
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ scalarKernel y t := by
    intro t ht
    exact (scalarKernel_pos hy).le
  have hnat : Summable (fun n : ℕ => scalarKernel y (n : ℝ)) :=
    (scalarKernel_antitoneOn_Ici hy).summable_of_integrableOn_Ioi_zero
      (scalarKernel_integrableOn_Ioi hy) hnonneg
  have hneg : Summable (fun n : ℕ => scalarKernel y (-(n : ℤ) : ℝ)) := by
    simpa [scalarKernel_even] using hnat
  apply (summable_int_iff_summable_nat_and_neg).2
  constructor
  · simpa [signedKernel] using hnat
  · simpa [signedKernel] using hneg

/-- Full even signed-lattice sum bound. The integer regrouping retains the
zero mode; the constant 2/y follows from y≥1. -/
theorem signedKernel_tsum_le {y : ℝ} (hy : 1 ≤ y) :
    ∑' m : ℤ, signedKernel y m ≤ 2 / y := by
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hy
  have hsum : Summable (signedKernel y) := signedKernel_summable hypos
  have htail := (scalarKernel_antitoneOn_Ici hypos).tsum_add_one_le_integral
    (scalarKernel_integrableOn_Ioi hypos)
    (fun t ht => (scalarKernel_pos hypos).le)
  rw [scalarKernel_integral_Ioi_zero hypos] at htail
  have hpnat : (∑' n : ℕ+, scalarKernel y (n : ℝ)) =
      ∑' n : ℕ, scalarKernel y ((n + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tsum_pnat_eq_tsum_succ (f := fun k : ℕ => scalarKernel y (k : ℝ)))
  have htailPos : ∑' n : ℕ+, scalarKernel y (n : ℝ) ≤ 1 / (2 * y) := by
    rw [hpnat]
    exact htail
  have heven : Function.Even (signedKernel y) := by
    intro m
    simp [signedKernel, scalarKernel_even]
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum]
  have hz : scalarKernel y 0 = 1 / y ^ 2 := by
    simp [scalarKernel]
  rw [show signedKernel y 0 = scalarKernel y 0 by simp [signedKernel], hz]
  simp only [signedKernel, two_smul]
  have hhalf : 2 * (1 / (2 * y)) = 1 / y := by
    field_simp [ne_of_gt hypos]
  have htwice : 2 * (∑' n : ℕ+, scalarKernel y (n : ℝ)) ≤ 1 / y := by
    calc
      2 * (∑' n : ℕ+, scalarKernel y (n : ℝ))
          ≤ 2 * (1 / (2 * y)) := by gcongr
      _ = 1 / y := hhalf
  calc
    1 / y ^ 2 + (∑' n : ℕ+, scalarKernel y (n : ℝ) + ∑' n : ℕ+, scalarKernel y (n : ℝ))
        = 1 / y ^ 2 + 2 * (∑' n : ℕ+, scalarKernel y (n : ℝ)) := by rw [← two_mul]
    _ ≤ 1 / y ^ 2 + 1 / y := add_le_add le_rfl htwice
    _ ≤ 2 / y :=
      NlsGge.Pilot.ImaginaryResolventReciprocalFinalInequalityPrerequisiteV2.reciprocal_final_inequality hy

end NlsGge.Pilot.ImaginaryResolventSignedTsumBoundV5
