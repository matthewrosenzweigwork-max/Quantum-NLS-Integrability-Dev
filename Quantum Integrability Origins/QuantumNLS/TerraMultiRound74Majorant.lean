import QuantumNLS.TerraMultiRound74UpperBounds

/-! The integrable positive majorant for the upper fractional correction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace QuantumNLS.TerraMultiRound74Majorant
open QuantumNLS.TranslatedCorrelation QuantumNLS.Reg014Moments
open QuantumNLS.TerraMultiRound74UpperBounds

variable {L : ℝ} [Fact (0 < L)]

def upperMajorant (s Y : ℝ) : ℝ :=
  if Y ≤ 1 then Y ^ (2 * s - 3) else Y ^ (2 * s - 5)

theorem upperMajorant_integrable (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    IntegrableOn (upperMajorant s) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · have h : IntegrableOn (fun Y : ℝ => Y ^ (2 * s - 3)) (Ioc 0 1) := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo, intervalIntegral.integrableOn_Ioo_rpow_iff (show (0 : ℝ) < 1 by norm_num)]
      linarith
    apply h.congr_fun
    · intro Y hY
      simp [upperMajorant, hY.2]
    · exact measurableSet_Ioc
  · have h : IntegrableOn (fun Y : ℝ => Y ^ (2 * s - 5)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
    apply h.congr_fun
    · intro Y hY
      simp [upperMajorant, not_le_of_gt (mem_Ioi.mp hY)]
    · exact measurableSet_Ioi

/-- The REG-014 bound and the small-Y bound provide the common integrable
majorant needed for dominated convergence, with no extra field hypothesis. -/
theorem upper_correction_majorant (κ : ℝ) (hκ : 0 < κ) (B : Set (Hk L 1))
    (hB : Bornology.IsBounded B) (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    ∃ C : ℝ, 0 ≤ C ∧ IntegrableOn (fun Y => C * upperMajorant s Y) (Ioi 0) ∧
      ∀ u ∈ B, ∀ Y > 0, |Y ^ (2 * s - 5) * Dfun κ hκ 2 u.val Y| ≤ C * upperMajorant s Y := by
  obtain ⟨C, hC, hb⟩ := correction_bounds κ hκ B hB
  refine ⟨C, hC, (upperMajorant_integrable s hs1 hs2).const_mul C, ?_⟩
  intro u hu Y hY
  have hp : 0 ≤ Y ^ (2 * s - 5) := Real.rpow_nonneg hY.le _
  rw [abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ Y ^ (2 * s - 5) * (C * (if Y ≤ 1 then Y ^ 2 else 1)) :=
      mul_le_mul_of_nonneg_left (hb u hu Y hY) hp
    _ = C * upperMajorant s Y := by
      by_cases hy : Y ≤ 1
      · simp only [if_pos hy, upperMajorant]
        rw [mul_left_comm, ← Real.rpow_two Y, ← Real.rpow_add hY]
        congr 1
        congr 1
        <;> ring
      · simp [upperMajorant, hy, mul_comm]

#print axioms upperMajorant_integrable
#print axioms upper_correction_majorant
end QuantumNLS.TerraMultiRound74Majorant
