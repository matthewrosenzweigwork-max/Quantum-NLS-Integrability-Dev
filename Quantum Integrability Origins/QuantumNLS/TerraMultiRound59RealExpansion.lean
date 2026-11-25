import QuantumNLS.TerraMultiRound59RoughParity
import QuantumNLS.TerraMultiRound59OddCollection
import QuantumNLS.TerraMultiRound57PhysicalPowers
import QuantumNLS.TerraMultiRound57FirstCoefficient

/-! The physical scalar expansion after taking real parts and collecting odd powers. -/
set_option autoImplicit false
noncomputable section
open Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound59RealExpansion
open QuantumNLS.PhysicalTensor QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.RiccatiSobolevE1 QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.RootH1RatioBounds QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound57Collection QuantumNLS.TerraMultiRound57PhysicalPowers
open QuantumNLS.TerraMultiRound57CollectedPowers QuantumNLS.TerraMultiRound57FirstCoefficient
open QuantumNLS.TerraMultiRound59RoughParity QuantumNLS.TerraMultiRound59OddCollection

theorem real_tree_sum (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (x : Ell2) (Y : ℝ) :
    (∑ n ∈ Finset.range (2 * s + 2), (Y⁻¹ ^ n) •
      treeCoefficient (L := L) (k := s - 1) κ x s n).re =
    ∑ j ∈ Finset.Icc 1 s, Y⁻¹ ^ (2 * j + 1) *
      (treeCoefficient (L := L) (k := s - 1) κ x s (2 * j + 1)).re := by
  let f : ℕ → ℝ := fun n => Y⁻¹ ^ n * (treeCoefficient (L := L) (k := s - 1) κ x s n).re
  have h0 : f 0 = 0 := by simp [f, tree_coefficients_below_three (L := L) (k := s - 1) κ x s 0 (by omega)]
  have he : ∀ m : ℕ, 2 * m + 2 ≤ 2 * s + 1 → f (2 * m + 2) = 0 := by
    intro m hm
    simp [f, (rough_tree_coefficient_parity L s hs κ hκ x).1 m hm]
  have hz : f 1 = 0 := by simp [f, tree_coefficients_below_three (L := L) (k := s - 1) κ x s 1 (by omega)]
  have h := sum_odd s f h0 he
  have hset : Finset.Ico 1 (s + 1) = Finset.Icc 1 s := by ext j; simp
  have hsplit := Finset.sum_range_add_sum_Ico (fun j => f (2 * j + 1)) (show 1 ≤ s + 1 by omega)
  simp only [Finset.sum_range_one, show 2 * 0 + 1 = 1 by omega, hz, zero_add, hset] at hsplit
  simp only [Complex.re_sum, Complex.smul_re, smul_eq_mul] 
  change (∑ n ∈ Finset.range (2 * s + 2), f n) = ∑ j ∈ Finset.Icc 1 s, f (2 * j + 1)
  rw [h, ← hsplit]

theorem physical_ratio_real_expansion (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ : ℝ) (hκ : 0 < κ) (u : L2T L)
    (hu : hsq L (s - 1 : ℕ) (fun k => QuantumNLS.Fourier.coeff L u k) ≠ ⊤) :
    ∃ (x : Ell2) (ha0 : 0 ≤ ((s - 1 : ℕ) : ℝ)) (r : ℝ → Ell2),
      fieldMap L (s - 1 : ℕ) ha0 x = u ∧
      (∀ᶠ Y : ℝ in atTop, ∃ (hY : 0 < Y) (hlog : Real.log 3 ≤ Y * L)
        (hsmall : 16 * κ * ‖u‖ ^ 2 ≤ Y),
        fieldMap L (s - 1 : ℕ) ha0 (r Y) = ratioL2 hY hlog hκ.le u hsmall) ∧
      (fun Y : ℝ => (scalar L (s - 1 : ℕ) x (r Y) - freeScalar (L := L) (s - 1 : ℕ) x Y).re -
        ∑ j ∈ Finset.Icc 1 s, Y⁻¹ ^ (2 * j + 1) *
          (treeCoefficient (L := L) (k := s - 1) κ x s (2 * j + 1)).re)
        =o[atTop] (fun Y : ℝ => Y⁻¹ ^ (2 * s + 1)) := by
  obtain ⟨x, ha0, r, hx, hr, he⟩ := physical_ratio_power_expansion L s hs κ hκ u hu
  refine ⟨x, ha0, r, hx, hr, ?_⟩
  have hb : (fun Y : ℝ => (scalar L (s - 1 : ℕ) x (r Y) -
      (freeScalar (L := L) (s - 1 : ℕ) x Y + ∑ n ∈ Finset.range (2 * s + 2), (Y⁻¹ ^ n) •
        treeCoefficient (L := L) (k := s - 1) κ x s n)).re)
      =O[atTop] (fun Y : ℝ => scalar L (s - 1 : ℕ) x (r Y) -
      (freeScalar (L := L) (s - 1 : ℕ) x Y + ∑ n ∈ Finset.range (2 * s + 2), (Y⁻¹ ^ n) •
        treeCoefficient (L := L) (k := s - 1) κ x s n)) := by
    apply isBigO_of_le
    intro Y
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm _
  have h := hb.trans_isLittleO he
  apply h.congr'
  · exact Filter.Eventually.of_forall (fun Y => by dsimp only; rw [Complex.sub_re, Complex.add_re, real_tree_sum L s hs κ hκ x Y, Complex.sub_re]; ring)
  · exact Filter.Eventually.of_forall (fun _ => rfl)

#print axioms real_tree_sum
#print axioms physical_ratio_real_expansion
end QuantumNLS.TerraMultiRound59RealExpansion
