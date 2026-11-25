import QuantumNLS.TerraMultiRound58SelectedSmooth
import QuantumNLS.TerraMultiRound58FreeSmooth
import QuantumNLS.TerraMultiRound57CollectedPowers

/-! Comparison of finite tree coefficients with the smooth recursive coefficients. -/
set_option autoImplicit false
noncomputable section
open Complex Finset Filter Topology Asymptotics
namespace QuantumNLS.TerraMultiRound58Compare
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.RiccatiExpansions QuantumNLS.ClassicalCharges
open QuantumNLS.TerraMultiRound39PhysicalBall QuantumNLS.TerraMultiRound40ScalarParity
open QuantumNLS.TerraMultiRound41Coefficients QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound57CollectedPowers QuantumNLS.TerraMultiRound57CoefficientUniqueness
open QuantumNLS.TerraMultiRound58LittleO QuantumNLS.TerraMultiRound58SelectedSmooth
open QuantumNLS.TerraMultiRound58FreeSmooth

def recursiveDifference (L κ : ℝ) (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else coefficient L κ f n - coefficient L 0 f n

lemma recursive_difference_sum (L κ : ℝ) (f : ℝ → ℂ) (N : ℕ) (Y : ℝ) :
    (∑ n ∈ Finset.Icc 1 N, coefficient L κ f n * ((Y : ℂ)⁻¹) ^ n) -
      (∑ n ∈ Finset.Icc 1 N, coefficient L 0 f n * ((Y : ℂ)⁻¹) ^ n) =
    ∑ n ∈ Finset.range (N + 1), (Y⁻¹ ^ n) • recursiveDifference L κ f n := by
  have hset : Finset.Ico 1 (N + 1) = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hsplit := Finset.sum_range_add_sum_Ico
    (fun n => (Y⁻¹ ^ n) • recursiveDifference L κ f n) (show 1 ≤ N + 1 by omega)
  have hz : recursiveDifference L κ f 0 = 0 := by simp [recursiveDifference]
  simp only [Finset.sum_range_one, hz, smul_zero, zero_add, hset] at hsplit
  rw [← hsplit, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
  simp only [recursiveDifference, if_neg hn0, smul_sub, Complex.real_smul, Complex.ofReal_pow,
    Complex.ofReal_inv]
  ring

/-- Each finite tree coefficient equals the difference between the interacting
and zero-coupling smooth recursive scalar coefficients. -/
theorem tree_coefficient_eq_smooth (L : ℝ) [hLf : Fact (0 < L)]
    (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (x : Ell2) (f : ℝ → ℂ)
    (hrep : physRep L (s - 1 : ℕ) x = f) (hf : SmoothPeriodic L f)
    (r : ℝ → Ell2)
    (huniq : ∀ᶠ Y : ℝ in atTop, ∀ (hY : 0 < |Y|) (t : Ell2),
      ‖t‖ ≤ 2 * ‖x‖ / |Y| → physicalT hLf.out (a := ((s - 1 : ℕ) : ℝ)) (by
        have h : (1 : ℝ) ≤ (s - 1 : ℕ) := by exact_mod_cast (show 1 ≤ s - 1 by omega)
        linarith) hY κ x t = t → t = r Y) :
    ∀ n ≤ 2 * s + 1, treeCoefficient (L := L) (k := s - 1) κ x s n =
      recursiveDifference L κ f n := by
  have ha : (1 : ℝ) / 2 < ((s - 1 : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ (s - 1 : ℕ) := by exact_mod_cast (show 1 ≤ s - 1 by omega)
    linarith
  let N := 2 * s + 1
  have hN : 1 ≤ N := by dsimp [N]; omega
  have ht := scalar_tree_expansion (L := L) s hs κ x r huniq
  have ht' : (fun Y : ℝ => (scalar L (s - 1 : ℕ) x (r Y) - freeScalar (L := L) (s - 1 : ℕ) x Y) -
      ∑ n ∈ Finset.range (N + 1), (Y⁻¹ ^ n) • treeCoefficient (L := L) (k := s - 1) κ x s n)
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ N) := by
    convert ht using 1
    funext Y
    rw [← collect_tree_powers (L := L) (k := s - 1) s hs κ x Y]
    ring
  have hi := selected_smooth_scalar_littleO L (s - 1 : ℕ) ha κ x f hrep hf r huniq N hN
  obtain ⟨B, C, hB, hb⟩ := free_scalar_smooth_expansion L (s - 1 : ℕ) ha x f hrep hf N hN
  have hfree : (fun Y : ℝ => freeScalar (L := L) (s - 1 : ℕ) x Y -
      ∑ n ∈ Finset.Icc 1 N, coefficient L 0 f n * ((Y : ℂ)⁻¹) ^ n)
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ N) := by
    apply inverse_power_bound_littleO N _ C
    filter_upwards [eventually_ge_atTop B] with Y hY
    exact hb Y hY
  have hd : (fun Y : ℝ => (scalar L (s - 1 : ℕ) x (r Y) - freeScalar (L := L) (s - 1 : ℕ) x Y) -
      ∑ n ∈ Finset.range (N + 1), (Y⁻¹ ^ n) • recursiveDifference L κ f n)
      =o[atTop] (fun Y : ℝ => Y⁻¹ ^ N) := by
    have hh := hi.sub hfree
    convert hh using 1
    funext Y
    rw [← recursive_difference_sum]
    ring
  exact inverse_power_coefficients_unique N _ _ _ ht' hd

#print axioms recursive_difference_sum
#print axioms tree_coefficient_eq_smooth
end QuantumNLS.TerraMultiRound58Compare
