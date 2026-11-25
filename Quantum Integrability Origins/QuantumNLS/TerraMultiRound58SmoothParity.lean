import QuantumNLS.TerraMultiRound58Compare
import QuantumNLS.TerraMultiRound41CoefficientParity

/-! Smooth coefficient comparison without a branch hypothesis and relative parity. -/
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
namespace QuantumNLS.TerraMultiRound58SmoothParity
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwiseDisc
open QuantumNLS.ClassicalCharges QuantumNLS.TerraMultiRound39PhysicalBall
open QuantumNLS.TerraMultiRound41Coefficients QuantumNLS.TerraMultiRound41CoefficientParity
open QuantumNLS.TerraMultiRound57CollectedPowers QuantumNLS.TerraMultiRound58Compare

/-- The smooth identification holds without assuming a branch: existence and
uniqueness of a small branch supply it for every real coupling. -/
theorem tree_coefficient_smooth (L : ℝ) [hLf : Fact (0 < L)]
    (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (x : Ell2) (f : ℝ → ℂ)
    (hrep : physRep L (s - 1 : ℕ) x = f) (hf : SmoothPeriodic L f) :
    ∀ n ≤ 2 * s + 1, treeCoefficient (L := L) (k := s - 1) κ x s n =
      recursiveDifference L κ f n := by
  classical
  have ha : (1 : ℝ) / 2 < ((s - 1 : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ (s - 1 : ℕ) := by exact_mod_cast (show 1 ≤ s - 1 by omega)
    linarith
  obtain ⟨B, hB, hb⟩ := physical_fixed_eventually hLf.out ha κ x
  have hex : ∀ Y : ℝ, ∃ r : Ell2, B ≤ Y →
      ∀ (hY : 0 < |Y|) (t : Ell2), ‖t‖ ≤ 2 * ‖x‖ / |Y| →
        physicalT hLf.out ha hY κ x t = t → t = r := by
    intro Y
    by_cases hy : B ≤ Y
    · obtain ⟨hY, r, _, _, hu⟩ := hb Y (hy.trans (le_abs_self Y))
      exact ⟨r, fun _ _ t ht hf => hu t ht hf⟩
    · exact ⟨0, fun h => False.elim (hy h)⟩
  choose r hr using hex
  have huniq : ∀ᶠ Y : ℝ in atTop, ∀ (hY : 0 < |Y|) (t : Ell2),
      ‖t‖ ≤ 2 * ‖x‖ / |Y| → physicalT hLf.out ha hY κ x t = t → t = r Y := by
    filter_upwards [eventually_ge_atTop B] with Y hY
    exact hr Y hY
  exact tree_coefficient_eq_smooth L s hs κ x f hrep hf r huniq

/-- For two positive couplings, the difference of their even tree coefficients
has vanishing real part, and the difference at odd indices has vanishing imaginary part. -/
theorem relative_tree_coefficient_parity (L : ℝ) [Fact (0 < L)] (s : ℕ) (hs : 2 ≤ s)
    (κ η : ℝ) (hκ : 0 < κ) (hη : 0 < η) (x : Ell2) (f : ℝ → ℂ)
    (hrep : physRep L (s - 1 : ℕ) x = f) (hf : SmoothPeriodic L f) :
    (∀ m : ℕ, 2 * m + 2 ≤ 2 * s + 1 →
      (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 2) -
       treeCoefficient (L := L) (k := s - 1) η x s (2 * m + 2)).re = 0) ∧
    (∀ m : ℕ, 2 * m + 1 ≤ 2 * s + 1 →
      (treeCoefficient (L := L) (k := s - 1) κ x s (2 * m + 1) -
       treeCoefficient (L := L) (k := s - 1) η x s (2 * m + 1)).im = 0) := by
  have hk := tree_coefficient_smooth L s hs κ x f hrep hf
  have hl := tree_coefficient_smooth L s hs η x f hrep hf
  have pk := coefficient_parity hκ hf
  have pl := coefficient_parity hη hf
  constructor
  · intro m hm
    rw [hk _ hm, hl _ hm]
    simp only [recursiveDifference, show 2 * m + 2 ≠ 0 by omega, if_false, Complex.sub_re,
      pk.2 m, pl.2 m]
    ring
  · intro m hm
    rw [hk _ hm, hl _ hm]
    simp only [recursiveDifference, show 2 * m + 1 ≠ 0 by omega, if_false, Complex.sub_im,
      pk.1 m, pl.1 m]
    ring

#print axioms tree_coefficient_smooth
#print axioms relative_tree_coefficient_parity
end QuantumNLS.TerraMultiRound58SmoothParity
