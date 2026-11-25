import NlsGge.GK38.StdRootBranchesPairFar

/-! Finite-index bounds use the symmetric polynomial and retain every pair. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem root_piN_norm_ge_one38 (n : ℤ) (hn : n ≠ 0) : 1 ≤ ‖(Lib.piN n : ℂ)‖ := by
  rw [root_piN_norm38 n hn]
  have hi : (1 : ℤ) ≤ |n| := by have := abs_pos.mpr hn; omega
  have hr : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hi
  nlinarith [Real.pi_gt_three]

theorem rootFactor_head_bound38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38)
    {D G R : ℝ} (_hD : 0 ≤ D) (hG : 0 ≤ G) (_hR : 0 ≤ R) (M : ℕ)
    (hδ : ∀ n : ℤ, ‖tauN p.1 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (hg : ∀ n : ℤ, ‖gamma2 p.1 n‖ ≤ G) (hz : ‖p.2‖ ≤ R)
    (n : ℤ) (hn : n ≠ 0) (hM : |n| ≤ (M : ℤ)) :
    ‖rootFactor38 n p‖ ≤ ((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1 := by
  have hw : ‖tauN p.1 n - p.2‖ ≤ (M : ℝ) * Real.pi + D + R := by
    have hc := countingCenter_low_norm38 hM
    have he : tauN p.1 n - p.2 =
      (tauN p.1 n - countingCenter38 n) + countingCenter38 n - p.2 := by ring
    rw [he]
    calc
      _ ≤ ‖(tauN p.1 n - countingCenter38 n) + countingCenter38 n‖ + ‖p.2‖ := norm_sub_le _ _
      _ ≤ ‖tauN p.1 n - countingCenter38 n‖ + ‖countingCenter38 n‖ + ‖p.2‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (M : ℝ) * Real.pi + D + R := by
        dsimp [countingCenter38] at hc ⊢
        linarith [hδ n]
  have hm : tauN p.1 n - p.2 ≠ 0 := by
    rw [tauN_value38 p.1 hp.1 n, add_comm (lamPlus p.1 n)]
    exact stdRoot_midpoint_ne38 (rootDomain_avoids38 hp n)
  have hs := stdRoot_norm_le38 (g := gamma2 p.1 n) hm
  have hs' : ‖stdRoot38 (tauN p.1 n) (gamma2 p.1 n) p.2‖ ≤
      ((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1 := by
    have hw2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    linarith [hg n]
  rw [rootFactor38, norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (root_piN_norm_ge_one38 n hn))).mpr
  have hP : 0 ≤ ((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1 := by positivity
  exact hs'.trans (le_mul_of_one_le_right hP (root_piN_norm_ge_one38 n hn))

theorem root_pair_head_bound38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38)
    {D G R : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hR : 0 ≤ R) (M : ℕ)
    (hδ : ∀ n : ℤ, ‖tauN p.1 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (hg : ∀ n : ℤ, ‖gamma2 p.1 n‖ ≤ G) (hz : ‖p.2‖ ≤ R)
    (m : ℕ) (hM : m + 1 ≤ M) :
    ‖Lib.pairDev (fun n => rootFactor38 n p) m‖ ≤
      ((((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1)^2 + 1) *
        (M : ℝ)^2 / ((m : ℝ) + 1)^2 := by
  let A : ℝ := ((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hpos := rootFactor_head_bound38 p hp hD hG hR M hδ hg hz ((m : ℤ) + 1)
    (by omega) (by rw [abs_of_nonneg (by omega)]; exact_mod_cast hM)
  have hneg := rootFactor_head_bound38 p hp hD hG hR M hδ hg hz (-((m : ℤ) + 1))
    (by omega) (by rw [abs_neg, abs_of_nonneg (by omega)]; exact_mod_cast hM)
  change ‖rootFactor38 ((m : ℤ) + 1) p‖ ≤ A at hpos
  change ‖rootFactor38 (-((m : ℤ) + 1)) p‖ ≤ A at hneg
  have hb : ‖Lib.pairDev (fun n => rootFactor38 n p) m‖ ≤ A^2 + 1 := by
    unfold Lib.pairDev
    calc
      _ ≤ ‖rootFactor38 ((m : ℤ) + 1) p * rootFactor38 (-((m : ℤ) + 1)) p‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ A^2 + 1 := by
        rw [norm_mul, norm_one, pow_two]
        exact add_le_add (mul_le_mul hpos hneg (norm_nonneg _) hA) le_rfl
  apply hb.trans
  apply (le_div_iff₀ (by positivity : 0 < ((m : ℝ) + 1)^2)).mpr
  have ht : (m : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hs : ((m : ℝ) + 1)^2 ≤ (M : ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  exact mul_le_mul_of_nonneg_left hs (by positivity)

end
end NlsGge.GK38
