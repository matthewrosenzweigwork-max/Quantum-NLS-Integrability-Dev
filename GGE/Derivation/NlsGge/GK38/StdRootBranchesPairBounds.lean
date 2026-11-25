import NlsGge.GK38.StdRootBranchesPairTail
import NlsGge.GK38.StdRootBranchesPairHead

/-! One majorant absorbs every finite pair and every far correction. -/
set_option autoImplicit false
open Set Metric Filter Topology
namespace NlsGge.GK38
noncomputable section

def rootPairS38 (D G R : ℝ) (M : ℕ) : ℝ := rootGapPairC38 G +
  ((((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1)^2 + 1) * (M : ℝ)^2

def rootPairRadius38 (R S : ℝ) : ℝ := Real.sqrt (R^2 + Real.pi^2 * S / 2)

theorem rootPairS_nonneg38 {D G R : ℝ} (hG : 0 ≤ G) (M : ℕ) :
    0 ≤ rootPairS38 D G R M := by
  unfold rootPairS38
  exact add_nonneg (rootGapPairC_nonneg38 hG) (by positivity)

theorem root_pairMaj_absorb38 (Q : ℤ → ℝ) (R : ℝ) {S : ℝ} (hS : 0 ≤ S) (m : ℕ) :
    Lib.pairMaj Q (rootPairRadius38 R S) m =
      Lib.pairMaj Q R m + S / ((m : ℝ) + 1)^2 := by
  have hs : (rootPairRadius38 R S)^2 = R^2 + Real.pi^2 * S / 2 :=
    Real.sq_sqrt (by positivity)
  unfold Lib.pairMaj Lib.majC2
  rw [hs]
  field_simp
  ring

theorem root_pair_common_bound38 (p : PotPair × ℂ) (hp : p ∈ rootDomain38)
    {D G R : ℝ} (hD : 0 ≤ D) (hG : 0 ≤ G) (hR : 0 ≤ R) (M : ℕ)
    (hsep : 2 * (D + R) ≤ (M : ℝ) * Real.pi)
    (hδ : ∀ n : ℤ, ‖tauN p.1 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (hg : ∀ n : ℤ, ‖gamma2 p.1 n‖ ≤ G) (hz : ‖p.2‖ ≤ R) (m : ℕ) :
    ‖Lib.pairDev (fun n => rootFactor38 n p) m‖ ≤
      Lib.pairMaj (rootTauQ38 p) (rootPairRadius38 R (rootPairS38 D G R M)) m := by
  rw [root_pairMaj_absorb38 _ _ (rootPairS_nonneg38 hG M)]
  have hmaj : 0 ≤ Lib.pairMaj (rootTauQ38 p) R m := by
    unfold Lib.pairMaj
    exact add_nonneg (mul_nonneg Lib.majC1_nonneg
      (add_nonneg (rootTauQ_nonneg38 _ _) (rootTauQ_nonneg38 _ _)))
      (mul_nonneg (Lib.majC2_nonneg R) (by positivity))
  by_cases hM : m + 1 ≤ M
  · have hb := root_pair_head_bound38 p hp hD hG hR M hδ hg hz m hM
    have hs : ((((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1)^2 + 1) * (M : ℝ)^2 ≤
        rootPairS38 D G R M := by
      dsimp [rootPairS38]
      linarith [rootGapPairC_nonneg38 hG]
    exact hb.trans ((div_le_div_of_nonneg_right hs (by positivity)).trans (le_add_of_nonneg_left hmaj))
  · have ht : (M : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : M ≤ m + 1)
    have hb := root_pair_tail_bound38 p hG hδ hg hz m
      (hsep.trans (mul_le_mul_of_nonneg_right ht Real.pi_pos.le))
    have hs : rootGapPairC38 G ≤ rootPairS38 D G R M := by
      dsimp [rootPairS38]
      have hH : 0 ≤ ((((M : ℝ) * Real.pi + D + R)^2 + G / 4 + 1)^2 + 1) * (M : ℝ)^2 := by positivity
      linarith
    exact hb.trans (add_le_add le_rfl (div_le_div_of_nonneg_right hs (by positivity)))

end
end NlsGge.GK38
