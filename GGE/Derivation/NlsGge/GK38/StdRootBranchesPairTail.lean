import NlsGge.GK38.StdRootBranchesPairFar
import NlsGge.GK38.StdRootBranchesLines

/-! The actual far pair is the τ-linear pair plus an inverse-square gap correction. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

def rootGapPairC38 (G : ℝ) : ℝ :=
  (9 / 4) * (2 * G / Real.pi^2 + G^2 / Real.pi^4)

theorem rootGapPairC_nonneg38 {G : ℝ} (hG : 0 ≤ G) : 0 ≤ rootGapPairC38 G := by
  unfold rootGapPairC38
  positivity

theorem root_pair_tail_bound38 (p : PotPair × ℂ) {D G R : ℝ} (hG : 0 ≤ G)
    (hδ : ∀ n : ℤ, ‖tauN p.1 n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ D)
    (hg : ∀ n : ℤ, ‖gamma2 p.1 n‖ ≤ G) (hz : ‖p.2‖ ≤ R) (m : ℕ)
    (hsep : 2 * (D + R) ≤ ((m : ℝ) + 1) * Real.pi) :
    ‖Lib.pairDev (fun n => rootFactor38 n p) m‖ ≤
      Lib.pairMaj (rootTauQ38 p) R m + rootGapPairC38 G / ((m : ℝ) + 1)^2 := by
  let t : ℝ := (m : ℝ) + 1
  let k : ℤ := (m : ℤ) + 1
  let L : ℤ → ℂ := fun n => (tauN p.1 n - p.2) / (Lib.piN n : ℂ)
  let s : ℤ → ℂ := fun n =>
    Complex.sqrt (1 - (gamma2 p.1 n / 4) / (tauN p.1 n - p.2)^2)
  have ht : 1 ≤ t := by dsimp [t]; linarith [Nat.cast_nonneg (α := ℝ) m]
  have htp : 0 < t * Real.pi := mul_pos (lt_of_lt_of_le zero_lt_one ht) Real.pi_pos
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hnorm (n : ℤ) (hn : n = k ∨ n = -k) :
      ‖(n : ℂ) * (Real.pi : ℂ)‖ = t * Real.pi := by
    change ‖countingCenter38 n‖ = t * Real.pi
    rw [norm_countingCenter38]
    have habs : |(n : ℝ)| = t := by
      rcases hn with rfl | rfl
      · dsimp [k, t]; push_cast; rw [abs_of_nonneg (by positivity)]
      · rw [Int.cast_neg, abs_neg]; dsimp [k, t]; push_cast; rw [abs_of_nonneg (by positivity)]
    rw [habs]
  have hlin (n : ℤ) (hn : n = k ∨ n = -k) :
      t * Real.pi / 2 ≤ ‖tauN p.1 n - p.2‖ ∧ ‖L n‖ ≤ 3 / 2 := by
    have hn0 : n ≠ 0 := by rcases hn with rfl | rfl <;> simpa using hk
    have h := root_pair_linear_norm38 (hδ n) hz (hnorm n hn) htp hsep
    have he : (Lib.piN n : ℂ) = (n : ℂ) * (Real.pi : ℂ) := by
      rw [Lib.piN_of_ne hn0]
      push_cast
      rfl
    simpa only [L, he] using h
  have hs (n : ℤ) (hn : n = k ∨ n = -k) :
      ‖s n - 1‖ ≤ G / (t^2 * Real.pi^2) := by
    have h := root_far_sqrt_error38 (hg n) htp (hlin n hn).1
    simpa only [s, mul_pow] using h
  have he : 0 ≤ G / (t^2 * Real.pi^2) := by positivity
  have hb := root_pair_expand_bound38 (L k) (L (-k)) (s k) (s (-k)) he
    (hs k (Or.inl rfl)) (hs (-k) (Or.inr rfl))
  have hl : ‖L k * L (-k) - 1‖ ≤ Lib.pairMaj (rootTauQ38 p) R m := by
    simpa only [Lib.pairTerm_eq_pairDev, Lib.pairDev, Lib.prodFactor, k, L] using
      (Lib.pairTerm_le_maj (σ := fun n => tauN p.1 n) (d := rootTauQ38 p) hz
        (fun n => le_rfl : ∀ n, ‖Lib.prodDev (fun n => tauN p.1 n) n‖^2 ≤ rootTauQ38 p n) m)
  have hcoeff : ‖L k‖ * ‖L (-k)‖ ≤ (9 / 4 : ℝ) := by
    nlinarith [(hlin k (Or.inl rfl)).2, (hlin (-k) (Or.inr rfl)).2,
      norm_nonneg (L k), norm_nonneg (L (-k))]
  have hdec := root_pair_correction_decay38 hG ht
  change ‖rootFactor38 k p * rootFactor38 (-k) p - 1‖ ≤ _
  rw [rootFactor_split38, rootFactor_split38]
  calc
    _ ≤ ‖L k * L (-k) - 1‖ + ‖L k‖ * ‖L (-k)‖ *
        (2 * (G / (t^2 * Real.pi^2)) + (G / (t^2 * Real.pi^2))^2) := hb
    _ ≤ Lib.pairMaj (rootTauQ38 p) R m + (9 / 4) *
        ((2 * G / Real.pi^2 + G^2 / Real.pi^4) / t^2) := by gcongr
    _ = _ := by dsimp [rootGapPairC38, t]; ring

end
end NlsGge.GK38
