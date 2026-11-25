import NlsGge.Hierarchy.UniformPartitionBound38
import NlsGge.Ramer.ActualHeadLawBridge

/-! # NEW-F11 (`F:cor:charge`, v2 l.1801-1819), file 1: lowering finitely many coefficients; the free-normalizer product

Source: `paper/v2.tex` l.1808-1812 (first two sentences of the proof of `F:cor:charge`). This file is `B`-free.

Notation (v2). `β_j = c_j/(j!)^4 = NlsGge.coefficient c j`, `W(r) = Σ_j β_j r^{2j} = weight c r`,
`a_n = W(2πn) = fullWeightRate c n`. For a finite collection `t_j`, `0 ≤ t_j < β_j` (`j ≤ J`),
`p(r) = Σ_{j ≤ J} t_j r^{2j}` (`tiltPoly38`) and `W - p` has coefficients
`β_j - t_j` (`j ≤ J`), `β_j` (`j > J`); in terms of the numerators this is
`tiltCoeff38 c J t j = c_j - t_j (j!)^4` (`j ≤ J`), `c_j` otherwise.

* **NEW-F11.01** `tiltedCoefficients38`: `W - p` belongs to a class (`eq:weight`) with the explicit lower bound
  `tiltLower38 c J t = min (c₋, min_{j ≤ J} (c_j - t_j (j!)^4)) > 0` and the same upper bound `c₊`
  (`tiltLower38_pos`, `tiltCoeff_admitted38`); `weight_tilt38 : W_{c'}(r) = W_c(r) - p(r)` and
  `tiltRatio_ge38 : ε W_c ≤ W_{c'}` with an explicit `ε ∈ (0,1]`.
* **NEW-F11.02** `tiltDet38 c J t N = D_{p,N} = ∏_{|n|≤N} (1 - p(2πn)/a_n)`: every factor is in `[ε,1]`
  (`tiltFactor_*`), `Σ_n p(2πn)/a_n < ∞` (`summable_tiltRatio38`), hence `D_{p,N} ≥ δ > 0` uniformly in `N`
  (`tiltDet_lower38`), and `D_{p,N}` converges to a positive limit (`tiltDet_tendsto38`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.HierarchyRiccati.Core Filter Topology
open scoped Real

section Tilt

variable {lower upper : ℝ}

/-- The numerators of `W - p`: `c_j - t_j (j!)^4` for `j ≤ J` and `c_j` for `j > J`
(so that `β_j' = β_j - t_j` for `j ≤ J`). -/
def tiltCoeff38 (c : ℕ → ℝ) (J : ℕ) (t : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j ≤ J then c j - t j * ((j.factorial : ℝ)) ^ 4 else c j

/-- `p(r) = Σ_{j=0}^J t_j r^{2j}`. -/
def tiltPoly38 (J : ℕ) (t : ℕ → ℝ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), t j * r ^ (2 * j)

theorem coefficient_tilt38 (c : ℕ → ℝ) (J : ℕ) (t : ℕ → ℝ) (j : ℕ) :
    NlsGge.coefficient (tiltCoeff38 c J t) j =
      NlsGge.coefficient c j - (if j ≤ J then t j else 0) := by
  unfold NlsGge.coefficient tiltCoeff38
  have h : ((j.factorial : ℝ)) ^ 4 ≠ 0 := by positivity
  split_ifs
  · field_simp
  · simp

theorem coefficient_nonneg_F11_38 (c : BoundedCoefficients lower upper) (j : ℕ) :
    0 ≤ NlsGge.coefficient c.val j := by
  unfold NlsGge.coefficient
  have := c.property.1.trans_le (c.property.2.2 j).1
  positivity

theorem tiltPoly38_nonneg (J : ℕ) (t : ℕ → ℝ) (ht : ∀ j ≤ J, 0 ≤ t j) (r : ℝ) :
    0 ≤ tiltPoly38 J t r :=
  Finset.sum_nonneg fun j hj => mul_nonneg (ht j (by simpa [Nat.lt_succ_iff] using hj))
    (by rw [pow_mul]; positivity)

/-- Hypothesis of the claim: `0 ≤ t_j < β_j` for `j ≤ J`. -/
def TiltAdmissible38 (c : BoundedCoefficients lower upper) (J : ℕ) (t : ℕ → ℝ) : Prop :=
  ∀ j ≤ J, 0 ≤ t j ∧ t j < NlsGge.coefficient c.val j

theorem tilt_pos38 (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) {j : ℕ} (hj : j ≤ J) :
    0 < tiltCoeff38 c.val J t j := by
  have h := (ht j hj).2
  unfold NlsGge.coefficient at h
  have hf : (0 : ℝ) < ((j.factorial : ℝ)) ^ 4 := by positivity
  rw [lt_div_iff₀ hf] at h
  unfold tiltCoeff38
  simp only [hj, ↓reduceIte]; linarith

/-- The lower coefficient bound of `W - p` (NEW-F11.01):
`min (c₋, min_{j ≤ J} (c_j - t_j (j!)^4))`. -/
def tiltLower38 (c : BoundedCoefficients lower upper) (J : ℕ) (t : ℕ → ℝ) : ℝ :=
  min lower ((Finset.range (J + 1)).inf' (Finset.nonempty_range_iff.2 (Nat.succ_ne_zero J)) (fun j => tiltCoeff38 c.val J t j))

theorem tiltLower38_pos (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) : 0 < tiltLower38 c J t := by
  unfold tiltLower38
  refine lt_min c.property.1 ?_
  rw [Finset.lt_inf'_iff]
  intro j hj
  exact tilt_pos38 c ht (by simpa [Nat.lt_succ_iff] using hj)

theorem tiltCoeff_admitted38 (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) :
    AdmittedCoefficients (tiltLower38 c J t) upper (tiltCoeff38 c.val J t) := by
  have hl := c.property.1
  have hlu := c.property.2.1
  refine ⟨tiltLower38_pos c ht, (min_le_left _ _).trans hlu, fun j => ⟨?_, ?_⟩⟩
  · by_cases hj : j ≤ J
    · exact (min_le_right _ _).trans (Finset.inf'_le _ (by simpa [Nat.lt_succ_iff] using hj))
    · unfold tiltCoeff38
      simp only [hj, ↓reduceIte]
      exact (min_le_left _ _).trans (c.property.2.2 j).1
  · unfold tiltCoeff38
    split_ifs with hj
    · have h1 : 0 ≤ t j * ((j.factorial : ℝ)) ^ 4 :=
        mul_nonneg (ht j hj).1 (by positivity)
      linarith [(c.property.2.2 j).2]
    · exact (c.property.2.2 j).2

/-- **NEW-F11.01.** `W - p` as an element of the class `eq:weight` with the explicit lower bound
`tiltLower38 c J t > 0` and the original upper bound `c₊`. -/
def tiltedCoefficients38 (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) : BoundedCoefficients (tiltLower38 c J t) upper :=
  ⟨tiltCoeff38 c.val J t, tiltCoeff_admitted38 c ht⟩

@[simp] theorem tiltedCoefficients38_val (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) : (tiltedCoefficients38 c ht).val = tiltCoeff38 c.val J t := rfl

/-- Termwise: `weightTerm (W-p) = weightTerm W - [j ≤ J] t_j r^{2j}`. -/
theorem weightTerm_tilt38 (c : ℕ → ℝ) (J : ℕ) (t : ℕ → ℝ) (r : ℝ) (j : ℕ) :
    NlsGge.weightTerm (tiltCoeff38 c J t) r j =
      NlsGge.weightTerm c r j - (if j ≤ J then t j * r ^ (2 * j) else 0) := by
  unfold NlsGge.weightTerm
  rw [coefficient_tilt38]
  split_ifs <;> ring

theorem summable_tiltTerm38 (J : ℕ) (t : ℕ → ℝ) (r : ℝ) :
    Summable (fun j : ℕ => if j ≤ J then t j * r ^ (2 * j) else 0) := by
  refine summable_of_ne_finset_zero (s := Finset.range (J + 1)) fun j hj => ?_
  have : ¬ j ≤ J := fun h => hj (by simpa [Nat.lt_succ_iff] using h)
  simp [this]

theorem tsum_tiltTerm38 (J : ℕ) (t : ℕ → ℝ) (r : ℝ) :
    ∑' j : ℕ, (if j ≤ J then t j * r ^ (2 * j) else 0) = tiltPoly38 J t r := by
  rw [tsum_eq_sum (s := Finset.range (J + 1))]
  · unfold tiltPoly38
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j ≤ J := by simpa [Nat.lt_succ_iff] using hj
    simp only [hj', ↓reduceIte]
  · intro j hj
    have : ¬ j ≤ J := fun h => hj (by simpa [Nat.lt_succ_iff] using h)
    simp [this]

/-- `W_{c'}(r) = W_c(r) - p(r)` (`c'` the lowered coefficients). -/
theorem weight_tilt38 (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) (r : ℝ) :
    weight (tiltCoeff38 c.val J t) r = weight c.val r - tiltPoly38 J t r := by
  have hs1 : Summable (NlsGge.weightTerm c.val r) :=
    weightTerm_summable lower upper c.val c.property.1 ((fun j => (c.property.2.2 j).1)) ((fun j => (c.property.2.2 j).2)) r
  have hs2 := summable_tiltTerm38 J t r
  unfold weight
  have key : (NlsGge.weightTerm (tiltCoeff38 c.val J t) r) =
      fun j => NlsGge.weightTerm c.val r j - (if j ≤ J then t j * r ^ (2 * j) else 0) :=
    funext (weightTerm_tilt38 c.val J t r)
  rw [key, Summable.tsum_sub hs1 hs2, tsum_tiltTerm38]

/-- Lower comparison: there is `ε ∈ (0,1]` with `ε W_c ≤ W_{c'}` everywhere. -/
theorem exists_tiltRatio38 (c : BoundedCoefficients lower upper) {J : ℕ} {t : ℕ → ℝ}
    (ht : TiltAdmissible38 c J t) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ r : ℝ, ε * weight c.val r ≤ weight (tiltCoeff38 c.val J t) r := by
  -- a uniform ratio for the finitely many lowered coefficients
  have hfin : ∀ K : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ j ≤ K, j ≤ J →
      ε₀ * NlsGge.coefficient c.val j ≤ NlsGge.coefficient c.val j - t j := by
    intro K
    induction K with
    | zero =>
      by_cases h0 : 0 ≤ J
      · have hc : 0 < NlsGge.coefficient c.val 0 := by
          have := c.property.1.trans_le (c.property.2.2 0).1
          unfold NlsGge.coefficient; positivity
        have := (ht 0 h0).2
        refine ⟨(NlsGge.coefficient c.val 0 - t 0) / NlsGge.coefficient c.val 0,
          div_pos (by linarith) hc, fun j hj _ => ?_⟩
        have : j = 0 := by omega
        subst this
        rw [div_mul_cancel₀ _ hc.ne']
      · exact ⟨1, one_pos, fun j _ hj => absurd hj (by omega)⟩
    | succ K ih =>
      obtain ⟨ε₀, hε₀, hK⟩ := ih
      by_cases hJ : K + 1 ≤ J
      · have hc : 0 < NlsGge.coefficient c.val (K + 1) := by
          have := c.property.1.trans_le (c.property.2.2 (K + 1)).1
          unfold NlsGge.coefficient; positivity
        have := (ht (K + 1) hJ).2
        refine ⟨min ε₀ ((NlsGge.coefficient c.val (K + 1) - t (K + 1)) /
          NlsGge.coefficient c.val (K + 1)), lt_min hε₀ (div_pos (by linarith) hc),
          fun j hj hjJ => ?_⟩
        rcases Nat.lt_or_ge j (K + 1) with h | h
        · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by
            have := c.property.1.trans_le (c.property.2.2 j).1
            unfold NlsGge.coefficient; positivity)).trans (hK j (by omega) hjJ)
        · have : j = K + 1 := by omega
          subst this
          calc _ ≤ ((NlsGge.coefficient c.val (K + 1) - t (K + 1)) /
              NlsGge.coefficient c.val (K + 1)) * NlsGge.coefficient c.val (K + 1) :=
                mul_le_mul_of_nonneg_right (min_le_right _ _) hc.le
            _ = _ := div_mul_cancel₀ _ hc.ne'
      · exact ⟨ε₀, hε₀, fun j hj hjJ => hK j (by omega) hjJ⟩
  obtain ⟨ε₀, hε₀, hε⟩ := hfin J
  refine ⟨min ε₀ 1, lt_min hε₀ one_pos, min_le_right _ _, fun r => ?_⟩
  have hs1 : Summable (NlsGge.weightTerm c.val r) :=
    weightTerm_summable lower upper c.val c.property.1 ((fun j => (c.property.2.2 j).1)) ((fun j => (c.property.2.2 j).2)) r
  have hs2 : Summable (NlsGge.weightTerm (tiltCoeff38 c.val J t) r) :=
    weightTerm_summable (tiltLower38 c J t) upper (tiltCoeff38 c.val J t)
      (tiltLower38_pos c ht) (fun j => ((tiltCoeff_admitted38 c ht).2.2 j).1)
      (fun j => ((tiltCoeff_admitted38 c ht).2.2 j).2) r
  unfold weight
  rw [← tsum_mul_left]
  refine hs1.mul_left _ |>.tsum_le_tsum (fun j => ?_) hs2
  have hr : 0 ≤ r ^ (2 * j) := by rw [pow_mul]; positivity
  have hc0 : 0 ≤ NlsGge.coefficient c.val j := coefficient_nonneg_F11_38 c j
  unfold NlsGge.weightTerm
  rw [coefficient_tilt38, ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hr
  by_cases hj : j ≤ J
  · simp only [hj, ↓reduceIte]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hc0).trans (hε j hj hj)
  · simp only [hj, ↓reduceIte]
    simpa using mul_le_mul_of_nonneg_right (min_le_right ε₀ 1) hc0

end Tilt

end NlsGge.Birkhoff
end
