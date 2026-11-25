import NlsGge.GK38.IsolatingGeometry

/-! Finite real-interval circle patches with exact quarter-radius lattice tails.
Neighboring positive margins select radii even for collapsed finite intervals. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem real_interval_circle_patch38 (lo hi : ℤ → ℝ) (N : ℕ)
    (hle : ∀ n : ℤ, lo n ≤ hi n) (hgap : ∀ n : ℤ, hi n < lo (n + 1))
    (htail : ∀ n : ℤ, (N : ℤ) < |n| →
      lo n = (n : ℝ) * Real.pi - Real.pi / 4 ∧ hi n = (n : ℝ) * Real.pi + Real.pi / 4) :
    ∃ C : ℤ → ℂ, ∃ R : ℤ → ℝ, ∃ c : ℝ, IsolatingGeometry38 C R c N ∧
      ∀ n : ℤ, |n| ≤ (N : ℤ) → Icc (lo n) (hi n) ⊆ {x : ℝ | (x : ℂ) ∈ ball (C n) (R n)} := by
  let ε : ℤ → ℝ := fun n => if |n| ≤ (N : ℤ) then
    min (lo n - hi (n - 1)) (lo (n + 1) - hi n) / 4 else 0
  have hleft : ∀ n : ℤ, hi (n - 1) < lo n := by
    intro n
    simpa only [sub_add_cancel] using hgap (n - 1)
  have heps : ∀ n : ℤ, 0 ≤ ε n ∧ ε n ≤ (lo n - hi (n - 1)) / 4 ∧
      ε n ≤ (lo (n + 1) - hi n) / 4 := by
    intro n
    by_cases hn : |n| ≤ (N : ℤ)
    · dsimp only [ε]
      rw [ite_eq_left hn]
      have hp : 0 < min (lo n - hi (n - 1)) (lo (n + 1) - hi n) :=
        lt_min (sub_pos.mpr (hleft n)) (sub_pos.mpr (hgap n))
      refine ⟨by positivity, ?_, ?_⟩ <;>
        nlinarith [min_le_left (lo n - hi (n - 1)) (lo (n + 1) - hi n),
          min_le_right (lo n - hi (n - 1)) (lo (n + 1) - hi n)]
    · dsimp only [ε]
      rw [ite_eq_right hn]
      refine ⟨le_rfl, ?_, ?_⟩ <;> linarith [hleft n, hgap n]
  have hepspos : ∀ n : ℤ, |n| ≤ (N : ℤ) → 0 < ε n := by
    intro n hn
    dsimp only [ε]
    rw [ite_eq_left hn]
    exact div_pos (lt_min (sub_pos.mpr (hleft n)) (sub_pos.mpr (hgap n))) (by norm_num)
  let C : ℤ → ℂ := fun n => (((lo n + hi n) / 2 : ℝ) : ℂ)
  let R : ℤ → ℝ := fun n => (hi n - lo n) / 2 + ε n
  have hTail : ∀ n : ℤ, (N : ℤ) < |n| → C n = countingCenter38 n ∧ R n = Real.pi / 4 := by
    intro n hn
    obtain ⟨hl, hh⟩ := htail n hn
    have he : ε n = 0 := by dsimp only [ε]; rw [ite_eq_right (not_le.mpr hn)]
    constructor
    · dsimp only [C]
      rw [hl, hh]
      have hm : ((n : ℝ) * Real.pi - Real.pi / 4 + ((n : ℝ) * Real.pi + Real.pi / 4)) / 2 =
          (n : ℝ) * Real.pi := by ring
      rw [hm]
      simp [countingCenter38]
    · dsimp only [R]
      rw [hl, hh, he]
      ring
  have hR : ∀ n : ℤ, 0 < R n := by
    intro n
    by_cases hn : |n| ≤ (N : ℤ)
    · dsimp only [R]
      linarith [hle n, hepspos n hn]
    · rw [(hTail n (lt_of_not_ge hn)).2]
      positivity
  have hmono : StrictMono (fun n => (C n).re) := by
    change StrictMono (fun n => (lo n + hi n) / 2)
    apply strictMono_int_of_lt_succ
    intro n
    linarith [hle n, hle (n + 1), hgap n]
  have hadj : ∀ n : ℤ, (C n).re + R n < (C (n + 1)).re - R (n + 1) := by
    intro n
    have hε := (heps n).2.2
    have hε' := (heps (n + 1)).2.1
    simp only [add_sub_cancel_right] at hε'
    dsimp only [C, R]
    simp only [Complex.ofReal_re]
    linarith [hgap n]
  have hLmono : StrictMono (fun n => (C n).re - R n) := by
    apply strictMono_int_of_lt_succ
    intro n
    linarith [hR n, hadj n]
  have hsepOrdered : ∀ m n : ℤ, m < n → R m + R n < dist (C m) (C n) := by
    intro m n hmn
    have hs := (hadj m).trans_le (hLmono.monotone (show m + 1 ≤ n from by omega))
    rw [dist_eq_norm, realType_norm_sub_real38 _ _ (by simp [C]) (by simp [C]),
      abs_of_neg (sub_neg.mpr (hmono hmn))]
    linarith
  have hsep : ∀ m n : ℤ, m ≠ n → R m + R n < dist (C m) (C n) := by
    intro m n hmn
    rcases lt_or_gt_of_ne hmn with hh | hh
    · exact hsepOrdered m n hh
    · simpa only [add_comm, dist_comm] using hsepOrdered n m hh
  obtain ⟨c, hgeom⟩ := tail_comparable_geometry38 C R N
    (fun n => ⟨hR n, by simp [C]⟩) hmono hsep hTail
  refine ⟨C, R, c, hgeom, ?_⟩
  intro n hn x hx
  have hnorm : ‖(x : ℂ) - C n‖ = |x - (lo n + hi n) / 2| := by
    dsimp only [C]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  change (x : ℂ) ∈ ball (C n) (R n)
  rw [mem_ball_iff_norm, hnorm]
  apply abs_lt.mpr
  dsimp only [R]
  constructor <;> linarith [hx.1, hx.2, hepspos n hn]

end
end NlsGge.GK38
