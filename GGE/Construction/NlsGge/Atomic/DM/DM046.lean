import Mathlib

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.DM046

/-- Pointwise submultiplicativity for a weight on the additive integer group. -/
def SubmultiplicativeWeight (w : ℤ → ℝ) : Prop :=
  ∀ k l : ℤ, w (k + l) ≤ w k * w l

theorem submultiplicativeWeight_iff (w : ℤ → ℝ) :
    SubmultiplicativeWeight w ↔ ∀ k l : ℤ, w (k + l) ≤ w k * w l := Iff.rfl

/-- The even integer weight obtained by exponentiating a natural-number log profile. -/
def logRatioWeight (h : ℕ → ℝ) (k : ℤ) : ℝ := Real.exp (h k.natAbs)

theorem h_add_le_of_logRatio_antitone (h : ℕ → ℝ)
    (hratio : Antitone (fun n : ℕ+ => h n / (n : ℝ)))
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    h (a + b) ≤ h a + h b := by
  have hdenA : 0 < (a : ℝ) := by exact_mod_cast ha
  have hdenB : 0 < (b : ℝ) := by exact_mod_cast hb
  have hdenAB : 0 < ((a + b : ℕ) : ℝ) := by
    have hab : 0 < a + b := by omega
    exact_mod_cast hab
  have hratioA : h (a + b) / ((a + b : ℕ) : ℝ) ≤ h a / (a : ℝ) := by
    have hindex : (⟨a, ha⟩ : ℕ+) ≤ ⟨a + b, by omega⟩ := by
      change a ≤ a + b
      exact Nat.le_add_right a b
    have hh := hratio hindex
    change h (a + b) / ((a + b : ℕ) : ℝ) ≤ h a / (a : ℝ) at hh
    exact hh
  have hratioB : h (a + b) / ((a + b : ℕ) : ℝ) ≤ h b / (b : ℝ) := by
    have hindex : (⟨b, hb⟩ : ℕ+) ≤ ⟨a + b, by omega⟩ := by
      change b ≤ a + b
      exact Nat.le_add_left b a
    have hh := hratio hindex
    change h (a + b) / ((a + b : ℕ) : ℝ) ≤ h b / (b : ℝ) at hh
    exact hh
  have hcrossA : h (a + b) * (a : ℝ) ≤ h a * ((a + b : ℕ) : ℝ) :=
    (div_le_div_iff₀ hdenAB hdenA).1 hratioA
  have hcrossB : h (a + b) * (b : ℝ) ≤ h b * ((a + b : ℕ) : ℝ) :=
    (div_le_div_iff₀ hdenAB hdenB).1 hratioB
  have hcross : h (a + b) * ((a + b : ℕ) : ℝ) ≤
      (h a + h b) * ((a + b : ℕ) : ℝ) := by
    calc
      h (a + b) * ((a + b : ℕ) : ℝ) =
          h (a + b) * (a : ℝ) + h (a + b) * (b : ℝ) := by push_cast; ring
      _ ≤ h a * ((a + b : ℕ) : ℝ) + h b * ((a + b : ℕ) : ℝ) := add_le_add hcrossA hcrossB
      _ = (h a + h b) * ((a + b : ℕ) : ℝ) := by ring
  exact le_of_mul_le_mul_right hcross hdenAB

theorem h_add_le_of_logRatio_antitone_nat (h : ℕ → ℝ) (hzero : h 0 = 0)
    (hratio : Antitone (fun n : ℕ+ => h n / (n : ℝ))) (a b : ℕ) :
    h (a + b) ≤ h a + h b := by
  by_cases ha : a = 0
  · subst a
    simpa [hzero]
  · by_cases hb : b = 0
    · subst b
      simpa [hzero]
    · exact h_add_le_of_logRatio_antitone h hratio a b (Nat.pos_of_ne_zero ha)
        (Nat.pos_of_ne_zero hb)

theorem logRatioWeight_one_at_zero (h : ℕ → ℝ) (hzero : h 0 = 0) :
    logRatioWeight h 0 = 1 := by
  simp [logRatioWeight, hzero]

theorem logRatioWeight_pos (h : ℕ → ℝ) (k : ℤ) : 0 < logRatioWeight h k :=
  Real.exp_pos _

theorem logRatioWeight_even (h : ℕ → ℝ) (k : ℤ) :
    logRatioWeight h (-k) = logRatioWeight h k := by
  simp [logRatioWeight]

theorem h_natAbs_add_le_of_logRatio_antitone (h : ℕ → ℝ) (hzero : h 0 = 0)
    (hmono : Monotone h)
    (hratio : Antitone (fun n : ℕ+ => h n / (n : ℝ))) (k l : ℤ) :
    h (k + l).natAbs ≤ h k.natAbs + h l.natAbs := by
  calc
    h (k + l).natAbs ≤ h (k.natAbs + l.natAbs) := hmono (Int.natAbs_add_le k l)
    _ ≤ h k.natAbs + h l.natAbs := h_add_le_of_logRatio_antitone_nat h hzero hratio _ _

/-- DM Lemma 46: a monotone log profile with decreasing positive-index ratios gives
an even, normalized, pointwise submultiplicative integer weight after exponentiation. -/
theorem logRatio_weight_submultiplicative (h : ℕ → ℝ) (hzero : h 0 = 0)
    (hmono : Monotone h)
    (hratio : Antitone (fun n : ℕ+ => h n / (n : ℝ))) :
    SubmultiplicativeWeight (logRatioWeight h) := by
  intro k l
  change Real.exp (h (k + l).natAbs) ≤
    Real.exp (h k.natAbs) * Real.exp (h l.natAbs)
  rw [← Real.exp_add]
  exact Real.exp_le_exp.mpr
    (h_natAbs_add_le_of_logRatio_antitone h hzero hmono hratio k l)

end NlsGge.Atomic.DM046
