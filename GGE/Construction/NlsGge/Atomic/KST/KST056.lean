import NlsGge.Atomic.KST.KST055

set_option autoImplicit false

namespace NlsGge.Atomic.KST

noncomputable section

/-- The source's slowly increasing dyadic minorant, extended harmlessly by
zero at index zero. On positive indices its recurrence is exactly the one in
Kappeler--Serier--Topalov, Lemma 9.1. -/
def dyadicMinorant (c : ℕ → ℝ) : (n : ℕ) → ℝ
  | 0 => 0
  | 1 => c 1
  | n + 2 =>
      if (n + 2) % 2 = 0 then
        min (2 * dyadicMinorant c ((n + 2) / 2)) (c (n + 2))
      else
        dyadicMinorant c (n + 1)
termination_by n => n
decreasing_by
  · exact Nat.div_lt_self (by omega) (by omega)
  · omega

@[simp] theorem dyadicMinorant_zero (c : ℕ → ℝ) : dyadicMinorant c 0 = 0 := by
  simp [dyadicMinorant]

@[simp] theorem dyadicMinorant_one (c : ℕ → ℝ) : dyadicMinorant c 1 = c 1 := by
  simp [dyadicMinorant]

/-- Even-index source recurrence. The hypothesis keeps the recursive parent
index positive, as in the source's one-based sequence. -/
theorem dyadicMinorant_even (c : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    dyadicMinorant c (2 * n) =
      min (2 * dyadicMinorant c n) (c (2 * n)) := by
  cases n with
  | zero => omega
  | succ n =>
      have hidx : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [hidx, dyadicMinorant]
      have he : (2 * n + 2) % 2 = 0 := by omega
      have hdiv : (2 * n + 2) / 2 = n + 1 := by omega
      simp [he, hdiv]

/-- Odd-index source recurrence. -/
theorem dyadicMinorant_odd (c : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n) :
    dyadicMinorant c (2 * n + 1) = dyadicMinorant c (2 * n) := by
  cases n with
  | zero => omega
  | succ n =>
      have hidx : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by omega
      rw [hidx, dyadicMinorant]
      simp
      have hidx' : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
      rw [hidx']

private theorem dyadicMinorant_pos_le (c : ℕ → ℝ)
    (hpos : ∀ n, 1 ≤ n → 0 < c n)
    (hmono : MonotoneOn c (Set.Ici 1)) :
    ∀ n, 1 ≤ n → 0 < dyadicMinorant c n ∧ dyadicMinorant c n ≤ c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hone : n = 1
      · subst n
        rw [dyadicMinorant_one]
        exact ⟨hpos 1 (by omega), le_rfl⟩
      · have hn2 : 2 ≤ n := by omega
        by_cases he : n % 2 = 0
        · let m := n / 2
          have hm' : n = 2 * m := by dsimp [m]; omega
          have hmpos : 1 ≤ m := by omega
          have hm_lt : m < n := by omega
          have hi := ih m hm_lt hmpos
          rw [hm', dyadicMinorant_even c m hmpos]
          constructor
          · apply lt_min
            · nlinarith [hi.1]
            · exact hpos (2 * m) (by omega)
          · exact min_le_right _ _
        · have hmod : n % 2 = 1 := by omega
          let m := n / 2
          have hmform : n = 2 * m + 1 := by
            dsimp [m]
            omega
          have hmpos : 1 ≤ m := by omega
          have heq : dyadicMinorant c n = dyadicMinorant c (2 * m) := by
            rw [hmform, dyadicMinorant_odd c m hmpos]
          rw [heq]
          have hm_lt : m < n := by omega
          have hi := ih m hm_lt hmpos
          have hprev_lt : 2 * m < n := by omega
          have hprev := ih (2 * m) hprev_lt (by omega)
          constructor
          · exact hprev.1
          · calc
              dyadicMinorant c (2 * m) ≤ c (2 * m) := hprev.2
              _ ≤ c n := by
                have hfirst : 2 * m ∈ Set.Ici (1 : ℕ) := by simp; omega
                have hsecond : n ∈ Set.Ici (1 : ℕ) := by simp; omega
                exact hmono hfirst hsecond (by omega)

private theorem dyadicMinorant_step (c : ℕ → ℝ)
    (hpos : ∀ n, 1 ≤ n → 0 < c n)
    (hmono : MonotoneOn c (Set.Ici 1)) :
    ∀ n, 1 ≤ n → dyadicMinorant c n ≤ dyadicMinorant c (n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      by_cases hone : n = 1
      · subst n
        simp only [dyadicMinorant_one]
        rw [dyadicMinorant_even c 1 (by omega)]
        simp only [dyadicMinorant_one]
        apply le_min
        · nlinarith [hpos 1 (by omega)]
        · exact hmono (by norm_num) (by norm_num) (by norm_num)
      · have hn2 : 2 ≤ n := by omega
        by_cases he : n % 2 = 0
        · let m := n / 2
          have hm' : n = 2 * m := by dsimp [m]; omega
          have hmpos : 1 ≤ m := by omega
          rw [hm', dyadicMinorant_odd c m hmpos]
        · have hmod : n % 2 = 1 := by omega
          let m := n / 2
          have hmform : n = 2 * m + 1 := by
            dsimp [m]
            omega
          have hmpos : 1 ≤ m := by omega
          rw [hmform, dyadicMinorant_odd c m hmpos]
          have hnext : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
          rw [hnext, dyadicMinorant_even c (m + 1) (by omega)]
          have hstep := ih m (by omega) hmpos
          have hdouble := dyadicMinorant_even c m hmpos
          have hdom := (dyadicMinorant_pos_le c hpos hmono (2 * m) (by omega)).2
          apply le_min
          · calc
              dyadicMinorant c (2 * m) ≤ 2 * dyadicMinorant c m := by
                rw [hdouble]
                exact min_le_left _ _
              _ ≤ 2 * dyadicMinorant c (m + 1) := by
                exact mul_le_mul_of_nonneg_left hstep (by norm_num)
          · have hfirst : 2 * m ∈ Set.Ici (1 : ℕ) := by simp; omega
            have hsecond : 2 * m + 2 ∈ Set.Ici (1 : ℕ) := by simp
            exact le_trans hdom (hmono hfirst hsecond (by omega))

/-- All source properties of the positive-index recursive minorant. -/
theorem dyadicMinorant_properties (c : ℕ → ℝ)
    (hpos : ∀ n, 1 ≤ n → 0 < c n)
    (hmono : MonotoneOn c (Set.Ici 1)) :
    (∀ n, 1 ≤ n → 0 < dyadicMinorant c n) ∧
    MonotoneOn (dyadicMinorant c) (Set.Ici 1) ∧
    (∀ n, 1 ≤ n → dyadicMinorant c n ≤ c n) ∧
    (∀ n, 1 ≤ n → dyadicMinorant c (2 * n) ≤ 2 * dyadicMinorant c n) := by
  have hprops := dyadicMinorant_pos_le c hpos hmono
  refine ⟨fun n hn => (hprops n hn).1, ?_, fun n hn => (hprops n hn).2, ?_⟩
  · intro a ha b hb hab
    have haux : ∀ b, ∀ a, 1 ≤ a → a ≤ b →
        dyadicMinorant c a ≤ dyadicMinorant c b := by
      intro b
      induction b with
      | zero =>
          intro a ha hab
          omega
      | succ b ih =>
          intro a ha hab
          by_cases heq : a = b + 1
          · simpa [heq]
          · have hab' : a ≤ b := by omega
            exact le_trans (ih a ha hab')
              (dyadicMinorant_step c hpos hmono b (by omega))
    exact haux b a (by simpa using ha) (by simpa using hab)
  · intro n hn
    rw [dyadicMinorant_even c n hn]
    exact min_le_left _ _

end
end NlsGge.Atomic.KST
