import NlsGge.Atomic.DM.DM046

set_option autoImplicit false

noncomputable section

namespace NlsGge.Atomic.M.M054

/-- The linear integer weight occurring in the source factorization. -/
def indexWeight (j : ℤ) : ℝ := 1 + |(j : ℝ)|

/-- The M-054 source weight `w(j) = (1 + |j|) v(j)`. -/
def w (v : ℤ → ℝ) (j : ℤ) : ℝ := indexWeight j * v j

/-- Separate the shifted weight in the two-resolvent kernel. -/
theorem two_resolvent_weight_factor
    {v : ℤ → ℝ}
    (heven : ∀ j : ℤ, v (-j) = v j)
    (hv : NlsGge.Atomic.DM046.SubmultiplicativeWeight v)
    (k l n : ℤ) :
    w v (k - n) ≤
      indexWeight (k - n) * w v (k + l) * w v (-l - n) /
        (indexWeight (k + l) * indexWeight (l + n)) := by
  have hindex_pos (j : ℤ) : 0 < indexWeight j := by
    dsimp [indexWeight]
    positivity
  have hsum : (k + l) + (-l - n) = k - n := by omega
  have hv' : v (k - n) ≤ v (k + l) * v (-l - n) := by
    simpa only [hsum] using hv (k + l) (-l - n)
  have hindex_neg : indexWeight (-l - n) = indexWeight (l + n) := by
    have harg : -l - n = -(l + n) := by ring
    dsimp [indexWeight]
    have hcast : ((-l - n : ℤ) : ℝ) = -((l + n : ℤ) : ℝ) := by
      exact_mod_cast harg
    rw [hcast, abs_neg]
  calc
    w v (k - n) = indexWeight (k - n) * v (k - n) := rfl
    _ ≤ indexWeight (k - n) * (v (k + l) * v (-l - n)) :=
      mul_le_mul_of_nonneg_left hv' (le_of_lt (hindex_pos _))
    _ = indexWeight (k - n) * w v (k + l) * w v (-l - n) /
          (indexWeight (k + l) * indexWeight (l + n)) := by
      rw [w, w, hindex_neg]
      field_simp [ne_of_gt (hindex_pos (k + l)), ne_of_gt (hindex_pos (l + n))]
      <;> ring

end NlsGge.Atomic.M.M054

end
