import NlsGge.Sobolev.WeightedHilbert

set_option autoImplicit false
noncomputable section

namespace NlsGge.Pilot

local instance : Fact (∀ n : ℤ, 0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The constant-weight complex ℓ² isometry preserves the raw coordinate of
an element viewed through the real-restricted carrier. -/
theorem unweightedRealIsometry_coordinateSecond
    (y : WeightedRealHilbert (fun _ : ℤ => (1 : ℝ))) (n : ℤ) :
    (weightedIsometry (fun _ : ℤ => (1 : ℝ))
      (show WeightedHilbert (fun _ : ℤ => (1 : ℝ)) from y)) n =
        (show WeightedHilbert (fun _ : ℤ => (1 : ℝ)) from y) n := by
  rw [weightedIsometry_apply]
  change (Real.sqrt (1 : ℝ) : ℂ) *
    (show WeightedHilbert (fun _ : ℤ => (1 : ℝ)) from y) n =
      (show WeightedHilbert (fun _ : ℤ => (1 : ℝ)) from y) n
  simp only [Real.sqrt_one, Complex.ofReal_one, one_mul]

end NlsGge.Pilot
