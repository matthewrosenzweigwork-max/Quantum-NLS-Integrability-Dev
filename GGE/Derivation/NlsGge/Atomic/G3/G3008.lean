import NlsGge.GK38.AngleSegmentGeometry

set_option autoImplicit false

namespace NlsGge.Atomic.G3

/-- Along the segment from `a` to a point at least as close to `a` as to `b`,
the distance to `b` stays at least half of `‖b - a‖`. -/
theorem nearest_endpoint_segment (a b μ : ℂ) (t : ℝ)
    (_hab : a ≠ b) (hnear : ‖μ - a‖ ≤ ‖μ - b‖)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖b - a‖ / 2 ≤ ‖b - (a + (t : ℂ) * (μ - a))‖ := by
  have hroot :
      ‖a - b‖ / 2 ≤ ‖a + (t : ℂ) * (μ - a) - b‖ :=
    NlsGge.GK38.angleSegment_far_root38 a b μ t ht.1 ht.2 hnear
  calc
    ‖b - a‖ / 2 = ‖a - b‖ / 2 := by rw [norm_sub_rev]
    _ ≤ ‖a + (t : ℂ) * (μ - a) - b‖ := hroot
    _ = ‖b - (a + (t : ℂ) * (μ - a))‖ := by rw [norm_sub_rev]

end NlsGge.Atomic.G3
