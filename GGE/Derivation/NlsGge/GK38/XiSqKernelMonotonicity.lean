import NlsGge.GK38.XiSqActualKernelBound

set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

/-- Typed scalar monotonicity and coefficient assembly, isolated from all functional quantifiers. -/
theorem a5KernelMajorant_mono38 (d r x b g h s t : ℝ) (hd : 0 < d)
    (hx : x ≤ b) (hh : h ≤ s+t) :
    (1/(8*d))*(4*(1+1/d)*x+8*(1+1/d)*(g/(4*d^2))+h/d)+t/(8*d*r) ≤
      ((1/(8*d))*(4*(1+1/d)))*b+
      ((1/(8*d))*(8*(1+1/d)/(4*d^2)))*g+
      ((1/(8*d))/d)*s+(((1/(8*d))/d)+1/(8*d*r))*t := by
  have hfirst : 4*(1+1/d)*x ≤ 4*(1+1/d)*b :=
    mul_le_mul_of_nonneg_left hx (by positivity)
  have hlast : h/d ≤ (s+t)/d := div_le_div_of_nonneg_right hh hd.le
  calc
    _ ≤ (1/(8*d))*(4*(1+1/d)*b+8*(1+1/d)*(g/(4*d^2))+(s+t)/d)+t/(8*d*r) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hfirst le_rfl) hlast) (by positivity)) le_rfl
    _ = _ := by ring

end
end NlsGge.GK38
