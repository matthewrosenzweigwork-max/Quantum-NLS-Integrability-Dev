import NlsGge.Measure.FourierGaussian

set_option autoImplicit false

namespace NlsGge.Measure

/-- The exact scalar doubling identity used on a common finite-mode likelihood.
Conjugation is stated through `starRingEnd ℂ`, matching the elaborated exponent. -/
lemma commonLikelihoodScalarDoubling (q : ℝ) (u z : ℂ) :
    (2 * q * ((starRingEnd ℂ) u * z).re - q * ‖u‖ ^ 2) +
        (2 * q * ((starRingEnd ℂ) u * z).re - q * ‖u‖ ^ 2) =
      2 * q * ‖u‖ ^ 2 +
        (2 * q * ((starRingEnd ℂ) ((2 : ℂ) * u) * z).re -
          q * ‖(2 : ℂ) * u‖ ^ 2) := by
  have htwo : (starRingEnd ℂ) (2 : ℂ) = (2 : ℂ) := by
    exact map_ofNat (starRingEnd ℂ) 2
  have hstar : (starRingEnd ℂ) ((2 : ℂ) * u) =
      (2 : ℂ) * (starRingEnd ℂ) u := by
    calc
      (starRingEnd ℂ) ((2 : ℂ) * u) =
          (starRingEnd ℂ) (2 : ℂ) * (starRingEnd ℂ) u :=
            map_mul (starRingEnd ℂ) (2 : ℂ) u
      _ = (2 : ℂ) * (starRingEnd ℂ) u := by rw [htwo]
  have hreal :
      ((starRingEnd ℂ) ((2 : ℂ) * u) * z).re =
        2 * ((starRingEnd ℂ) u * z).re := by
    rw [hstar]
    calc
      (((2 : ℂ) * (starRingEnd ℂ) u) * z).re =
          ((2 : ℂ) * ((starRingEnd ℂ) u * z)).re := by congr 1 <;> ring
      _ = 2 * ((starRingEnd ℂ) u * z).re := by
        simp [Complex.mul_re]
  have hnorm : ‖(2 : ℂ) * u‖ ^ 2 = 4 * ‖u‖ ^ 2 := by
    rw [norm_mul]
    norm_num
    <;> ring
  rw [hreal, hnorm]
  ring

end NlsGge.Measure
