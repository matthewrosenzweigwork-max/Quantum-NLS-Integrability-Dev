import QuantumNLS.Local001Basis

set_option autoImplicit false
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.LocalSpectral

/-- The source contour around the free eigenvalue `p_n`. -/
def OnGamma (L r : ℝ) (n : ℤ) (z : ℂ) : Prop :=
  ‖z - (LocalSpectral.pm L n : ℂ)‖ = r

/-- Distance from a point on the `n`th contour to a same-parity free eigenvalue. -/
theorem contour_distance_lower {L r : ℝ} (hL : 0 < L)
    {n k : ℤ} {z : ℂ}
    (hz : ‖z - (LocalSpectral.pm L n : ℂ)‖ = r) :
    spacing L * |(k : ℝ)| - r ≤ ‖z - (LocalSpectral.pm L (n + 2 * k) : ℂ)‖ := by
  have hshift := pm_even_shift (L := L) n k
  have htriangle := norm_sub_le (z - (LocalSpectral.pm L n : ℂ))
    (z - (LocalSpectral.pm L (n + 2 * k) : ℂ))
  have halgebra : (z - (LocalSpectral.pm L n : ℂ)) -
      (z - (LocalSpectral.pm L (n + 2 * k) : ℂ)) = ((spacing L * k : ℝ) : ℂ) := by
    rw [hshift]
    push_cast
    ring
  have hnorm : ‖((spacing L * k : ℝ) : ℂ)‖ = spacing L * |(k : ℝ)| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (spacing_pos hL)]
  rw [halgebra, hnorm, hz] at htriangle
  nlinarith

/-- On `Γ_n`, every denominator in the fixed parity sector is bounded below by `r`. -/
theorem contour_denominator_lower {L r : ℝ} (hL : 0 < L)
    (hsmall : r < spacing L / 2) {n m : ℤ} {z : ℂ}
    (hz : OnGamma L r n z) (hpar : LocalSpectral.parity m = LocalSpectral.parity n) :
    r ≤ ‖z - (LocalSpectral.pm L m : ℂ)‖ := by
  by_cases hmn : m = n
  · subst m
    exact hz.symm.le
  · obtain ⟨k, hk⟩ := (even_iff_two_dvd.mp (parity_eq_even_sub hpar))
    have hindex : m = n + 2 * k := by omega
    have hk0 : k ≠ 0 := by
      intro hkz
      apply hmn
      rw [hindex, hkz]
      ring
    have hdist := contour_distance_lower hL (n := n) (k := k) (z := z) hz
    have hdist' : spacing L * |(k : ℝ)| - r ≤ ‖z - (LocalSpectral.pm L m : ℂ)‖ := by
      simpa only [← hindex] using hdist
    have hkabs : 1 ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
    have hd : 0 < spacing L := spacing_pos hL
    have hmul : spacing L ≤ spacing L * |(k : ℝ)| := by
      calc
        spacing L = spacing L * 1 := by ring
        _ ≤ spacing L * |(k : ℝ)| := mul_le_mul_of_nonneg_left hkabs hd.le
    linarith

/-- The free `L²` resolvent multiplier attached to a source mode. -/
def freeResolventMultiplier (L : ℝ) (n : ℤ) (z : ℂ) (m : ℤ) : ℂ :=
  (z - (LocalSpectral.pm L m : ℂ))⁻¹

/-- Every same-parity free resolvent multiplier on `Γ_n` has norm at most `1/r`. -/
theorem freeResolventMultiplier_norm_le {L r : ℝ} (hL : 0 < L) {n m : ℤ}
    {z : ℂ} (hr : 0 < r) (hsmall : r < spacing L / 2)
    (hz : OnGamma L r n z)
    (hpar : LocalSpectral.parity m = LocalSpectral.parity n) :
    ‖freeResolventMultiplier L n z m‖ ≤ r⁻¹ := by
  have hden := contour_denominator_lower hL hsmall hz hpar
  have hpos : 0 < ‖z - (LocalSpectral.pm L m : ℂ)‖ := lt_of_lt_of_le hr hden
  rw [freeResolventMultiplier, norm_inv]
  exact (inv_le_inv₀ hpos hr).2 hden

#print axioms contour_denominator_lower
#print axioms freeResolventMultiplier_norm_le

end QuantumNLS.ResetFreeResolventLOCAL001
