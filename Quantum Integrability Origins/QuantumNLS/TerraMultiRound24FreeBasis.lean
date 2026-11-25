import QuantumNLS.TerraMultiRound24SwapContour

/-! Action of the two involutions on the source's free ordered basis. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate
namespace QuantumNLS.LocalSpectral.Round24
open Round23

private theorem swap_chiFun (L : ℝ) (n : ℤ) (x : ℝ) :
    swapConj (chiFun L n 0 x) = chiFun L n 1 x := by
  ext i
  fin_cases i <;> simp [swapConj, vec2, chiFun, rate, sgn, ← Complex.exp_conj, map_ofNat]

private theorem parity_chiFun_zero (L : ℝ) (n : ℤ) (x : ℝ) :
    parityFlip (chiFun L n 0 x) = chiFun L n 0 x := by
  ext i
  fin_cases i <;> simp [parityFlip, Jm, chiFun ]

private theorem parity_chiFun_one (L : ℝ) (n : ℤ) (x : ℝ) :
    parityFlip (chiFun L n 1 x) = -chiFun L n 1 x := by
  ext i
  fin_cases i <;> simp [parityFlip, Jm, chiFun ]

/-- The anti-linear swap exchanges the free basis vectors. -/
theorem swap_chi_zero (L : ℝ) (n : ℤ) :
    liftFiber L swapConjIsometry (chi L n 0) = chi L n 1 := by
  rw [Lp.ext_iff]
  filter_upwards [swapConjIsometry.toContinuousLinearMap.coeFn_compLp (chi L n 0),
    (memLp_chiFun L n 0).coeFn_toLp, (memLp_chiFun L n 1).coeFn_toLp] with x h h0 h1
  change (swapConjIsometry.toContinuousLinearMap.compLp (chi L n 0)) x = _
  change (chi L n 0 : ℝ → E2) x = _ at h0
  change (chi L n 1 : ℝ → E2) x = _ at h1
  rw [h, h0, h1]
  exact swap_chiFun L n x


/-- The swap returns the second free basis vector to the first. -/
theorem swap_chi_one (L : ℝ) (n : ℤ) :
    liftFiber L swapConjIsometry (chi L n 1) = chi L n 0 := by
  rw [Lp.ext_iff]
  filter_upwards [swapConjIsometry.toContinuousLinearMap.coeFn_compLp (chi L n 1),
    (memLp_chiFun L n 0).coeFn_toLp, (memLp_chiFun L n 1).coeFn_toLp] with x h h0 h1
  change (swapConjIsometry.toContinuousLinearMap.compLp (chi L n 1)) x = _
  change (chi L n 0 : ℝ → E2) x = _ at h0
  change (chi L n 1 : ℝ → E2) x = _ at h1
  rw [h, h1, h0]
  have hs := congrArg swapConj (swap_chiFun L n x)
  change swapConj (chiFun L n 1 x) = chiFun L n 0 x
  simpa using hs.symm

/-- The sign flip acts diagonally on the free basis. -/
theorem parity_chi_zero (L : ℝ) (n : ℤ) :
    liftFiber L parityFlipIsometry (chi L n 0) = chi L n 0 := by
  rw [Lp.ext_iff]
  filter_upwards [parityFlipIsometry.toContinuousLinearMap.coeFn_compLp (chi L n 0),
    (memLp_chiFun L n 0).coeFn_toLp] with x h h0
  change (parityFlipIsometry.toContinuousLinearMap.compLp (chi L n 0)) x = _
  change (chi L n 0 : ℝ → E2) x = _ at h0
  rw [h, h0]
  exact parity_chiFun_zero L n x

theorem parity_chi_one (L : ℝ) (n : ℤ) :
    liftFiber L parityFlipIsometry (chi L n 1) = -chi L n 1 := by
  rw [Lp.ext_iff]
  filter_upwards [parityFlipIsometry.toContinuousLinearMap.coeFn_compLp (chi L n 1),
    (memLp_chiFun L n 1).coeFn_toLp, Lp.coeFn_neg (chi L n 1)] with x h h1 hn
  change (parityFlipIsometry.toContinuousLinearMap.compLp (chi L n 1)) x = _
  change (chi L n 1 : ℝ → E2) x = _ at h1
  rw [h, hn, Pi.neg_apply, h1]
  exact parity_chiFun_one L n x

end QuantumNLS.LocalSpectral.Round24
#print axioms QuantumNLS.LocalSpectral.Round24.swap_chi_zero
#print axioms QuantumNLS.LocalSpectral.Round24.swap_chi_one
#print axioms QuantumNLS.LocalSpectral.Round24.parity_chi_zero
#print axioms QuantumNLS.LocalSpectral.Round24.parity_chi_one
