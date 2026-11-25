import QuantumNLS.LocalSpectralReduced

/-! Pointwise symmetries of the DEF-049 differential expression.  These
identities do not assert the corresponding graph, resolvent or contour laws. -/
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace QuantumNLS.LocalSpectral.Round23

/-- The source's anti-linear component swap on a point of the fiber. -/
def swapConj (v : E2) : E2 := vec2 (conj (v 1)) (conj (v 0))

/-- The source's sign change on the second component. -/
def parityFlip (v : E2) : E2 := Jm v

@[simp] theorem swapConj_involutive (v : E2) : swapConj (swapConj v) = v := by
  ext i
  fin_cases i <;> simp [swapConj, vec2]

@[simp] theorem parityFlip_involutive (v : E2) : parityFlip (parityFlip v) = v := by
  ext i
  fin_cases i <;> simp [parityFlip, Jm, vec2, add_comm]

/-- The differential expression commutes with the anti-linear swap, with
both the function and derivative transformed. -/
theorem lopPt_swapConj (κ : ℝ) (w : ℂ) (d g : E2) :
    swapConj (lopPt κ w d g) = lopPt κ w (swapConj d) (swapConj g) := by
  ext i
  fin_cases i <;> simp [swapConj, lopPt, Jm, vec2, map_add, map_mul, map_ofNat]

/-- Conjugating the differential expression by the component sign changes
sends the potential to its negative. -/
theorem lopPt_parityFlip (κ : ℝ) (w : ℂ) (d g : E2) :
    parityFlip (lopPt κ w d g) = lopPt κ (-w) (parityFlip d) (parityFlip g) := by
  ext i
  fin_cases i <;> simp [parityFlip, lopPt, Jm, vec2, add_comm]

/-- The anti-linear fiber swap is an isometry over the real scalars. -/
def swapConjIsometry : E2 →ₗᵢ[ℝ] E2 where
  toFun := swapConj
  map_add' v w := by
    ext i
    fin_cases i <;> simp [swapConj, vec2]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [swapConj, vec2, Complex.real_smul]
  norm_map' v := by
    simp [PiLp.norm_eq_of_L2, Fin.sum_univ_two, swapConj, vec2, add_comm]

/-- The component sign flip is an isometry over the real scalars. -/
def parityFlipIsometry : E2 →ₗᵢ[ℝ] E2 where
  toFun := parityFlip
  map_add' v w := by
    ext i
    fin_cases i <;> simp [parityFlip, Jm, vec2, add_comm]
  map_smul' c v := by
    ext i
    fin_cases i <;> simp [parityFlip, Jm, vec2, smul_neg]
  norm_map' v := by
    simp [PiLp.norm_eq_of_L2, Fin.sum_univ_two, parityFlip, Jm, vec2]

end QuantumNLS.LocalSpectral.Round23
#print axioms QuantumNLS.LocalSpectral.Round23.swapConj_involutive
#print axioms QuantumNLS.LocalSpectral.Round23.parityFlip_involutive
#print axioms QuantumNLS.LocalSpectral.Round23.lopPt_swapConj
#print axioms QuantumNLS.LocalSpectral.Round23.lopPt_parityFlip
#print axioms QuantumNLS.LocalSpectral.Round23.swapConjIsometry
#print axioms QuantumNLS.LocalSpectral.Round23.parityFlipIsometry
