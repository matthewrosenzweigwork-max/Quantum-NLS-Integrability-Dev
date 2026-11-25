import NlsGge.GK38.AbelianRealJacobian

/-! Genuine real/imaginary lp2 coordinates for complexifying the actual real
Jacobian inverse. No inverse is assumed in this coordinate module. -/
set_option autoImplicit false
namespace NlsGge.GK38.P4NumeratorVariation
noncomputable section

def imagPart (n : ℤ) : P2Space38 n →L[ℝ] P3RealSpace38 n :=
  lp.mapCLM 2 (fun _ : P2Index38 n => Complex.imCLM) zero_le_one
    (fun _ => by rw [Complex.imCLM_norm])

theorem imagPart_apply (n : ℤ) (z : P2Space38 n) (m : P2Index38 n) :
    imagPart n z m=(z m).im := rfl

theorem realPart_I_include (n : ℤ) (x : P3RealSpace38 n) :
    p3RealPart38 n (Complex.I • p3RealInclude38 n x)=0 := by
  apply Subtype.ext
  funext m
  change ((Complex.I • p3RealInclude38 n x : P2Space38 n) m).re=0
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,p3RealInclude_apply38,
    Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero]

theorem imagPart_include (n : ℤ) (x : P3RealSpace38 n) :
    imagPart n (p3RealInclude38 n x)=0 := by
  apply Subtype.ext
  funext m
  exact Complex.ofReal_im (x m)

theorem imagPart_I_include (n : ℤ) (x : P3RealSpace38 n) :
    imagPart n (Complex.I • p3RealInclude38 n x)=x := by
  apply Subtype.ext
  funext m
  change ((Complex.I • p3RealInclude38 n x : P2Space38 n) m).im=x m
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,p3RealInclude_apply38,
    Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,one_mul,zero_add]

theorem complex_coordinates (n : ℤ) (z : P2Space38 n) :
    z=p3RealInclude38 n (p3RealPart38 n z)+Complex.I • p3RealInclude38 n (imagPart n z) := by
  apply Subtype.ext
  funext m
  change z m=(p3RealInclude38 n (p3RealPart38 n z)+
    Complex.I • p3RealInclude38 n (imagPart n z) : P2Space38 n) m
  simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    p3RealInclude_apply38,p3RealPart_apply38,imagPart_apply]
  apply Complex.ext <;> simp

end
end NlsGge.GK38.P4NumeratorVariation
