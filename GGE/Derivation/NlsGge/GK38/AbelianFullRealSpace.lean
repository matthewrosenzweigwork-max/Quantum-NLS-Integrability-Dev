import NlsGge.GK38.AbelianRealSequenceSpace

/-! Genuine FULL real lp2 coordinates, inclusion, and standard real Hilbert
basis. The spectral index is all of Z, including zero. -/
set_option autoImplicit false
namespace NlsGge.GK38
noncomputable section

abbrev P6RealSpace38 : Type := lp (fun _ : ℤ => ℝ) 2

def p6RealInclude38 : P6RealSpace38 →L[ℝ] Lib.L2Seq :=
  lp.mapCLM 2 (fun _ : ℤ => Complex.ofRealCLM) zero_le_one
    (fun _ => by rw [Complex.ofRealCLM_norm])

@[simp] theorem p6RealInclude_apply38 (s : P6RealSpace38) (m : ℤ) :
    p6RealInclude38 s m=(s m : ℂ) := rfl

def p6RealPart38 : Lib.L2Seq →L[ℝ] P6RealSpace38 :=
  lp.mapCLM 2 (fun _ : ℤ => Complex.reCLM) zero_le_one
    (fun _ => by rw [Complex.reCLM_norm])

@[simp] theorem p6RealPart_apply38 (s : Lib.L2Seq) (m : ℤ) :
    p6RealPart38 s m=(s m).re := rfl

def p6ImagPart38 : Lib.L2Seq →L[ℝ] P6RealSpace38 :=
  lp.mapCLM 2 (fun _ : ℤ => Complex.imCLM) zero_le_one
    (fun _ => by rw [Complex.imCLM_norm])

@[simp] theorem p6ImagPart_apply38 (s : Lib.L2Seq) (m : ℤ) :
    p6ImagPart38 s m=(s m).im := rfl

@[simp] theorem p6RealPart_include38 (s : P6RealSpace38) :
    p6RealPart38 (p6RealInclude38 s)=s := by
  apply Subtype.ext
  funext m
  exact Complex.ofReal_re (s m)

theorem p6RealInclude_realPart38 (s : Lib.L2Seq) (hs : ∀ m : ℤ, (s m).im=0) :
    p6RealInclude38 (p6RealPart38 s)=s := by
  apply Subtype.ext
  funext m
  change (((s m).re : ℝ) : ℂ)=s m
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im,hs m]

theorem p6RealInclude_single38 (r : ℤ) :
    p6RealInclude38 (lp.single 2 r (1 : ℝ))=lp.single 2 r (1 : ℂ) := by
  apply Subtype.ext
  funext m
  by_cases hm : m=r
  · subst m
    simp only [p6RealInclude_apply38,lp.single_apply_self,Complex.ofReal_one]
  · simp only [p6RealInclude_apply38,
      lp.single_apply_ne (E := fun _ : ℤ => ℝ) 2 r (1 : ℝ) hm,
      lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 r (1 : ℂ) hm,Complex.ofReal_zero]

theorem p6RealPart_I_include38 (x : P6RealSpace38) :
    p6RealPart38 (Complex.I • p6RealInclude38 x)=0 := by
  apply Subtype.ext
  funext m
  change ((Complex.I • p6RealInclude38 x : Lib.L2Seq) m).re=0
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,p6RealInclude_apply38,
    Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero]

@[simp] theorem p6ImagPart_include38 (x : P6RealSpace38) :
    p6ImagPart38 (p6RealInclude38 x)=0 := by
  apply Subtype.ext
  funext m
  exact Complex.ofReal_im (x m)

theorem p6ImagPart_I_include38 (x : P6RealSpace38) :
    p6ImagPart38 (Complex.I • p6RealInclude38 x)=x := by
  apply Subtype.ext
  funext m
  change ((Complex.I • p6RealInclude38 x : Lib.L2Seq) m).im=x m
  simp only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,p6RealInclude_apply38,
    Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,one_mul,zero_add]

theorem p6Complex_coordinates38 (z : Lib.L2Seq) :
    z=p6RealInclude38 (p6RealPart38 z)+Complex.I • p6RealInclude38 (p6ImagPart38 z) := by
  apply Subtype.ext
  funext m
  change z m=(p6RealInclude38 (p6RealPart38 z)+
    Complex.I • p6RealInclude38 (p6ImagPart38 z) : Lib.L2Seq) m
  simp only [lp.coeFn_add,Pi.add_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
    p6RealInclude_apply38,p6RealPart_apply38,p6ImagPart_apply38]
  apply Complex.ext <;> simp

def p6RealHilbertBasis38 : HilbertBasis ℤ ℝ P6RealSpace38 :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ _)

theorem p6RealHilbertBasis_apply38 (r : ℤ) :
    p6RealHilbertBasis38 r=lp.single 2 r (1 : ℝ) := by
  classical
  simpa only [p6RealHilbertBasis38,LinearIsometryEquiv.coe_refl] using!
    p6RealHilbertBasis38.repr_self r

end
end NlsGge.GK38
