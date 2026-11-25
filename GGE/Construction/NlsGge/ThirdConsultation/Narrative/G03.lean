import Mathlib
import NlsGge.Birkhoff.F01Determinant38d
import NlsGge.ThirdConsultation.PDE.OneSmoothing

   
                                                                       
                                                                  
                                                                             
                                                                            
                                                                              
                                                                                
  

set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace
open NlsGge.Pilot NlsGge.Birkhoff NlsGge.Sobolev38

namespace NlsGge.ThirdConsultation.Narrative

/-- The existing weighted real basis, at any genuine completed Sobolev exponent. -/
def g03Basis (r : ℝ) : HilbertBasis (ℤ × Fin 2) ℝ (SobolevCarrier38 r) :=
  weightedRealHilbertBasis (sobolevModeWeight r)

theorem g03Basis_coe (r : ℝ) (p : ℤ × Fin 2) (n : ℤ) :
    carrierCoe38 r (g03Basis r p) n =
      (if n = p.1 then Complex.orthonormalBasisOneI p.2 else 0) /
        (Real.sqrt (sobolevModeWeight r n) : ℂ) := by
  have e : g03Basis r p = weightedRealBasisVector (sobolevModeWeight r) p :=
    weightedRealHilbertBasis_apply _ p
  rw [e]
  exact weightedRealBasisVector_apply _ p n

theorem g03Coe_smul (r c : ℝ) (x : SobolevCarrier38 r) (n : ℤ) :
    carrierCoe38 r (c • x) n = (c : ℂ) * carrierCoe38 r x n := rfl

theorem g03Basis_inner (r : ℝ) (p : ℤ × Fin 2) (x : SobolevCarrier38 r) :
    inner ℝ (g03Basis r p) x = Real.sqrt (sobolevModeWeight r p.1) *
      inner ℝ (Complex.orthonormalBasisOneI p.2) (carrierCoe38 r x p.1) := by
  have e : g03Basis r p = weightedRealBasisVector (sobolevModeWeight r) p :=
    weightedRealHilbertBasis_apply _ p
  have h := weightedRealBasisVector_inner (sobolevModeWeight r) p x
  rw [e]
  refine h.trans ?_
  change inner ℝ (Complex.orthonormalBasisOneI p.2)
      ((Real.sqrt (sobolevModeWeight r p.1) : ℂ) * carrierCoe38 r x p.1) = _
  have hm : Real.sqrt (sobolevModeWeight r p.1) • carrierCoe38 r x p.1 =
      (Real.sqrt (sobolevModeWeight r p.1) : ℂ) * carrierCoe38 r x p.1 :=
    RCLike.real_smul_eq_coe_mul _ _
  rw [← hm, real_inner_smul_right]

theorem g03Weight_neg (r : ℝ) (n : ℤ) :
    sobolevModeWeight (-r) n = (sobolevModeWeight r n)⁻¹ := by
  unfold sobolevModeWeight
  simp only [Real.rpow_eq_pow]
  rw [show (2 : ℝ) * -r = -(2 * r) by ring]
  exact Real.rpow_neg (japaneseBracket_pos n).le (2 * r)

theorem g03SqrtWeight_neg (r : ℝ) (n : ℤ) :
    Real.sqrt (sobolevModeWeight (-r) n) =
      (Real.sqrt (sobolevModeWeight r n))⁻¹ := by
  rw [g03Weight_neg, Real.sqrt_inv]

/-- The coordinate identity inclusion has the expected diagonal action on normalized modes. -/
theorem g03Incl_basis {r s : ℝ} (hrs : r ≤ s) (p : ℤ × Fin 2) :
    carrierIncl38 hrs (g03Basis s p) =
      (Real.sqrt (sobolevModeWeight r p.1) /
        Real.sqrt (sobolevModeWeight s p.1)) • g03Basis r p := by
  classical
  apply carrierExt38
  funext n
  rw [carrierCoe38_incl38, g03Coe_smul, g03Basis_coe, g03Basis_coe]
  by_cases hn : n = p.1
  · subst n
    have hr0 : (Real.sqrt (sobolevModeWeight r p.1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (sobolevModeWeight_pos r p.1)).ne'
    have hs0 : (Real.sqrt (sobolevModeWeight s p.1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr (sobolevModeWeight_pos s p.1)).ne'
    simp only [ite_true, Complex.ofReal_div]
    field_simp [hr0, hs0] <;> ring
  · simp only [ite_eq_right hn, zero_div, mul_zero]

/-- The explicit square-root-weight change of coordinates, using the SAME real mode index. -/
def g03ScaleEquiv (r s : ℝ) : SobolevCarrier38 r ≃ₗᵢ[ℝ] SobolevCarrier38 s :=
  (g03Basis r).repr.trans (g03Basis s).repr.symm

def g03ScaleCLM (r s : ℝ) : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 s :=
  (g03ScaleEquiv r s).toContinuousLinearEquiv.toContinuousLinearMap

theorem g03Scale_repr (r s : ℝ) (x : SobolevCarrier38 r) :
    (g03Basis s).repr (g03ScaleCLM r s x) = (g03Basis r).repr x := by
  change (g03Basis s).repr ((g03Basis s).repr.symm ((g03Basis r).repr x)) = _
  exact (g03Basis s).repr.apply_symm_apply _

theorem g03Scale_inner (r s : ℝ) (p : ℤ × Fin 2) (x : SobolevCarrier38 r) :
    inner ℝ (g03Basis s p) (g03ScaleCLM r s x) = inner ℝ (g03Basis r p) x := by
  have h := congrArg (fun y : lp (fun _ : ℤ × Fin 2 => ℝ) 2 => y p)
    (g03Scale_repr r s x)
  simpa only [HilbertBasis.repr_apply_apply] using h

theorem g03Scale_cancel (r s : ℝ) (x : SobolevCarrier38 s) :
    g03ScaleCLM r s (g03ScaleCLM s r x) = x := by
  apply (g03Basis s).repr.injective
  rw [g03Scale_repr, g03Scale_repr]

theorem g03Scale_norm (r s : ℝ) (x : SobolevCarrier38 r) :
    ‖g03ScaleCLM r s x‖ = ‖x‖ := (g03ScaleEquiv r s).norm_map x

/-- The negative-to-positive Riesz identification agrees with the adjoint of the
ordinary source inclusion on the entire original h0 carrier. -/
theorem g03Scale_incl_adjoint (r : ℝ) (hr : 0 ≤ r) (x : H0_38) :
    g03ScaleCLM (-r) r
      (carrierIncl38 (r := -r) (s := ((0 : ℕ) : ℝ))
        (by simpa only [Nat.cast_zero] using neg_nonpos.mpr hr) x) =
      ContinuousLinearMap.adjoint
        (carrierIncl38 (r := ((0 : ℕ) : ℝ)) (s := r)
          (by simpa only [Nat.cast_zero] using hr)) x := by
  have hr' : ((0 : ℕ) : ℝ) ≤ r := by simpa only [Nat.cast_zero] using hr
  apply (g03Basis r).repr.injective
  apply lp.ext
  funext p
  simp only [HilbertBasis.repr_apply_apply]
  rw [g03Scale_inner, ContinuousLinearMap.adjoint_inner_right]
  rw [g03Basis_inner, carrierCoe38_incl38, g03Incl_basis hr',
    real_inner_smul_left, g03Basis_inner]
  simp only [g03SqrtWeight_neg, sobolevModeWeight_natCast_zero, Real.sqrt_one,
    one_div, one_mul]

/-- Dualize a real bounded operator between actual positive Sobolev completions.
The same formula is defined at all exponents; the extension theorem uses 1 and 2. -/
def g03Dualize (r s : ℝ) (E : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 s) :
    SobolevCarrier38 (-s) →L[ℝ] SobolevCarrier38 (-r) :=
  (g03ScaleCLM r (-r)).comp
    ((ContinuousLinearMap.adjoint E).comp (g03ScaleCLM (-s) s))

theorem continuous_g03Dualize (r s : ℝ) : Continuous (g03Dualize r s) := by
  unfold g03Dualize
  have hadj : Continuous (fun E : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 s =>
      ContinuousLinearMap.adjoint E) := ContinuousLinearMap.adjoint.continuous
  have hright : Continuous (fun E : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 s =>
      (ContinuousLinearMap.adjoint E).comp (g03ScaleCLM (-s) s)) :=
    (((ContinuousLinearMap.compL ℝ (SobolevCarrier38 (-s)) (SobolevCarrier38 s)
      (SobolevCarrier38 r)).flip (g03ScaleCLM (-s) s)).continuous).comp hadj
  exact ((ContinuousLinearMap.compL ℝ (SobolevCarrier38 (-s)) (SobolevCarrier38 r)
    (SobolevCarrier38 (-r)) (g03ScaleCLM r (-r))).continuous).comp hright

theorem g03Dualize_norm_le (r s : ℝ)
    (E : SobolevCarrier38 r →L[ℝ] SobolevCarrier38 s) :
    ‖g03Dualize r s E‖ ≤ ‖E‖ := by
  refine ContinuousLinearMap.opNorm_le_bound (g03Dualize r s E) (norm_nonneg E) ?_
  intro x
  simp only [g03Dualize, ContinuousLinearMap.comp_apply, g03Scale_norm]
  have h := (ContinuousLinearMap.adjoint E).le_opNorm (g03ScaleCLM (-s) s x)
  rwa [ContinuousLinearMap.adjoint.norm_map, g03Scale_norm] at h

/-- No smoothing assumption is smuggled into the conclusion: the single input
is the positive-scale adjoint endpoint that v2 has already proved. -/
theorem g03Dualize_compatible (A : H0_38 →L[ℝ] H0_38) (E : H1_38 →L[ℝ] H2_38)
    (hE : ∀ h : H1_38, ContinuousLinearMap.adjoint A (i10_38 h) = i20_38 (E h))
    (h : H0_38) :
    g03Dualize ((1 : ℕ) : ℝ) (((1 + 1 : ℕ)) : ℝ) E (carrierIncl38 (by norm_num : (-(((1 + 1 : ℕ)) : ℝ)) ≤ ((0 : ℕ) : ℝ)) h) =
      carrierIncl38 (by norm_num : (-((1 : ℕ) : ℝ)) ≤ ((0 : ℕ) : ℝ)) (A h) := by
  have heq : (ContinuousLinearMap.adjoint A).comp i10_38 = i20_38.comp E := by
    apply ContinuousLinearMap.ext
    exact hE
  have hd := congrArg
    (fun T : H1_38 →L[ℝ] H0_38 => ContinuousLinearMap.adjoint T) heq
  simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] at hd
  have hpoint : ContinuousLinearMap.adjoint E (ContinuousLinearMap.adjoint i20_38 h) =
      ContinuousLinearMap.adjoint i10_38 (A h) :=
    congrArg (fun T : H0_38 →L[ℝ] H1_38 => T h) hd.symm
  apply (g03ScaleEquiv (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ)).injective
  change g03ScaleCLM (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ)
      (g03Dualize ((1 : ℕ) : ℝ) (((1 + 1 : ℕ)) : ℝ) E (carrierIncl38 (by norm_num : (-(((1 + 1 : ℕ)) : ℝ)) ≤ ((0 : ℕ) : ℝ)) h)) =
    g03ScaleCLM (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ)
      (carrierIncl38 (by norm_num : (-((1 : ℕ) : ℝ)) ≤ ((0 : ℕ) : ℝ)) (A h))
  rw [g03Dualize, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    g03Scale_cancel]
  rw [g03Scale_incl_adjoint (((1 + 1 : ℕ)) : ℝ) (by norm_num), g03Scale_incl_adjoint ((1 : ℕ) : ℝ) (by norm_num)]
  exact hpoint

/-- The exact reusable missing duality head from REPORT01, now with a candidate proof. -/
theorem f01_real_scale_duality :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : H0_38 →L[ℝ] H0_38) (E : H1_38 →L[ℝ] H2_38),
        (∀ h : H1_38,
          ContinuousLinearMap.adjoint A (i10_38 h) = i20_38 (E h)) →
        ∃ D : SobolevCarrier38 (-(((1 + 1 : ℕ)) : ℝ)) →L[ℝ] SobolevCarrier38 (-((1 : ℕ) : ℝ)),
          (∀ h : H0_38,
            D (carrierIncl38 (by norm_num : (-(((1 + 1 : ℕ)) : ℝ)) ≤ ((0 : ℕ) : ℝ)) h) =
              carrierIncl38 (by norm_num : (-((1 : ℕ) : ℝ)) ≤ ((0 : ℕ) : ℝ)) (A h)) ∧
          ‖D‖ ≤ C * ‖E‖ := by
  refine ⟨1, one_pos, ?_⟩
  intro A E hE
  refine ⟨g03Dualize ((1 : ℕ) : ℝ) (((1 + 1 : ℕ)) : ℝ) E, g03Dualize_compatible A E hE, ?_⟩
  simpa only [one_mul] using g03Dualize_norm_le ((1 : ℕ) : ℝ) (((1 + 1 : ℕ)) : ℝ) E

/-- The negative-scale extension of the SAME actual Bop in v2. -/
def g03ActualDualExtension (x : H1_38) :
    SobolevCarrier38 (-(((1 + 1 : ℕ)) : ℝ)) →L[ℝ] SobolevCarrier38 (-((1 : ℕ) : ℝ)) :=
  g03Dualize ((1 : ℕ) : ℝ) (((1 + 1 : ℕ)) : ℝ)
    (PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 x)

theorem continuous_g03ActualDualExtension : Continuous g03ActualDualExtension :=
  (continuous_g03Dualize ((1 : ℕ) : ℝ) (((1 + 1 : ℕ)) : ℝ)).comp
    (PDE.actualBirkhoffInput38.continuous_Dadj PDE.actualOneSmoothingInput38)

/-- Compatibility holds on all of the original h0 domain, hence on every smooth sequence. -/
theorem g03ActualDualExtension_compatible (x : H1_38) (h : H0_38) :
    g03ActualDualExtension x
        (carrierIncl38 (by norm_num : (-(((1 + 1 : ℕ)) : ℝ)) ≤ ((0 : ℕ) : ℝ)) h) =
      carrierIncl38 (by norm_num : (-((1 : ℕ) : ℝ)) ≤ ((0 : ℕ) : ℝ))
        (PDE.actualBirkhoffInput38.Bop (i10_38 x) h) :=
  g03Dualize_compatible (PDE.actualBirkhoffInput38.Bop (i10_38 x))
    (PDE.actualBirkhoffInput38.Dadj PDE.actualOneSmoothingInput38 x)
    (PDE.actualBirkhoffInput38.Bop_adjoint_incl PDE.actualOneSmoothingInput38 x) h

/-- G03's literal dual-extension head, with the genuine inclusions fully specified. -/
theorem grouped_f01_dual_extension :
    ∃ D : H1_38 →
        (SobolevCarrier38 (-(((1 + 1 : ℕ)) : ℝ)) →L[ℝ] SobolevCarrier38 (-((1 : ℕ) : ℝ))),
      Continuous D ∧ ∀ (x h : H1_38),
        D x (carrierIncl38 (by norm_num : (-(((1 + 1 : ℕ)) : ℝ)) ≤ ((1 : ℕ) : ℝ)) h) =
          carrierIncl38 (by norm_num : (-((1 : ℕ) : ℝ)) ≤ ((0 : ℕ) : ℝ))
            (PDE.actualBirkhoffInput38.Bop (i10_38 x) (i10_38 h)) := by
  refine ⟨g03ActualDualExtension, continuous_g03ActualDualExtension, ?_⟩
  intro x h
  have hc := g03ActualDualExtension_compatible x (i10_38 h)
  have hi : carrierIncl38 (by norm_num : (-(((1 + 1 : ℕ)) : ℝ)) ≤ ((0 : ℕ) : ℝ)) (i10_38 h) =
      carrierIncl38 (by norm_num : (-(((1 + 1 : ℕ)) : ℝ)) ≤ ((1 : ℕ) : ℝ)) h := by
    apply carrierExt38
    rw [carrierCoe38_incl38, coe_i10_38', carrierCoe38_incl38]
  rw [hi] at hc
  exact hc

end NlsGge.ThirdConsultation.Narrative
