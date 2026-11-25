import QuantumNLS.TerraMultiRound18FieldConformal
import QuantumNLS.TerraMultiRound18Variational

/-! Pullback identities for the D01 flow, conditional on the named GP-04
short-time compact-uniform analytic-dependence remainder. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
attribute [local instance] InnerProductSpace.complexToReal
open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef
open QuantumNLS.TerraMultiRound18Flow QuantumNLS.TerraMultiRound18AnalyticFlow
open QuantumNLS.TerraMultiRound18Variational QuantumNLS.TerraMultiRound18FieldConformal
namespace QuantumNLS.TerraMultiRound18Pullbacks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem one_form_infinitesimal (S : Hyp H) (u h : H) :
    fderiv ℝ S.abar u (S.Y u) h + S.abar u (fderiv ℝ S.Y u h) = S.abar u h := by
  have hY := (QuantumNLS.TerraMultiRound17D01Repair.analytic_field_and_local_solutions S).1 u
  have hA := analyticAt_of_isRealAnalyticPoly (S.abar_analytic u)
  have hd := hA.differentiableAt.hasFDerivAt.clm_apply hY.differentiableAt.hasFDerivAt
  have he : (fun x => S.abar x (S.Y x)) = (fun _ => (0 : ℝ)) := by
    funext x
    exact (QuantumNLS.TerraMultiRound15D01Partial.action_derivative_and_self_contraction S).2.1 x
  have hz := (he ▸ hd).unique (hasFDerivAt_const (c := (0 : ℝ)) u)
  have hz' := congrArg (fun L : H →L[ℝ] ℝ => L h) hz
  have hz'' : fderiv ℝ S.abar u h (S.Y u) + S.abar u (fderiv ℝ S.Y u h) = 0 := by
    simpa [add_comm] using hz'
  have hdA := S.abar_d u (S.Y u) h
  have hw : omega (S.Y u) h = S.abar u h := by rw [Hyp.Y, omega_Winv]
  rw [hw] at hdA
  linarith

private theorem exp_integrate {g : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g t) t) (t : ℝ) :
    g t = Real.exp t * g 0 := by
  have hd : ∀ s, HasDerivAt (fun s => Real.exp (-s) * g s) 0 s := by
    intro s
    have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-s)) s := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (-s)).scomp s (hasDerivAt_neg s)
    have hh := he.mul (hg s)
    convert hh using 1
    ring
  have heq := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  have hmul : Real.exp (-t) * g t = g 0 := by simpa using heq
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc
    g t = (Real.exp t * Real.exp (-t)) * g t := by rw [he, one_mul]
    _ = Real.exp t * g 0 := by rw [mul_assoc, hmul]

theorem conformal_symplectic (S : Hyp H) (ha : GP04CompactLocalAnalyticity S)
    (t : ℝ) (u h k : H) :
    omega (fderiv ℝ (flow S t) u h) (fderiv ℝ (flow S t) u k) = Real.exp t * omega h k := by
  obtain ⟨J, hJ, -⟩ := QuantumNLS.Ext025A.gp06_strong_symplectic_identification (E := H)
  have hom : ∀ v w, omega v w = J v w := fun v w => (hJ v w).symm
  let g := fun s => J (fderiv ℝ (flow S s) u h) (fderiv ℝ (flow S s) u k)
  have hg : ∀ s, HasDerivAt g (g s) s := by
    intro s
    have hh := variational_apply S ha u h s
    have hk := variational_apply S ha u k s
    have hJd := (J : H →L[ℝ] (H →L[ℝ] ℝ)).hasFDerivAt.comp_hasDerivAt s hh
    have hd := hJd.clm_apply hk
    have he : J (fderiv ℝ S.Y (flow S s u) (fderiv ℝ (flow S s) u h))
          (fderiv ℝ (flow S s) u k) +
        J (fderiv ℝ (flow S s) u h)
          (fderiv ℝ S.Y (flow S s u) (fderiv ℝ (flow S s) u k)) = g s := by
      dsimp [g]
      rw [← hom, ← hom, ← hom]
      exact infinitesimal_conformal S _ _ _
    rw [← he]
    exact hd
  have hzero : flow S 0 = id := funext fun x => (flow_spec S x).1
  have hresult := exp_integrate hg t
  simpa [g, ← hom, hzero] using hresult

theorem one_form_pullback (S : Hyp H) (ha : GP04CompactLocalAnalyticity S)
    (t : ℝ) (u h : H) :
    S.abar (flow S t u) (fderiv ℝ (flow S t) u h) = Real.exp t * S.abar u h := by
  let g := fun s => S.abar (flow S s u) (fderiv ℝ (flow S s) u h)
  have hg : ∀ s, HasDerivAt g (g s) s := by
    intro s
    have hA := (analyticAt_of_isRealAnalyticPoly (S.abar_analytic (flow S s u))).differentiableAt.hasFDerivAt
    have hAd := hA.comp_hasDerivAt s ((flow_spec S u).2 s)
    have hd := hAd.clm_apply (variational_apply S ha u h s)
    have he := one_form_infinitesimal S (flow S s u) (fderiv ℝ (flow S s) u h)
    dsimp [g]
    rw [← he]
    convert hd using 1
    all_goals rfl
  have hzero : flow S 0 = id := funext fun x => (flow_spec S x).1
  have hresult := exp_integrate hg t
  simpa [g, hzero] using hresult

#print axioms conformal_symplectic
#print axioms one_form_pullback
end QuantumNLS.TerraMultiRound18Pullbacks
