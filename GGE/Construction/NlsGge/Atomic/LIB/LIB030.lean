import NlsGge.Atomic.LIB.LIB028

/-!
# LIB-030: exact annihilators of the four Dirac boundary conditions

Affine functions in the literal distributional H1 graph realize arbitrary endpoint
traces. Testing the Green boundary form on their allowed endpoint values forces
precisely the same separated or Floquet relation on the second argument.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff
namespace NlsGge.Atomic.LIB030
open NlsGge.Schur NlsGge.Atomic.Interval NlsGge.Atomic.LIB026

def affineValue (a b : ℂ) (x : ℝ) : ℂ := a + (x : ℂ) * (b - a)

lemma affineValue_contDiff (a b : ℂ) : ContDiff ℝ ∞ (affineValue a b) :=
  contDiff_const.add (Complex.ofRealCLM.contDiff.mul contDiff_const)

lemma affineValue_deriv (a b : ℂ) : deriv (affineValue a b) = fun _ => b - a := by
  funext x
  have h := (((hasDerivAt_id x).ofReal_comp).mul_const (b - a)).const_add a
  have hd : HasDerivAt (affineValue a b) (b - a) x := by
    simpa only [affineValue, id_eq, Complex.ofReal_one, one_mul] using! h
  exact hd.deriv

lemma affineValue_memLp (a b : ℂ) :
    MemLp (affineValue a b) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound (affineValue_contDiff a b).continuous.aestronglyMeasurable
    (‖a‖ + ‖b - a‖)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  change ‖a + (x : ℂ) * (b - a)‖ ≤ _
  calc
    _ ≤ ‖a‖ + ‖(x : ℂ) * (b - a)‖ := norm_add_le _ _
    _ = ‖a‖ + x * ‖b - a‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.1.le]
    _ ≤ ‖a‖ + ‖b - a‖ := by
      apply add_le_add (le_refl _)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hx.2 (norm_nonneg (b - a))

lemma affineDeriv_memLp (a b : ℂ) :
    MemLp (deriv (affineValue a b)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  rw [affineValue_deriv]
  exact memLp_const _

/-- Actual affine interpolation in the distributional H1 graph. -/
def affineH1 (a b : ℂ) : H1 where
  value := (affineValue_memLp a b).toLp (affineValue a b)
  derivative := (affineDeriv_memLp a b).toLp (deriv (affineValue a b))
  weak := by
    intro ψ hψs hψc hψU
    have h := NlsGge.Atomic.LIB028.smooth_hasWeakDerivative
      (affineValue a b) (affineValue_contDiff a b) ψ hψs hψc hψU
    have hv : (∫ x in (0 : ℝ)..1,
        ((affineValue_memLp a b).toLp (affineValue a b)) x * ((deriv ψ x : ℝ) : ℂ)) =
        ∫ x in (0 : ℝ)..1, affineValue a b x * ((deriv ψ x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr_ae_restrict
      simp only [uIoc_of_le zero_le_one]
      filter_upwards [(affineValue_memLp a b).coeFn_toLp] with x hx
      rw [hx]
    have hd : (∫ x in (0 : ℝ)..1,
        ((affineDeriv_memLp a b).toLp (deriv (affineValue a b))) x * (ψ x : ℂ)) =
        ∫ x in (0 : ℝ)..1, deriv (affineValue a b) x * (ψ x : ℂ) := by
      apply intervalIntegral.integral_congr_ae_restrict
      simp only [uIoc_of_le zero_le_one]
      filter_upwards [(affineDeriv_memLp a b).coeFn_toLp] with x hx
      rw [hx]
    rw [hv, hd]
    exact h

lemma affineH1_representative (a b : ℂ) (x : Icc (0 : ℝ) 1) :
    representative (affineH1 a b) x = affineValue a b x := by
  let F : C(Icc (0 : ℝ) 1, ℂ) :=
    ⟨fun x => affineValue a b x, (affineValue_contDiff a b).continuous.comp continuous_subtype_val⟩
  have heq : F = representative (affineH1 a b) := by
    apply representative_eq_of_ae
    filter_upwards [(affineValue_memLp a b).coeFn_toLp,
      ae_restrict_mem measurableSet_Ioc] with y hy hmem
    rw [IccExtend_of_mem zero_le_one F ⟨hmem.1.le, hmem.2⟩]
    exact hy.symm
  exact congrArg (fun f : C(Icc (0 : ℝ) 1, ℂ) => f x) heq.symm

@[simp] lemma affineH1_traceLeft (a b : ℂ) : traceLeft (affineH1 a b) = a := by
  rw [traceLeft, affineH1_representative]
  simp [affineValue]

@[simp] lemma affineH1_traceRight (a b : ℂ) : traceRight (affineH1 a b) = b := by
  rw [traceRight, affineH1_representative]
  simp [affineValue]

/-- Every prescribed pair of endpoint vectors is realized by an actual H1 pair. -/
theorem exists_H1Pair_traces (a b : Bool → ℂ) :
    ∃ f : H1Pair, (∀ c, traceLeft (f c) = a c) ∧ (∀ c, traceRight (f c) = b c) := by
  exact ⟨fun c => affineH1 (a c) (b c), fun c => affineH1_traceLeft _ _,
    fun c => affineH1_traceRight _ _⟩

lemma zsBoundaryForm_eq_zero_iff (f g : H1Pair) :
    zsBoundaryForm f g = 0 ↔
      (star (traceRight (f true)) * traceRight (g true) -
        star (traceRight (f false)) * traceRight (g false)) -
      (star (traceLeft (f true)) * traceLeft (g true) -
        star (traceLeft (f false)) * traceLeft (g false)) = 0 := by
  simp only [zsBoundaryForm, mul_eq_zero, neg_eq_zero, Complex.I_ne_zero, false_or]

/-- The boundary annihilator of each literal source domain is exactly the same domain.
The boundary form is independent of the potential; no real-type hypothesis is needed here. -/
theorem zs_adjoint_boundary_iff (bc : ZSBoundaryCondition) (g : H1Pair) :
    (∀ f : H1Pair, HasZSBoundaryCondition bc f → zsBoundaryForm f g = 0) ↔
      HasZSBoundaryCondition bc g := by
  constructor
  · intro h
    have htest (a b : Bool → ℂ)
        (hbc : HasZSBoundaryCondition bc (fun c => affineH1 (a c) (b c))) :
        (star (b true) * traceRight (g true) - star (b false) * traceRight (g false)) -
          (star (a true) * traceLeft (g true) - star (a false) * traceLeft (g false)) = 0 := by
      have he := (zsBoundaryForm_eq_zero_iff _ _).mp
        (h (fun c => affineH1 (a c) (b c)) hbc)
      simpa only [affineH1_traceLeft, affineH1_traceRight] using he
    cases bc with
    | dirichlet =>
      have hL := htest (fun _ => 1) (fun _ => 0) (by simp [HasZSBoundaryCondition])
      have hR := htest (fun _ => 0) (fun _ => 1) (by simp [HasZSBoundaryCondition])
      simp at hL hR
      constructor
      · linear_combination -hL
      · linear_combination hR
    | neumann =>
      have hL := htest (fun c => if c then 1 else -1) (fun _ => 0)
        (by simp [HasZSBoundaryCondition])
      have hR := htest (fun _ => 0) (fun c => if c then 1 else -1)
        (by simp [HasZSBoundaryCondition])
      simp at hL hR
      constructor
      · linear_combination -hL
      · linear_combination hR
    | periodic =>
      intro b
      have he := htest (fun c => if c = b then 1 else 0)
        (fun c => if c = b then 1 else 0) (by simp [HasZSBoundaryCondition])
      cases b with
      | false =>
        simp at he
        linear_combination -he
      | true =>
        simp at he
        linear_combination he
    | antiperiodic =>
      intro b
      have he := htest (fun c => if c = b then 1 else 0)
        (fun c => -(if c = b then 1 else 0)) (by simp [HasZSBoundaryCondition])
      cases b with
      | false =>
        simp at he
        linear_combination he
      | true =>
        simp at he
        linear_combination -he
  · intro hg f hf
    exact NlsGge.Atomic.LIB028.zs_boundaryForm_eq_zero bc f g hf hg

end NlsGge.Atomic.LIB030
