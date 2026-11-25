import NlsGge.GK38.GradEigenDirichlet
import NlsGge.GK38.DirichletTriangularCalc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
open Set Filter Topology MeasureTheory
namespace NlsGge.GK38.GradEigen38
noncomputable section
open NlsGge.Pilot NlsGge.SpectralFoundations

theorem probe_dirichlet_nonreal_simple :
    dirichletChar (constL2 (2*Complex.I),0) Complex.I = 0 ∧
    deriv (dirichletChar (constL2 (2*Complex.I),0)) Complex.I = (Real.sinh 1 : ℂ) ∧
    deriv (dirichletChar (constL2 (2*Complex.I),0)) Complex.I ≠ 0 := by
  have hformula (w : ℂ) (hw : w ≠ 0) :
      dirichletChar (constL2 (2*Complex.I),0) w = (1-Complex.I/w)*Complex.sin w := by
    rw [dirichlet_triangle_nonzero38 _ _ hw]
    congr 1
    field_simp <;> ring
  have hsin : Complex.sin Complex.I = (Real.sinh 1 : ℂ)*Complex.I := by
    simpa using Complex.sin_mul_I (1 : ℂ)
  have hquot := (hasDerivAt_const Complex.I Complex.I).div
    (hasDerivAt_id Complex.I) Complex.I_ne_zero
  have hprod := ((hasDerivAt_const Complex.I (1 : ℂ)).sub hquot).mul
    (Complex.hasDerivAt_sin Complex.I)
  have hg : HasDerivAt (fun w : ℂ => (1-Complex.I/w)*Complex.sin w)
      (Real.sinh 1 : ℂ) Complex.I := by
    convert! hprod using 1 <;> norm_num [hsin,Complex.I_sq] <;> ring_nf <;> simp [Complex.I_sq]
  have hd : HasDerivAt (dirichletChar (constL2 (2*Complex.I),0))
      (Real.sinh 1 : ℂ) Complex.I := by
    apply hg.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds Complex.I_ne_zero] with w hw
    exact hformula w hw
  refine ⟨?_,hd.deriv,?_⟩
  · rw [hformula Complex.I Complex.I_ne_zero]
    simp
  · rw [hd.deriv]
    exact_mod_cast ne_of_gt ((Real.sinh_pos_iff).2 (by norm_num : (0 : ℝ)<1))

theorem probe_dirichlet_nonreal_full :
    Q (state (constL2 (2*Complex.I),0) Complex.I (![1,1] : PairVec38)) ≠ 0 ∧
    dirImplicitGradient (constL2 (2*Complex.I),0) Complex.I =
      bilinearGradient (state (constL2 (2*Complex.I),0) Complex.I (![1,1] : PairVec38)) ∧
    ∃ (U : Set PotPair) (κ : PotPair → ℂ),
      IsOpen U ∧ (constL2 (2*Complex.I),0) ∈ U ∧ AnalyticOnNhd ℂ κ U ∧
      κ (constL2 (2*Complex.I),0) = Complex.I ∧
      (∀ ψ ∈ U, dirichletChar ψ (κ ψ) = 0) ∧
      HasFDerivAt κ
        (bilinearGradient (state (constL2 (2*Complex.I),0) Complex.I (![1,1] : PairVec38)))
        (constL2 (2*Complex.I),0) :=
  complex_dirichlet_simple_target _ _ probe_dirichlet_nonreal_simple.1
    probe_dirichlet_nonreal_simple.2.2

theorem probe_dirichlet_nonreal_pair :
    (constL2 (2*Complex.I),0) ≠ (0 : PotPair) ∧
    ∀ u : PhysicalL2, (constL2 (2*Complex.I),0) ≠ realSlice u := by
  have hc : dirichletChar (constL2 (2*Complex.I),0) 0 ≠ 0 := by
    rw [dirichlet_triangle_zero38]
    norm_num [Complex.ext_iff]
  have hnonfree : (constL2 (2*Complex.I),0) ≠ (0 : PotPair) := by
    intro hz
    apply hc
    rw [hz,dirichletChar_zero]
    simp
  refine ⟨hnonfree,?_⟩
  intro u hu
  have hs := congrArg Prod.snd hu
  change (0 : PhysicalL2) = star u at hs
  have hu0 : u = 0 := by
    apply starLp.injective
    change star u = starLp (0 : PhysicalL2)
    rw [map_zero]
    exact hs.symm
  subst u
  exact hnonfree (by simpa only [realSlice_zero] using hu)

theorem probe_dirichlet_nonreal_phase :
    let w := state (constL2 (2*Complex.I),0) Complex.I (![1,1] : PairVec38)
    Q (Complex.I • w) = -Q w ∧ Q (Complex.I • w) ≠ 0 ∧
      bilinearGradient (Complex.I • w) = bilinearGradient w := by
  dsimp only
  have hQ := probe_dirichlet_nonreal_full.1
  refine ⟨?_,?_,bilinear_gradient_smul _ _ Complex.I_ne_zero hQ⟩
  · simp only [Q_smul,Complex.I_sq,neg_one_mul]
  · simpa only [Q_smul,Complex.I_sq,neg_one_mul,neg_ne_zero] using hQ

end
end NlsGge.GK38.GradEigen38
