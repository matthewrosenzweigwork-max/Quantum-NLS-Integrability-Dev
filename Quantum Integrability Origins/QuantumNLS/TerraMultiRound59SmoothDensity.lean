import QuantumNLS.TerraMultiRound58AbsoluteParity

/-! Smooth trigonometric approximations in the physical Fourier model. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace QuantumNLS.TerraMultiRound59SmoothDensity
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPointwise
open QuantumNLS.RiccatiPointwiseDisc QuantumNLS.ClassicalCharges

def trunc (F : Finset ℤ) (x : Ell2) : Ell2 := ∑ i ∈ F, lp.single 2 i (x i)

theorem trunc_apply (F : Finset ℤ) (x : Ell2) (n : ℤ) : trunc F x n = if n ∈ F then x n else 0 := by
  unfold trunc
  rw [lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]

theorem trunc_tendsto (x : Ell2) : Tendsto (fun F : Finset ℤ => trunc F x) atTop (𝓝 x) :=
  lp.hasSum_single (p := 2) (by simp) x

theorem physRep_trunc_formula (L a : ℝ) (F : Finset ℤ) (x : Ell2) (y : ℝ) :
    physRep L a (trunc F x) y = (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
      ∑ n ∈ F, toField L a (trunc F x) n * ex L n y := by
  unfold physRep series
  congr 1
  apply tsum_eq_sum
  intro n hn
  simp [toField, trunc_apply, hn]

theorem trunc_smooth (L : ℝ) [Fact (0 < L)] (a : ℝ) (F : Finset ℤ) (x : Ell2) :
    SmoothPeriodic L (physRep L a (trunc F x)) := by
  constructor
  · have he : physRep L a (trunc F x) = fun y : ℝ => (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
        ∑ n ∈ F, toField L a (trunc F x) n * ex L n y :=
      funext (physRep_trunc_formula L a F x)
    rw [he]
    refine contDiff_const.mul ?_
    apply ContDiff.sum
    intro n hn
    refine contDiff_const.mul ?_
    unfold ex
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  · intro y
    simp only [physRep, series_add_period (Fact.out : (0 : ℝ) < L).ne']

theorem dense_smooth (L : ℝ) [Fact (0 < L)] (a : ℝ) :
    Dense {x : Ell2 | SmoothPeriodic L (physRep L a x)} := by
  intro x
  apply mem_closure_of_tendsto (trunc_tendsto x)
  exact Filter.Eventually.of_forall (fun F => trunc_smooth L a F x)

#print axioms trunc
#print axioms trunc_apply
#print axioms trunc_tendsto
#print axioms physRep_trunc_formula
#print axioms trunc_smooth
#print axioms dense_smooth
end QuantumNLS.TerraMultiRound59SmoothDensity
