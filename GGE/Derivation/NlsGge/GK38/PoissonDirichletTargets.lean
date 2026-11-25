import NlsGge.GK38.GradEigenDirichlet
import NlsGge.GK38.GradEigenRealDirichlet

/-! Prospective K3 Dirichlet mutual commutation; target packet, not proof acceptance. -/
set_option autoImplicit false
open Set Filter Topology MeasureTheory
open NlsGge.GK38 NlsGge.GK38.GradEigen38
namespace NlsGge.GK38.PoissonDirichlet38
noncomputable section

def dirEigenKernel38 (φ : PotPair) (z : ℂ) : PairKernelCont38 :=
  (Q (state φ z ![1,1]))⁻¹ • square (state φ z ![1,1])

def dirEigenWedge38 (φ : PotPair) (z w : ℂ) (s : ℝ) : ℂ :=
  pairKernelExt38 (dirEigenKernel38 φ z) s 0 *
      pairKernelExt38 (dirEigenKernel38 φ w) s 1 -
    pairKernelExt38 (dirEigenKernel38 φ z) s 1 *
      pairKernelExt38 (dirEigenKernel38 φ w) s 0

def dirEigenPoisson38 (φ : PotPair) (z w : ℂ) : ℂ :=
  -Complex.I * ∫ s in (0 : ℝ)..1, dirEigenWedge38 φ z w s

def dirEigenHamField38 (φ : PotPair) (w : ℂ) : PotPair :=
  let g := pairKernelL2Class38 (dirEigenKernel38 φ w)
  (-Complex.I • g.2, Complex.I • g.1)

def DirichletMutualCommuteTarget : Prop :=
  ∀ (φ : PotPair) (z w : ℂ),
    dirichletChar φ z = 0 → dirichletChar φ w = 0 →
    deriv (dirichletChar φ) z ≠ 0 → deriv (dirichletChar φ) w ≠ 0 →
    Q (state φ z ![1,1]) ≠ 0 ∧ Q (state φ w ![1,1]) ≠ 0 ∧
    IntervalIntegrable (dirEigenWedge38 φ z w) volume 0 1 ∧
    dirEigenPoisson38 φ z w = 0 ∧
    dirImplicitGradient φ z (dirEigenHamField38 φ w) = dirEigenPoisson38 φ z w

end
end NlsGge.GK38.PoissonDirichlet38
