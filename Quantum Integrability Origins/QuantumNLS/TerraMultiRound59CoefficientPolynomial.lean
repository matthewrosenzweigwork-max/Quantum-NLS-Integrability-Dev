import QuantumNLS.TerraMultiRound59TreeForm
import QuantumNLS.TerraMultiRound57CollectedPowers

/-! Real polynomial representation of each retained finite tree coefficient. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59CoefficientPolynomial
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound53TreeIndex QuantumNLS.TerraMultiRound55TreeFactors
open QuantumNLS.TerraMultiRound57LevelPowers QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59TreeForm QuantumNLS.TerraMultiRound51TaylorIntegral

variable {L : ℝ} [Fact (0 < L)]

def realTreeForm {k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k) (κ : ℝ) (t : BinaryTree Unit) :
    ContinuousMultilinearMap ℝ (fun _ : Fin ((2 * t.numNodes + 1) + 1) => Ell2) ℝ :=
  ((-κ) ^ t.numNodes) • Complex.reCLM.compContinuousMultilinearMap (treeForm (L := L) hk hd t)

@[simp] theorem realTreeForm_diagonal {k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (κ : ℝ) (t : BinaryTree Unit) (x : Ell2) :
    realTreeForm (L := L) hk hd κ t (fun _ => x) =
      ((-(κ : ℂ)) ^ t.numNodes * integratedCoeff (Cfun (factorField (L := L) k x t))
        (finiteFactorPaths t) d).re := by
  change (-κ) ^ t.numNodes * (treeForm (L := L) hk hd t (fun _ => x)).re = _
  rw [treeForm_diagonal]
  rw [show (-(κ : ℂ)) ^ t.numNodes = (((-κ) ^ t.numNodes : ℝ) : ℂ) by push_cast; rfl]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

def coefficientPolynomial {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) (s n : ℕ) (x : Ell2) : ℝ :=
  ∑ ell ∈ Finset.Ico 1 (s + 1), ∑ d ∈ Finset.range (2 * (s - ell) + 1),
    if 2 * ell + 1 + d = n then
      if hd : d ≤ 2 * k then
        ∑ t ∈ BinaryTree.treesOfNumNodesEq ell, realTreeForm (L := L) hk hd κ t (fun _ => x)
      else 0
    else 0

theorem coefficientPolynomial_eq {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) (s n : ℕ)
    (hn : n ≤ 2 * k + 3) (x : Ell2) :
    coefficientPolynomial (L := L) hk κ s n x =
      (treeCoefficient (L := L) (k := k) κ x s n).re := by
  unfold coefficientPolynomial treeCoefficient
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  have he := Finset.mem_Ico.mp hell
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs with h
  · have hdk : d ≤ 2 * k := by omega
    simp only [hdk, ↓reduceDIte, levelCoeff, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro t ht
    exact realTreeForm_diagonal hk hdk κ t x
  · omega
  · simp only [Complex.zero_re]

theorem coefficientPolynomial_continuous {k : ℕ} (hk : 1 ≤ k) (κ : ℝ) (s n : ℕ) :
    Continuous (coefficientPolynomial (L := L) hk κ s n) := by
  unfold coefficientPolynomial
  apply continuous_finsetSum
  intro ell hell
  apply continuous_finsetSum
  intro d hd
  split_ifs with h hdk
  · apply continuous_finsetSum
    intro t ht
    exact (realTreeForm (L := L) hk hdk κ t).cont.comp (continuous_pi (fun _ => continuous_id))
  · exact continuous_const
  · exact continuous_const

#print axioms realTreeForm
#print axioms realTreeForm_diagonal
#print axioms coefficientPolynomial
#print axioms coefficientPolynomial_eq
#print axioms coefficientPolynomial_continuous
end QuantumNLS.TerraMultiRound59CoefficientPolynomial
