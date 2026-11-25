import QuantumNLS.TerraMultiRound59ContinuousForm
import QuantumNLS.TerraMultiRound59PhysicalLinear
import QuantumNLS.TerraMultiRound55TreeFactors

/-! Diagonal real multilinear forms for the physical tree correlations. -/
set_option autoImplicit false
noncomputable section
open ComplexConjugate
namespace QuantumNLS.TerraMultiRound59TreeForm
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.TranslatedCorrelation
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.TerraMultiRound59PhysicalLinear
open QuantumNLS.TerraMultiRound55TreeFactors QuantumNLS.TerraMultiRound53TreeIndex
open QuantumNLS.TerraMultiRound59ContinuousForm QuantumNLS.TerraMultiRound51TaylorIntegral

variable {L : ℝ} [Fact (0 < L)]

def conjugateReal : Ell2 →L[ℝ] Ell2 :=
  LinearMap.mkContinuous
    { toFun := jEll
      map_add' := fun x y => by ext n; simp
      map_smul' := fun c x => by ext n; simp }
    1 (fun x => by simp [norm_jEll])

@[simp] theorem conjugateReal_apply (x : Ell2) : conjugateReal x = jEll x := rfl

def factorCLM (k : ℕ) (t : BinaryTree Unit) (i : Fin ((2 * t.numNodes + 1) + 1)) :
    Ell2 →L[ℝ] Hk L k :=
  match finSuccEquiv (2 * t.numNodes + 1) i with
  | none => (physicalCLM (L := L) k).restrictScalars ℝ ∘L conjugateReal
  | some j => if internalAt t (indexedVertex t j) then
      (physicalCLM (L := L) k).restrictScalars ℝ ∘L conjugateReal
    else (physicalCLM (L := L) k).restrictScalars ℝ

@[simp] theorem factorCLM_apply (k : ℕ) (t : BinaryTree Unit)
    (i : Fin ((2 * t.numNodes + 1) + 1)) (x : Ell2) :
    factorCLM (L := L) k t i x = factorField (L := L) k x t i := by
  cases h : finSuccEquiv (2 * t.numNodes + 1) i with
  | none => simp [factorCLM, factorField, h, physicalCLM_apply, conjugateReal_apply]
  | some j =>
    by_cases hj : internalAt t (indexedVertex t j) = true <;>
      simp [factorCLM, factorField, vertexField, h, hj, physicalCLM_apply, conjugateReal_apply]

def treeForm {k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k) (t : BinaryTree Unit) :
    ContinuousMultilinearMap ℝ (fun _ : Fin ((2 * t.numNodes + 1) + 1) => Ell2) ℂ :=
  ((continuousIntegratedForm (L := L) (m := 2 * t.numNodes) hk hd (finiteFactorPaths t)).restrictScalars ℝ).compContinuousLinearMap
    (factorCLM k t)

@[simp] theorem treeForm_diagonal {k d : ℕ} (hk : 1 ≤ k) (hd : d ≤ 2 * k)
    (t : BinaryTree Unit) (x : Ell2) :
    treeForm (L := L) hk hd t (fun _ => x) =
      integratedCoeff (Cfun (factorField (L := L) k x t)) (finiteFactorPaths t) d := by
  simp [treeForm]

#print axioms conjugateReal
#print axioms conjugateReal_apply
#print axioms factorCLM
#print axioms factorCLM_apply
#print axioms treeForm
#print axioms treeForm_diagonal
end QuantumNLS.TerraMultiRound59TreeForm
