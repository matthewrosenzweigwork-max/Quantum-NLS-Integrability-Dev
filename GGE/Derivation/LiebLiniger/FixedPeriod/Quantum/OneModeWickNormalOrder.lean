import LiebLiniger.FixedPeriod.Quantum.WickContractionPairing
import LiebLiniger.FixedPeriod.Quantum.MixedTensor
import Mathlib.Analysis.InnerProductSpace.Adjoint
import LiebLiniger.FixedPeriod.Quantum.WickWirtinger
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.NoncommRing

/-! Source-only Q2-023 coalesced proposal. Original command blocks are copied
verbatim under separate section scopes; no compilation or acceptance claimed. -/

-- Original LiebLiniger.FixedPeriod.Quantum.WickCoherentSector; body SHA256 939542dc7b3d797d9a163b05f4bbdd308d44b04e0c9fb20061879b3f3dbe797f
section LLFPQ2023OriginalFile01

/-! Exact coherent-power matrix elements of the actual source sector Wick map.
These test the independently constructed operator on physical symmetric sectors;
no normal-ordering or polynomial-model transport is assumed. -/
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Every bounded source kernel has the literal coherent-power matrix element,
with all spectator factors retained in their physical tensor realization. -/
theorem unscaledWickAdded_pairing {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (k : ℕ) (v u : Lp ℂ 2 μ) :
    inner ℂ (pureSymmetricTensor μ (q + k) v)
      (unscaledWickAdded μ A k (pureSymmetricTensor μ (p + k) u)) =
      wickKernelPolarized μ A v u * inner ℂ v u ^ k := by
  change inner ℂ (pureTensorL2 (ι := Fin (q + k)) μ v)
    (symmetrizeL2 μ
      (fullTensorLift μ (fullSectorExtension μ A) k
        (pureTensorL2 (ι := Fin (p + k)) μ u))) = _
  have hsplit (a b : ℕ) (w : Lp ℂ 2 μ) :
      pureTensorL2 (ι := Fin (a + b)) μ w =
        unregroupL2 μ a b (separatedL2 (sectorMeasure μ a) (sectorMeasure μ b)
          (pureTensorL2 (ι := Fin a) μ w) (pureTensorL2 (ι := Fin b) μ w)) := by
    apply (regroupL2 μ a b).injective
    rw [regroupL2_pureTensorL2, regroupL2_unregroupL2]
  have habsorb : inner ℂ (pureTensorL2 (ι := Fin (q + k)) μ v)
      (symmetrizeL2 μ
        (fullTensorLift μ (fullSectorExtension μ A) k
          (pureTensorL2 (ι := Fin (p + k)) μ u))) =
      inner ℂ (pureTensorL2 (ι := Fin (q + k)) μ v)
        (fullTensorLift μ (fullSectorExtension μ A) k
          (pureTensorL2 (ι := Fin (p + k)) μ u)) := by
    have hs := symmetrizeL2_isSymmetric (ι := Fin (q + k)) μ
      (pureTensorL2 (ι := Fin (q + k)) μ v)
      (fullTensorLift μ (fullSectorExtension μ A) k
        (pureTensorL2 (ι := Fin (p + k)) μ u))
    change inner ℂ (symmetrizeL2 μ (pureTensorL2 (ι := Fin (q + k)) μ v))
        (fullTensorLift μ (fullSectorExtension μ A) k (pureTensorL2 (ι := Fin (p + k)) μ u)) =
      inner ℂ (pureTensorL2 (ι := Fin (q + k)) μ v)
        (symmetrizeL2 μ (fullTensorLift μ (fullSectorExtension μ A) k
          (pureTensorL2 (ι := Fin (p + k)) μ u))) at hs
    rw [symmetrizeL2_pureTensorL2] at hs
    exact hs.symm
  rw [habsorb, hsplit p k u]
  have hA := fullSectorExtension_tensor_symmetric μ A k
    (pureSymmetricTensor μ p u) (pureTensorL2 (ι := Fin k) μ u)
  change fullTensorLift μ (fullSectorExtension μ A) k
      (unregroupL2 μ p k (separatedL2 (sectorMeasure μ p) (sectorMeasure μ k)
        (pureTensorL2 (ι := Fin p) μ u) (pureTensorL2 (ι := Fin k) μ u))) =
    unregroupL2 μ q k (separatedL2 (sectorMeasure μ q) (sectorMeasure μ k)
      (A (pureSymmetricTensor μ p u) : ProductL2 μ (Fin q))
      (pureTensorL2 (ι := Fin k) μ u)) at hA
  rw [hA, hsplit q k v,
    (unregroupL2 μ q k).inner_map_map, separatedL2_inner, inner_pureTensorL2,
    Fintype.card_fin]
  rfl

/-- The same actual sector operator has exactly the source ε and factorial
coefficient, including p=0, q=0 and k=0. -/
theorem wickSectorAdded_pairing (epsilon : ℝ) {p q : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (k : ℕ) (v u : Lp ℂ 2 μ) :
    inner ℂ (pureSymmetricTensor μ (q + k) v)
      (wickSectorAdded μ epsilon A k (pureSymmetricTensor μ (p + k) u)) =
      (((epsilon ^ (((p : ℝ) + (q : ℝ)) / 2) *
        Real.sqrt (((p + k).factorial : ℝ) * ((q + k).factorial : ℝ)) /
          (k.factorial : ℝ) : ℝ) : ℂ)) *
        (wickKernelPolarized μ A v u * inner ℂ v u ^ k) := by
  change inner ℂ (pureSymmetricTensor μ (q + k) v)
    ((LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ) •
      unscaledWickAdded μ A k (pureSymmetricTensor μ (p + k) u)) = _
  rw [inner_smul_right (𝕜 := ℂ) (E := ↥(SymmetricSector μ (q + k)))
    (pureSymmetricTensor μ (q + k) v)
    (unscaledWickAdded μ A k (pureSymmetricTensor μ (p + k) u))
    (LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) : ℂ), unscaledWickAdded_pairing]
  have hc : LLFPSectorCandidate.wickCoefficient epsilon p q (p + k) =
      epsilon ^ (((p : ℝ) + (q : ℝ)) / 2) *
        Real.sqrt (((p + k).factorial : ℝ) * ((q + k).factorial : ℝ)) /
          (k.factorial : ℝ) := by
    unfold LLFPSectorCandidate.wickCoefficient
    rw [if_pos (Nat.le_add_right p k),
      show p + k + q - p = q + k by omega,
      show p + k - p = k by omega]
  rw [hc]

end LiebLiniger.FixedPeriod.Quantum

end -- closes the original anonymous noncomputable section
end LLFPQ2023OriginalFile01

-- Original LiebLiniger.FixedPeriod.Quantum.WickPureTensorTotality; body SHA256 5d9fbf33587fbfa8c462298b528b4131bd4f84e6a4819771cbe6b8c3fe5db573
section LLFPQ2023OriginalFile02

/-! Narrow genuine full-sector pure totality. The TWO declarations and their
proof bodies are copied VERBATIM from author-frozen90b1, independently reviewed
as used support in26f012. No zeroth/first bracket or derivative-kernel import is
needed for these proofs. SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Genuine pure powers determine every vector of the COMPLETE physical sector. -/
theorem wickSymmetricSector_eq_zero_of_inner_pure (n : ℕ) (ψ : SymmetricSector μ n)
    (hψ : ∀ u : Lp ℂ 2 μ, inner ℂ ψ (pureSymmetricTensor μ n u) = 0) : ψ = 0 := by
  let F := (innerSL ℂ ψ).compContinuousMultilinearMap
    (symmetricTensorContinuousMultilinear μ n)
  have hs (σ : Equiv.Perm (Fin n)) (u : Fin n → Lp ℂ 2 μ) :
      F (fun i => u (σ i)) = F u := by
    exact congrArg (fun z : SymmetricSector μ n => inner ℂ ψ z)
      (symmetricTensorContinuousMultilinear_permutation μ n σ u)
  have hd (u : Lp ℂ 2 μ) : F (fun _ => u) = 0 := by
    change inner ℂ ψ (symmetricTensorContinuousMultilinear μ n (fun _ => u)) = 0
    rw [symmetricTensorContinuousMultilinear_diagonal]
    exact hψ u
  have hF := continuousMultilinearMap_eq_zero_of_diagonal F hs hd
  apply Subtype.ext
  apply mixedTensorL2_eq_zero_of_inner μ
  intro u
  have hh := congrArg (fun G => G u) hF
  change inner ℂ (ψ : ProductL2 μ (Fin n))
    (symmetrizeL2 μ (mixedTensorL2 μ u)) = 0 at hh
  exact (inner_symmetricSector_symmetrize μ n ψ (mixedTensorL2 μ u)).symm.trans hh

/-- Actual complete-sector bounded operators are determined by every pure input
and pure output pairing. There is no density/uniqueness hypothesis. -/
theorem wickSymmetricSector_operator_eq_of_pure_pairings {p q : ℕ}
    (T S : SymmetricSector μ p →L[ℂ] SymmetricSector μ q)
    (h : ∀ u v : Lp ℂ 2 μ,
      inner ℂ (pureSymmetricTensor μ q v) (T (pureSymmetricTensor μ p u)) =
        inner ℂ (pureSymmetricTensor μ q v) (S (pureSymmetricTensor μ p u))) : T = S := by
  let R := T - S
  have hR (u : Lp ℂ 2 μ) : R (pureSymmetricTensor μ p u) = 0 := by
    apply wickSymmetricSector_eq_zero_of_inner_pure μ q
    intro v
    change inner ℂ (T (pureSymmetricTensor μ p u) - S (pureSymmetricTensor μ p u))
      (pureSymmetricTensor μ q v) = 0
    rw [inner_sub_left]
    apply sub_eq_zero.mpr
    simpa only [inner_conj_symm] using congrArg conj (h u v)
  have hstar (z : SymmetricSector μ q) : R.adjoint z = 0 := by
    apply wickSymmetricSector_eq_zero_of_inner_pure μ p
    intro u
    rw [ContinuousLinearMap.adjoint_inner_left, hR, inner_zero_right]
  apply ContinuousLinearMap.ext
  intro x
  apply sub_eq_zero.mp
  change R x = 0
  apply ext_inner_right ℂ
  intro z
  rw [← ContinuousLinearMap.adjoint_inner_right, hstar, inner_zero_right, inner_zero_left]

end LiebLiniger.FixedPeriod.Quantum

end -- closes the original anonymous noncomputable section
end LLFPQ2023OriginalFile02

-- Original LiebLiniger.FixedPeriod.Quantum.WickElementaryPhysicalActions; body SHA256 f1abf6c3b0acc64bec68503377584b2400f525613446037dc4b0e5f489157990
section LLFPQ2023OriginalFile03

/-! Actual elementary Wick creation/annihilation and their all-sector pure
matrix elements. The kernels are literal rank-one vacuum/one-particle maps;
the operators are EXACTLY wickSectorMap, not polynomial-model substitutes.
The derivative characterization of creation is earned on complete sectors.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem elementary_sectorCast_pure {m n : ℕ} (h : m = n) (u : Lp ℂ 2 μ) :
    symmetricSectorCast μ h (pureSymmetricTensor μ m u) = pureSymmetricTensor μ n u := by
  subst n
  rfl

/-- The actual source-sector map has its exact pure matrix element, with the
available input count proved before any natural subtraction is used. -/
theorem wickSectorMap_available_pairing (epsilon : ℝ) {p q n : ℕ}
    (A : SymmetricSector μ p →L[ℂ] SymmetricSector μ q) (hn : p ≤ n)
    (v u : Lp ℂ 2 μ) :
    inner ℂ (pureSymmetricTensor μ (n + q - p) v)
      (wickSectorMap μ epsilon A n (pureSymmetricTensor μ n u)) =
      (LLFPSectorCandidate.wickCoefficient epsilon p q n : ℂ) *
        (wickKernelPolarized μ A v u * inner ℂ v u ^ (n - p)) := by
  have hpn : p + (n - p) = n := by omega
  have hqn : q + (n - p) = n + q - p := by omega
  have hin := elementary_sectorCast_pure μ hpn.symm u
  have hout := elementary_sectorCast_pure μ hqn v
  rw [wickSectorMap, dif_pos hn]
  change inner ℂ (pureSymmetricTensor μ (n + q - p) v)
    (symmetricSectorCast μ hqn
      (wickSectorAdded μ epsilon A (n - p)
        (symmetricSectorCast μ hpn.symm (pureSymmetricTensor μ n u)))) = _
  rw [hin, ← hout,
    (symmetricSectorCast μ hqn).inner_map_map,
    wickSectorAdded_pairing]
  simp only [hpn, hqn]
  unfold LLFPSectorCandidate.wickCoefficient
  rw [if_pos hn]

/-- Literal source kernel for one creation, with the actual normalized vacuum. -/
def wickCreationVacuumKernel (h : Lp ℂ 2 μ) :
    SymmetricSector μ 0 →L[ℂ] SymmetricSector μ 1 :=
  InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 1 h)
    (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))

/-- Literal adjoint rank-one source kernel for one annihilation. -/
def wickAnnihilationVacuumKernel (g : Lp ℂ 2 μ) :
    SymmetricSector μ 1 →L[ℂ] SymmetricSector μ 0 :=
  InnerProductSpace.rankOne ℂ (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))
    (pureSymmetricTensor μ 1 g)

def sourceWickCreation (epsilon : ℝ) (h : Lp ℂ 2 μ) (n : ℕ) :
    SymmetricSector μ n →L[ℂ] SymmetricSector μ (n + 1) :=
  wickSectorMap μ epsilon (wickCreationVacuumKernel μ h) n

def sourceWickAnnihilation (epsilon : ℝ) (g : Lp ℂ 2 μ) (n : ℕ) :
    SymmetricSector μ (n + 1) →L[ℂ] SymmetricSector μ n :=
  wickSectorMap μ epsilon (wickAnnihilationVacuumKernel μ g) (n + 1)

/-- Exact epsilon/particle scalar, earned from source Wick coefficients below. -/
def sourceWickElementaryCoefficient (epsilon : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt epsilon * Real.sqrt (n + 1 : ℕ)

private theorem elementary_creation_coefficient (epsilon : ℝ) (n : ℕ) :
    LLFPSectorCandidate.wickCoefficient epsilon 0 1 n = sourceWickElementaryCoefficient epsilon n := by
  rw [LLFPSectorCandidate.wickCoefficient_eq_falling epsilon 0 1 n (Nat.zero_le _)]
  norm_num [sourceWickElementaryCoefficient, ← Real.sqrt_eq_rpow]

private theorem elementary_annihilation_coefficient (epsilon : ℝ) (n : ℕ) :
    LLFPSectorCandidate.wickCoefficient epsilon 1 0 (n + 1) = sourceWickElementaryCoefficient epsilon n := by
  rw [LLFPSectorCandidate.wickCoefficient_eq_falling epsilon 1 0 (n + 1) (by omega)]
  norm_num [sourceWickElementaryCoefficient, ← Real.sqrt_eq_rpow]

private theorem elementary_creation_symbol (h v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (wickCreationVacuumKernel μ h) v u = inner ℂ v h := by
  simp only [wickKernelPolarized, wickCreationVacuumKernel, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_pureSymmetricTensor, pow_zero, pow_one, one_mul, mul_one]

private theorem elementary_annihilation_symbol (g v u : Lp ℂ 2 μ) :
    wickKernelPolarized μ (wickAnnihilationVacuumKernel μ g) v u = inner ℂ g u := by
  simp only [wickKernelPolarized, wickAnnihilationVacuumKernel, InnerProductSpace.rankOne_apply,
    inner_smul_right, inner_pureSymmetricTensor, pow_zero, pow_one, one_mul, mul_one]

/-- Exact pure matrix element of actual source creation at EVERY n, including0. -/
theorem sourceWickCreation_pairing (epsilon : ℝ) (h v u : Lp ℂ 2 μ) (n : ℕ) :
    inner ℂ (pureSymmetricTensor μ (n + 1) v)
      (sourceWickCreation μ epsilon h n (pureSymmetricTensor μ n u)) =
      (sourceWickElementaryCoefficient epsilon n : ℂ) *
        (inner ℂ v h * inner ℂ v u ^ n) := by
  have hp := wickSectorMap_available_pairing μ epsilon (wickCreationVacuumKernel μ h)
    (n := n) (Nat.zero_le _) v u
  simpa only [sourceWickCreation, Nat.sub_zero, elementary_creation_coefficient,
    elementary_creation_symbol] using hp

/-- Actual annihilation acts on each pure symmetric tensor with the source
sqrt(epsilon)*sqrt(n+1) coefficient. It is not an assumed weighted shift. -/
theorem sourceWickAnnihilation_pure (epsilon : ℝ) (g u : Lp ℂ 2 μ) (n : ℕ) :
    sourceWickAnnihilation μ epsilon g n (pureSymmetricTensor μ (n + 1) u) =
      ((sourceWickElementaryCoefficient epsilon n : ℂ) * inner ℂ g u) •
        pureSymmetricTensor μ n u := by
  apply sub_eq_zero.mp
  apply wickSymmetricSector_eq_zero_of_inner_pure μ n
  intro v
  rw [inner_sub_left]
  apply sub_eq_zero.mpr
  have hp := wickSectorMap_available_pairing μ epsilon (wickAnnihilationVacuumKernel μ g)
    (n := n + 1) (by omega) v u
  have hleft : inner ℂ (pureSymmetricTensor μ n v)
      (sourceWickAnnihilation μ epsilon g n (pureSymmetricTensor μ (n + 1) u)) =
      inner ℂ (pureSymmetricTensor μ n v)
        (((sourceWickElementaryCoefficient epsilon n : ℂ) * inner ℂ g u) •
          pureSymmetricTensor μ n u) := by
    have hp' : inner ℂ (pureSymmetricTensor μ n v)
        (sourceWickAnnihilation μ epsilon g n (pureSymmetricTensor μ (n + 1) u)) =
        (sourceWickElementaryCoefficient epsilon n : ℂ) *
          (inner ℂ g u * inner ℂ v u ^ n) := by
      simpa only [sourceWickAnnihilation, Nat.add_zero, Nat.add_sub_cancel, Nat.succ_sub_one,
        elementary_annihilation_coefficient, elementary_annihilation_symbol] using hp
    rw [inner_smul_right (𝕜 := ℂ) (E := ↥(SymmetricSector μ n))
      (pureSymmetricTensor μ n v) (pureSymmetricTensor μ n u)
      ((sourceWickElementaryCoefficient epsilon n : ℂ) * inner ℂ g u),
      inner_pureSymmetricTensor]
    exact hp'.trans (by ring)
  simpa only [inner_conj_symm] using congrArg conj hleft

/-- Differentiating the true pure tensor pairing, after earning both derivatives. -/
theorem inner_pure_wickPureTensorDerivative (n : ℕ) (v u h : Lp ℂ 2 μ) :
    inner ℂ (pureSymmetricTensor μ n v) (wickPureTensorDerivative μ n u h) =
      (n : ℂ) * inner ℂ v u ^ (n - 1) * inner ℂ v h := by
  have hleft := (innerSL ℂ (pureSymmetricTensor μ n v)).hasFDerivAt.comp u
    (wickPureTensor_hasFDerivAt μ n u)
  have hright := ((innerSL ℂ v).hasFDerivAt (x := u)).pow n
  have hfun : (fun x : Lp ℂ 2 μ =>
      inner ℂ (pureSymmetricTensor μ n v) (pureSymmetricTensor μ n x)) =
      (fun x : Lp ℂ 2 μ => inner ℂ v x ^ n) := by
    funext x
    exact inner_pureSymmetricTensor μ n v x
  change HasFDerivAt (fun x : Lp ℂ 2 μ =>
    inner ℂ (pureSymmetricTensor μ n v) (pureSymmetricTensor μ n x)) _ u at hleft
  rw [hfun] at hleft
  have heq := hleft.unique hright
  have heval := congrArg (fun T : Lp ℂ 2 μ →L[ℂ] ℂ => T h) heq
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    ContinuousLinearMap.smul_apply, Nat.cast_smul_eq_nsmul, nsmul_eq_mul,
    smul_eq_mul] using heval

/-- Actual source creation is the scaled true derivative of a pure tensor.
This form avoids division and retains n=0. -/
theorem sourceWickCreation_pure_derivative (epsilon : ℝ) (h u : Lp ℂ 2 μ) (n : ℕ) :
    (Real.sqrt (n + 1 : ℕ) : ℂ) •
      sourceWickCreation μ epsilon h n (pureSymmetricTensor μ n u) =
    (Real.sqrt epsilon : ℂ) • wickPureTensorDerivative μ (n + 1) u h := by
  apply sub_eq_zero.mp
  apply wickSymmetricSector_eq_zero_of_inner_pure μ (n + 1)
  intro v
  rw [inner_sub_left]
  apply sub_eq_zero.mpr
  have hs : (Real.sqrt (n + 1 : ℕ) : ℂ) * (Real.sqrt (n + 1 : ℕ) : ℂ) =
      ((n + 1 : ℕ) : ℂ) := by
    exact_mod_cast (show Real.sqrt (n + 1 : ℕ) * Real.sqrt (n + 1 : ℕ) = (n + 1 : ℕ) by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℕ) by positivity)])
  have hp : inner ℂ (pureSymmetricTensor μ (n + 1) v)
      ((Real.sqrt (n + 1 : ℕ) : ℂ) •
        sourceWickCreation μ epsilon h n (pureSymmetricTensor μ n u)) =
      inner ℂ (pureSymmetricTensor μ (n + 1) v)
        ((Real.sqrt epsilon : ℂ) • wickPureTensorDerivative μ (n + 1) u h) := by
    rw [inner_smul_right (𝕜 := ℂ) (E := ↥(SymmetricSector μ (n + 1)))
        (pureSymmetricTensor μ (n + 1) v)
        (sourceWickCreation μ epsilon h n (pureSymmetricTensor μ n u))
        (Real.sqrt (n + 1 : ℕ) : ℂ),
      inner_smul_right (𝕜 := ℂ) (E := ↥(SymmetricSector μ (n + 1)))
        (pureSymmetricTensor μ (n + 1) v) (wickPureTensorDerivative μ (n + 1) u h)
        (Real.sqrt epsilon : ℂ),
      sourceWickCreation_pairing, inner_pure_wickPureTensorDerivative]
    simp only [Nat.add_sub_cancel, sourceWickElementaryCoefficient, Complex.ofReal_mul]
    calc
      _ = (Real.sqrt epsilon : ℂ) *
        ((Real.sqrt (n + 1 : ℕ) : ℂ) * (Real.sqrt (n + 1 : ℕ) : ℂ)) *
        (inner ℂ v u ^ n * inner ℂ v h) := by ring
      _ = _ := by rw [hs]; ring
  simpa only [inner_conj_symm] using congrArg conj hp
end LiebLiniger.FixedPeriod.Quantum

end -- closes the original anonymous noncomputable section
end LLFPQ2023OriginalFile03

-- Original LiebLiniger.FixedPeriod.Quantum.WickElementaryPhysicalCCR; body SHA256 8eacf77fc7ca99e3ec021e7aa3c90ad0f21075691c7a561914048f6680fcd7eb
section LLFPQ2023OriginalFile04

/-! Genuine elementary physical CCR/product identity for ACTUAL sector Wick
maps. The proof differentiates the independently earned pure-tensor action,
then uses proved pure-pairing totality on complete symmetric sectors. No CCR,
operator product, finite-mode transport or normal-order theorem is a premise.
Positive sectors and vacuum are both retained. SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasure μ]

private theorem elementary_sqrt_sq (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (Real.sqrt epsilon : ℂ) * (Real.sqrt epsilon : ℂ) = (epsilon : ℂ) := by
  exact_mod_cast (show Real.sqrt epsilon * Real.sqrt epsilon = epsilon by
    nlinarith [Real.sq_sqrt hepsilon.le])

/-- Differentiate the actual bounded annihilation action, after earning both
Frechet derivatives. This is the direct physical slot Leibniz identity. -/
theorem sourceWickAnnihilation_pure_derivative (epsilon : ℝ)
    (g u h : Lp ℂ 2 μ) (n : ℕ) :
    sourceWickAnnihilation μ epsilon g n (wickPureTensorDerivative μ (n + 1) u h) =
      (sourceWickElementaryCoefficient epsilon n : ℂ) •
        (inner ℂ g u • wickPureTensorDerivative μ n u h +
          inner ℂ g h • pureSymmetricTensor μ n u) := by
  have hleft := (sourceWickAnnihilation μ epsilon g n).hasFDerivAt.comp u
    (wickPureTensor_hasFDerivAt μ (n + 1) u)
  have hright := ((innerSL ℂ g).hasFDerivAt.smul
    (wickPureTensor_hasFDerivAt μ n u)).const_smul
      (sourceWickElementaryCoefficient epsilon n : ℂ)
  have hfun : (fun v : Lp ℂ 2 μ =>
      sourceWickAnnihilation μ epsilon g n (pureSymmetricTensor μ (n + 1) v)) =
      (fun v : Lp ℂ 2 μ => (sourceWickElementaryCoefficient epsilon n : ℂ) •
        (inner ℂ g v • pureSymmetricTensor μ n v)) := by
    funext v
    simpa only [mul_smul] using sourceWickAnnihilation_pure μ epsilon g v n
  change HasFDerivAt (fun v : Lp ℂ 2 μ =>
    sourceWickAnnihilation μ epsilon g n (pureSymmetricTensor μ (n + 1) v)) _ u at hleft
  rw [hfun] at hleft
  have heq := hleft.unique hright
  have heval := congrArg (fun T : Lp ℂ 2 μ →L[ℂ] SymmetricSector μ n => T h) heq
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply] using heval

/-- Actual creation followed by actual annihilation on every pure vector.
There is no occupation-weighted-shift or algebraic-particle replacement. -/
theorem sourceWickAnnihilation_creation_pure (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g h u : Lp ℂ 2 μ) (n : ℕ) :
    sourceWickAnnihilation μ epsilon g n
      (sourceWickCreation μ epsilon h n (pureSymmetricTensor μ n u)) =
      (epsilon : ℂ) • (inner ℂ g u • wickPureTensorDerivative μ n u h +
        inner ℂ g h • pureSymmetricTensor μ n u) := by
  have hscaled := congrArg (sourceWickAnnihilation μ epsilon g n)
    (sourceWickCreation_pure_derivative μ epsilon h u n)
  simp only [map_smul] at hscaled
  rw [sourceWickAnnihilation_pure_derivative, smul_smul] at hscaled
  have hcoef : (Real.sqrt epsilon : ℂ) *
      (sourceWickElementaryCoefficient epsilon n : ℂ) =
      (Real.sqrt (n + 1 : ℕ) : ℂ) * (epsilon : ℂ) := by
    unfold sourceWickElementaryCoefficient
    rw [Complex.ofReal_mul]
    calc
      _ = ((Real.sqrt epsilon : ℂ) * (Real.sqrt epsilon : ℂ)) *
          (Real.sqrt (n + 1 : ℕ) : ℂ) := by ring
      _ = _ := by rw [elementary_sqrt_sq epsilon hepsilon]; ring
  rw [hcoef, ← smul_smul] at hscaled
  have hnz : (Real.sqrt (n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show (0 : ℝ) < (n + 1 : ℕ) by positivity)).ne'
  have hc := congrArg (fun z : SymmetricSector μ n =>
    (Real.sqrt (n + 1 : ℕ) : ℂ)⁻¹ • z) hscaled
  simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hnz, one_mul, one_smul] using hc

/-- Reverse actual product on a positive input sector, with every scalar
normalization earned from the SAME source creation/annihilation maps. -/
theorem sourceWickCreation_annihilation_pure (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g h u : Lp ℂ 2 μ) (n : ℕ) :
    sourceWickCreation μ epsilon h n
      (sourceWickAnnihilation μ epsilon g n (pureSymmetricTensor μ (n + 1) u)) =
      (epsilon : ℂ) • (inner ℂ g u • wickPureTensorDerivative μ (n + 1) u h) := by
  rw [sourceWickAnnihilation_pure, map_smul]
  calc
    _ = ((Real.sqrt epsilon : ℂ) * inner ℂ g u) •
        ((Real.sqrt (n + 1 : ℕ) : ℂ) •
          sourceWickCreation μ epsilon h n (pureSymmetricTensor μ n u)) := by
      simp only [smul_smul, sourceWickElementaryCoefficient, Complex.ofReal_mul]
      congr 1
      ring
    _ = ((Real.sqrt epsilon : ℂ) * inner ℂ g u) •
        ((Real.sqrt epsilon : ℂ) • wickPureTensorDerivative μ (n + 1) u h) := by
      rw [sourceWickCreation_pure_derivative]
    _ = _ := by
      simp only [smul_smul]
      congr 1
      calc
        _ = ((Real.sqrt epsilon : ℂ) * (Real.sqrt epsilon : ℂ)) * inner ℂ g u := by ring
        _ = _ := by rw [elementary_sqrt_sq epsilon hepsilon]

/-- GENUINE bounded-operator CCR on EVERY positive physical input sector.
The particle number is n+1, so the reverse product lands in the SAME sector.
The correction is epsilon times the actual conjugate-first inner(g,h). -/
theorem sourceWick_CCR_positive_sector (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g h : Lp ℂ 2 μ) (n : ℕ) :
    (sourceWickAnnihilation μ epsilon g (n + 1)).comp
        (sourceWickCreation μ epsilon h (n + 1)) =
      (sourceWickCreation μ epsilon h n).comp (sourceWickAnnihilation μ epsilon g n) +
        ((epsilon : ℂ) * inner ℂ g h) • ContinuousLinearMap.id ℂ (SymmetricSector μ (n + 1)) := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  congr 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [sourceWickAnnihilation_creation_pure μ epsilon hepsilon,
    sourceWickCreation_annihilation_pure μ epsilon hepsilon]
  simp only [smul_add, smul_smul]

/-- The derivative of the scalar vacuum tensor is actually zero. -/
private theorem elementary_vacuum_derivative (u h : Lp ℂ 2 μ) :
    wickPureTensorDerivative μ 0 u h = 0 := by
  apply wickSymmetricSector_eq_zero_of_inner_pure μ 0
  intro v
  have hp := inner_pure_wickPureTensorDerivative μ 0 v u h
  have hz : inner ℂ (pureSymmetricTensor μ 0 v) (wickPureTensorDerivative μ 0 u h) = 0 := by
    simpa only [Nat.cast_zero, zero_mul] using hp
  simpa only [inner_conj_symm, map_zero] using congrArg (starRingEnd ℂ) hz

/-- GENUINE vacuum CCR: the reverse product vanishes and the forward actual
source Wick product equals epsilon inner(g,h) times the vacuum identity. -/
theorem sourceWick_CCR_vacuum (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g h : Lp ℂ 2 μ) :
    (sourceWickAnnihilation μ epsilon g 0).comp (sourceWickCreation μ epsilon h 0) =
      ((epsilon : ℂ) * inner ℂ g h) • ContinuousLinearMap.id ℂ (SymmetricSector μ 0) := by
  apply wickSymmetricSector_operator_eq_of_pure_pairings μ
  intro u v
  congr 1
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply]
  rw [sourceWickAnnihilation_creation_pure μ epsilon hepsilon, elementary_vacuum_derivative]
  simp only [smul_zero, zero_add, smul_smul]

/-- The source annihilation map itself is zero on vacuum by its unavailable
input branch; the vacuum CCR above did not invent an extra occupied sector. -/
theorem sourceWickAnnihilation_vacuum_zero (epsilon : ℝ) (g : Lp ℂ 2 μ) :
    wickSectorMap μ epsilon (wickAnnihilationVacuumKernel μ g) 0 = 0 :=
  wickSectorMap_of_lt μ epsilon (wickAnnihilationVacuumKernel μ g) (by omega)
end LiebLiniger.FixedPeriod.Quantum

end -- closes the original anonymous noncomputable section
end LLFPQ2023OriginalFile04

-- Original LiebLiniger.FixedPeriod.Quantum.WickFiniteParticleCCR; body SHA256 e22315c18d3b5ae95fa3bc846411a13ed99fc6cff202add13718ebc1529b477a
section LLFPQ2023OriginalFile05

/-! Actual physical finite-particle creation and annihilation. Each direct-sum
summand is the COMPLETE source SymmetricSector, with no finite-mode restriction
or occupation-basis replacement. The operators use precisely sourceWickCreation
and sourceWickAnnihilation; the latter has the literal vacuum-zero branch.
The global CCR and its first repeated-creation normal-ordering step are earned
from the genuine complete-sector operator CCR. SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped DirectSum
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- The full algebraic finite-particle domain of the physical symmetric Fock
space. Every summand is the already constructed complete symmetric sector. -/
abbrev SourceFiniteParticleSpace := ⨁ n : ℕ, SymmetricSector μ n

/-- The actual source Wick creation, applied to every finite-particle vector.
This linear map has no asserted bounded extension to the Hilbert Fock space. -/
def sourceFiniteParticleCreation (epsilon : ℝ) (h : Lp ℂ 2 μ) :
    Module.End ℂ (SourceFiniteParticleSpace μ) :=
  DirectSum.toModule ℂ ℕ _ (fun n =>
    (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (n + 1)).comp
      (sourceWickCreation μ epsilon h n).toLinearMap)

/-- Actual annihilation on a single source sector, with genuine vacuum zero. -/
def sourceFiniteParticleAnnihilationComponent (epsilon : ℝ) (g : Lp ℂ 2 μ) :
    (n : ℕ) → SymmetricSector μ n →ₗ[ℂ] SourceFiniteParticleSpace μ
  | 0 => 0
  | n + 1 => (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n).comp
      (sourceWickAnnihilation μ epsilon g n).toLinearMap

/-- The actual source Wick annihilation on every finite-particle vector. -/
def sourceFiniteParticleAnnihilation (epsilon : ℝ) (g : Lp ℂ 2 μ) :
    Module.End ℂ (SourceFiniteParticleSpace μ) :=
  DirectSum.toModule ℂ ℕ _ (sourceFiniteParticleAnnihilationComponent μ epsilon g)

@[simp] theorem sourceFiniteParticleCreation_lof (epsilon : ℝ) (h : Lp ℂ 2 μ)
    (n : ℕ) (v : SymmetricSector μ n) :
    sourceFiniteParticleCreation μ epsilon h
      (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (n + 1)
        (sourceWickCreation μ epsilon h n v) := by
  rw [sourceFiniteParticleCreation, DirectSum.toModule_lof]
  rfl

@[simp] theorem sourceFiniteParticleAnnihilation_lof_zero (epsilon : ℝ)
    (g : Lp ℂ 2 μ) (v : SymmetricSector μ 0) :
    sourceFiniteParticleAnnihilation μ epsilon g
      (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) 0 v) = 0 := by
  rw [sourceFiniteParticleAnnihilation, DirectSum.toModule_lof]
  rfl

@[simp] theorem sourceFiniteParticleAnnihilation_lof_succ (epsilon : ℝ)
    (g : Lp ℂ 2 μ) (n : ℕ) (v : SymmetricSector μ (n + 1)) :
    sourceFiniteParticleAnnihilation μ epsilon g
      (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (n + 1) v) =
      DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n
        (sourceWickAnnihilation μ epsilon g n v) := by
  rw [sourceFiniteParticleAnnihilation, DirectSum.toModule_lof]
  rfl

/-- The concrete global CCR on the whole physical finite-particle domain.
Neither a commutation relation nor a product expansion is an input premise. -/
theorem sourceFiniteParticle_CCR_apply (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g h : Lp ℂ 2 μ) (v : SourceFiniteParticleSpace μ) :
    sourceFiniteParticleAnnihilation μ epsilon g
        (sourceFiniteParticleCreation μ epsilon h v) =
      sourceFiniteParticleCreation μ epsilon h
        (sourceFiniteParticleAnnihilation μ epsilon g v) +
        ((epsilon : ℂ) * inner ℂ g h) • v := by
  induction v using DirectSum.induction_on with
  | zero => simp only [map_zero, smul_zero, add_zero]
  | of n x =>
    change sourceFiniteParticleAnnihilation μ epsilon g
      (sourceFiniteParticleCreation μ epsilon h
        (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n x)) =
      sourceFiniteParticleCreation μ epsilon h
        (sourceFiniteParticleAnnihilation μ epsilon g
          (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n x)) +
        ((epsilon : ℂ) * inner ℂ g h) •
          (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) n x)
    cases n with
    | zero =>
      simp only [sourceFiniteParticleCreation_lof,
        sourceFiniteParticleAnnihilation_lof_succ,
        sourceFiniteParticleAnnihilation_lof_zero, map_zero, zero_add]
      have heq := congrArg (fun T : SymmetricSector μ 0 →L[ℂ] SymmetricSector μ 0 => T x)
        (sourceWick_CCR_vacuum μ epsilon hepsilon g h)
      have hh := congrArg (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) 0) heq
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, map_smul] using hh
    | succ n =>
      simp only [sourceFiniteParticleCreation_lof,
        sourceFiniteParticleAnnihilation_lof_succ]
      have heq := congrArg
        (fun T : SymmetricSector μ (n + 1) →L[ℂ] SymmetricSector μ (n + 1) => T x)
        (sourceWick_CCR_positive_sector μ epsilon hepsilon g h n)
      have hh := congrArg (DirectSum.lof ℂ ℕ (fun n : ℕ => ↥(SymmetricSector μ n)) (n + 1)) heq
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_add,
        map_smul] using hh
  | add v w hv hw =>
    simp only [map_add, smul_add, hv, hw]
    abel

/-- The same physical CCR as an actual endomorphism equality. -/
theorem sourceFiniteParticle_CCR (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (g h : Lp ℂ 2 μ) :
    sourceFiniteParticleAnnihilation μ epsilon g * sourceFiniteParticleCreation μ epsilon h =
      sourceFiniteParticleCreation μ epsilon h * sourceFiniteParticleAnnihilation μ epsilon g +
        ((epsilon : ℂ) * inner ℂ g h) •
          (1 : Module.End ℂ (SourceFiniteParticleSpace μ)) := by
  apply LinearMap.ext
  intro v
  exact sourceFiniteParticle_CCR_apply μ epsilon hepsilon g h v

/-- First load-bearing repeated-creation normal-ordering identity, for arbitrary
physical L2 fields and every positive creation count. The scalar coefficient is
q epsilon inner(g,h), and powers are actual composition on finite particles. -/
theorem sourceFiniteParticle_annihilation_creation_pow (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (g h : Lp ℂ 2 μ) (q : ℕ)
    (v : SourceFiniteParticleSpace μ) :
    sourceFiniteParticleAnnihilation μ epsilon g
        ((sourceFiniteParticleCreation μ epsilon h ^ (q + 1)) v) =
      (sourceFiniteParticleCreation μ epsilon h ^ (q + 1))
        (sourceFiniteParticleAnnihilation μ epsilon g v) +
        (((q + 1 : ℕ) : ℂ) * ((epsilon : ℂ) * inner ℂ g h)) •
          ((sourceFiniteParticleCreation μ epsilon h ^ q) v) := by
  induction q with
  | zero =>
    simpa only [Nat.zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_one, one_mul] using
      sourceFiniteParticle_CCR_apply μ epsilon hepsilon g h v
  | succ q ih =>
    let C := sourceFiniteParticleCreation μ epsilon h
    let A := sourceFiniteParticleAnnihilation μ epsilon g
    let c : ℂ := (epsilon : ℂ) * inner ℂ g h
    change A ((C ^ (q + 1 + 1)) v) =
      (C ^ (q + 1 + 1)) (A v) + (((q + 1 + 1 : ℕ) : ℂ) * c) • ((C ^ (q + 1)) v)
    have hccr : A (C ((C ^ (q + 1)) v)) =
        C (A ((C ^ (q + 1)) v)) + c • ((C ^ (q + 1)) v) :=
      sourceFiniteParticle_CCR_apply μ epsilon hepsilon g h ((C ^ (q + 1)) v)
    have hih : A ((C ^ (q + 1)) v) =
        (C ^ (q + 1)) (A v) + (((q + 1 : ℕ) : ℂ) * c) • ((C ^ q) v) := ih
    rw [pow_succ', Module.End.mul_apply, hccr, hih, map_add, map_smul]
    have hpow : C ((C ^ q) v) = (C ^ (q + 1)) v := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hpow, ← Module.End.mul_apply, ← pow_succ']
    rw [add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

/-- Exact packet first-commutation identity in one normalized physical mode.
At epsilon=1 the CCR is one, with vacuum and all input sectors already included. -/
theorem sourceFiniteParticle_oneMode_first_commutation (h : Lp ℂ 2 μ)
    (hunit : ‖h‖ = 1) (q : ℕ) :
    sourceFiniteParticleAnnihilation μ 1 h *
        sourceFiniteParticleCreation μ 1 h ^ (q + 1) =
      sourceFiniteParticleCreation μ 1 h ^ (q + 1) *
          sourceFiniteParticleAnnihilation μ 1 h +
        (((q + 1 : ℕ) : ℂ)) • sourceFiniteParticleCreation μ 1 h ^ q := by
  have hinner : inner ℂ h h = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hunit]
    norm_num
  apply LinearMap.ext
  intro v
  have hh := sourceFiniteParticle_annihilation_creation_pow μ 1 (by norm_num) h h q v
  simpa only [Complex.ofReal_one, hinner, one_mul, mul_one, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply] using hh
end LiebLiniger.FixedPeriod.Quantum

end -- closes the original anonymous noncomputable section
end LLFPQ2023OriginalFile05

-- Original LiebLiniger.FixedPeriod.Quantum.WickOneModeNormalOrder; body SHA256 056969bc9e34b8caf5412abb360659b3daf6ca14148277d0ffa77cc6507a59b0
section LLFPQ2023OriginalFile06

/-! Exact one-mode Q2-023 normal ordering on ACTUAL physical finite particles.
The CCR is earned by the source Wick maps in the imported physical proof.
The two commuting maps below package precisely the packet's induction on p:
expanding (right multiplication + commutator)^p is Pascal's rule, and the
j-fold commutator of C^q is the actual falling factorial times C^(q-j).
The final public theorem has NO CCR, product, or transport hypothesis.
SOURCE ONLY / UNCOMPILED. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped DirectSum BigOperators
namespace LiebLiniger.FixedPeriod.Quantum
variable {X : Type} [MeasurableSpace X] (μ : Measure X)
  [SigmaFinite μ] [IsFiniteMeasure μ]

/-- Earn the SAME pointwise additive group from the actual direct-sum carrier.
This scoped cache adds no assumption or alternative finite-particle carrier. -/
local instance physicalFiniteParticleAddCommGroup : AddCommGroup (SourceFiniteParticleSpace μ) := by
  unfold SourceFiniteParticleSpace DirectSum
  infer_instance

private abbrev PhysicalEnd := Module.End ℂ (SourceFiniteParticleSpace μ)

private def physicalAnnihilationLeft (h : Lp ℂ 2 μ) :
    Module.End ℂ (PhysicalEnd μ) :=
  LinearMap.mulLeft ℂ (sourceFiniteParticleAnnihilation μ 1 h)

private def physicalAnnihilationRight (h : Lp ℂ 2 μ) :
    Module.End ℂ (PhysicalEnd μ) :=
  LinearMap.mulRight ℂ (sourceFiniteParticleAnnihilation μ 1 h)

private def physicalAnnihilationCommutator (h : Lp ℂ 2 μ) :
    Module.End ℂ (PhysicalEnd μ) :=
  physicalAnnihilationLeft μ h - physicalAnnihilationRight μ h

private theorem physical_left_pow (h : Lp ℂ 2 μ) (p : ℕ) (T : PhysicalEnd μ) :
    (physicalAnnihilationLeft μ h ^ p) T =
      sourceFiniteParticleAnnihilation μ 1 h ^ p * T := by
  induction p with
  | zero => simp only [pow_zero, Module.End.one_apply, one_mul]
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change sourceFiniteParticleAnnihilation μ 1 h *
      (sourceFiniteParticleAnnihilation μ 1 h ^ p * T) = _
    rw [← mul_assoc, ← pow_succ']

private theorem physical_right_pow (h : Lp ℂ 2 μ) (p : ℕ) (T : PhysicalEnd μ) :
    (physicalAnnihilationRight μ h ^ p) T =
      T * sourceFiniteParticleAnnihilation μ 1 h ^ p := by
  induction p with
  | zero => simp only [pow_zero, Module.End.one_apply, mul_one]
  | succ p ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change (T * sourceFiniteParticleAnnihilation μ 1 h ^ p) *
      sourceFiniteParticleAnnihilation μ 1 h = _
    rw [mul_assoc, ← pow_succ]

private theorem physical_commutator_right_commute (h : Lp ℂ 2 μ) :
    Commute (physicalAnnihilationCommutator μ h) (physicalAnnihilationRight μ h) := by
  change physicalAnnihilationCommutator μ h * physicalAnnihilationRight μ h =
    physicalAnnihilationRight μ h * physicalAnnihilationCommutator μ h
  apply LinearMap.ext
  intro T
  change (sourceFiniteParticleAnnihilation μ 1 h *
      (T * sourceFiniteParticleAnnihilation μ 1 h) -
      (T * sourceFiniteParticleAnnihilation μ 1 h) *
        sourceFiniteParticleAnnihilation μ 1 h) =
    (sourceFiniteParticleAnnihilation μ 1 h * T -
      T * sourceFiniteParticleAnnihilation μ 1 h) *
        sourceFiniteParticleAnnihilation μ 1 h
  simp only [sub_mul, mul_assoc]

/-- This private identity is earned from the actual physical first commutation,
including q=0, rather than assuming an abstract differential representation. -/
private theorem physical_commutator_creation_pow (h : Lp ℂ 2 μ)
    (hunit : ‖h‖ = 1) (q : ℕ) :
    physicalAnnihilationCommutator μ h
      (sourceFiniteParticleCreation μ 1 h ^ q) =
      (q : ℂ) • sourceFiniteParticleCreation μ 1 h ^ (q - 1) := by
  cases q with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_smul]
    change sourceFiniteParticleAnnihilation μ 1 h * 1 -
      1 * sourceFiniteParticleAnnihilation μ 1 h = 0
    simp only [mul_one, one_mul, sub_self]
  | succ q =>
    change sourceFiniteParticleAnnihilation μ 1 h *
        sourceFiniteParticleCreation μ 1 h ^ (q + 1) -
      sourceFiniteParticleCreation μ 1 h ^ (q + 1) *
        sourceFiniteParticleAnnihilation μ 1 h = _
    rw [sourceFiniteParticle_oneMode_first_commutation μ h hunit q,
      add_sub_cancel_left]
    simp only [Nat.add_sub_cancel]

private theorem physical_commutator_pow_creation_pow (h : Lp ℂ 2 μ)
    (hunit : ‖h‖ = 1) (q j : ℕ) :
    (physicalAnnihilationCommutator μ h ^ j)
        (sourceFiniteParticleCreation μ 1 h ^ q) =
      (q.descFactorial j : ℂ) • sourceFiniteParticleCreation μ 1 h ^ (q - j) := by
  induction j with
  | zero => simp only [pow_zero, Module.End.one_apply, Nat.descFactorial_zero,
      Nat.cast_one, one_smul, Nat.sub_zero]
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul,
      physical_commutator_creation_pow μ h hunit, smul_smul, Nat.descFactorial_succ,
      Nat.cast_mul]
    have hsub : q - j - 1 = q - (j + 1) := by omega
    rw [hsub]
    congr 1
    ring

/-- Exact full physical normal ordering, initially with the p+1 possible
contraction counts. Terms beyond q are genuinely zero, by the earned falling
factorial; no unavailable-sector assumption is imposed on vectors. -/
private theorem physical_normal_order_full_range (h : Lp ℂ 2 μ)
    (hunit : ‖h‖ = 1) (p q : ℕ) :
    sourceFiniteParticleAnnihilation μ 1 h ^ p * sourceFiniteParticleCreation μ 1 h ^ q =
      ∑ j ∈ Finset.range (p + 1),
        ((j.factorial * p.choose j * q.choose j : ℕ) : ℂ) •
          (sourceFiniteParticleCreation μ 1 h ^ (q - j) *
            sourceFiniteParticleAnnihilation μ 1 h ^ (p - j)) := by
  let D := physicalAnnihilationCommutator μ h
  let R := physicalAnnihilationRight μ h
  have hDR : Commute D R := physical_commutator_right_commute μ h
  have hsum : D + R = physicalAnnihilationLeft μ h := by
    dsimp only [D, R, physicalAnnihilationCommutator]
    exact sub_add_cancel
      (physicalAnnihilationLeft μ h : Module.End ℂ (PhysicalEnd μ))
      (physicalAnnihilationRight μ h : Module.End ℂ (PhysicalEnd μ))
  have hexp := congrArg (fun T : Module.End ℂ (PhysicalEnd μ) =>
    T (sourceFiniteParticleCreation μ 1 h ^ q)) (hDR.add_pow p)
  rw [hsum, physical_left_pow] at hexp
  rw [hexp, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hcomm : D ^ j * R ^ (p - j) = R ^ (p - j) * D ^ j :=
    (hDR.pow_pow j (p - j)).eq
  rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul,
    hcomm, Module.End.mul_apply]
  change (p.choose j) •
    ((physicalAnnihilationRight μ h ^ (p - j))
      ((physicalAnnihilationCommutator μ h ^ j)
        (sourceFiniteParticleCreation μ 1 h ^ q))) = _
  rw [physical_commutator_pow_creation_pow μ h hunit,
    map_smul, physical_right_pow]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    Nat.descFactorial_eq_factorial_mul_choose]
  congr 1
  push_cast
  ring

/-- WHOLE source Q2-023 finite-particle one-mode contraction formula.
The physical operators are exactly the source Wick maps at epsilon=1, on
complete symmetric sectors, and h is an arbitrary normalized physical L2 mode.
The formula retains p=0, q=0, vacuum and every finite input particle number. -/
theorem sourceFiniteParticle_oneMode_normal_order (h : Lp ℂ 2 μ)
    (hunit : ‖h‖ = 1) (p q : ℕ) :
    sourceFiniteParticleAnnihilation μ 1 h ^ p * sourceFiniteParticleCreation μ 1 h ^ q =
      ∑ j ∈ Finset.range (min p q + 1),
        ((j.factorial * p.choose j * q.choose j : ℕ) : ℂ) •
          (sourceFiniteParticleCreation μ 1 h ^ (q - j) *
            sourceFiniteParticleAnnihilation μ 1 h ^ (p - j)) := by
  rw [physical_normal_order_full_range μ h hunit p q]
  symm
  apply Finset.sum_subset
    (Finset.range_mono (Nat.succ_le_succ (Nat.min_le_left p q)))
  intro j hj hnot
  have hjp : j ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hlarge : min p q < j := by
    have hn : ¬ j < min p q + 1 := by simpa only [Finset.mem_range] using hnot
    omega
  have hq : q < j := by omega
  rw [Nat.choose_eq_zero_of_lt hq, Nat.mul_zero, Nat.cast_zero, zero_smul]

/-- The same whole formula evaluated on every actual physical finite-particle
vector; no Hilbert-Fock boundedness or domain extension is implicitly claimed. -/
theorem sourceFiniteParticle_oneMode_normal_order_apply (h : Lp ℂ 2 μ)
    (hunit : ‖h‖ = 1) (p q : ℕ) (v : SourceFiniteParticleSpace μ) :
    (sourceFiniteParticleAnnihilation μ 1 h ^ p)
        ((sourceFiniteParticleCreation μ 1 h ^ q) v) =
      ∑ j ∈ Finset.range (min p q + 1),
        ((j.factorial * p.choose j * q.choose j : ℕ) : ℂ) •
          ((sourceFiniteParticleCreation μ 1 h ^ (q - j))
            ((sourceFiniteParticleAnnihilation μ 1 h ^ (p - j)) v)) := by
  have hh := congrArg (fun T : PhysicalEnd μ => T v)
    (sourceFiniteParticle_oneMode_normal_order μ h hunit p q)
  simpa only [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] using hh
end LiebLiniger.FixedPeriod.Quantum

end -- closes the original anonymous noncomputable section
end LLFPQ2023OriginalFile06

