import Mathlib
import QuantumNLS.Prop022ACovTensor
import QuantumNLS.Prop022GClassical
import QuantumNLS.Prop022FactorialCoefficientsR115

/-! PROP-022 route A, stage A5c: covariance of the factorial coefficient data under `Γ(R)`.

For a unitary `R` of `L²(𝕋_L)` and kernels `B'_m = Γ_m(R) B_m Γ_m(R)⁻¹`:
* `symMap_insertion`, `symMap_insertion_adjoint`: the slot insertion `insertion r k u` and its adjoint;
* `mixedTerm_cov`, `pairTerm_cov`: the summands of the quadratic coefficients;
* `numberCoefficient_cov : Γ_1(R) a(B,u) Γ_1(R)⁻¹ = a(B', R u)`,
  `pairCoefficient_cov : Γ_2(R) b(B,u) = b(B', R u)`. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped InnerProductSpace
open ContinuousLinearMap

namespace QuantumNLS.Prop022ACovCoef
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GClassical Prop022ACovTensor
open Prop022TensorCompressionR115 Prop022FactorialCoefficientsR115

variable {L : ℝ} [Fact (0 < L)] (R : L2T L ≃ₗᵢ[ℂ] L2T L)

lemma conjSym_rel (p : ℕ) (A : HN L p →L[ℂ] HN L p) (y : HN L p) :
    symMap R p (A y) = conjSym R p A (symMap R p y) := by
  rw [conjSym_apply, LinearIsometryEquiv.symm_apply_apply]

lemma symMap_insertion (r k : ℕ) (u : L2T L) (x : HN L k) :
    symMap R (r + k) (insertion r k u x) = insertion r k (R u) (symMap R k x) := by
  change symMap R (r + k) ((physSector L (r + k)).orthogonalProjectionOnto
      ((splitIsometry (𝕜 := ℂ) (E := L2T L) r k).symm
        (htmul (htpow r u) (x : HilbertTensorPower ℂ (L2T L) k)))) =
    (physSector L (r + k)).orthogonalProjectionOnto
      ((splitIsometry (𝕜 := ℂ) (E := L2T L) r k).symm
        (htmul (htpow r (R u))
          ((symMap R k x : HN L k) : HilbertTensorPower ℂ (L2T L) k)))
  rw [symMap_orthProj, tensorMap_split_symm, tensorMap_htpow]
  rfl

lemma symMap_insertion_adjoint (r k : ℕ) (u : L2T L) (y : HN L (r + k)) :
    symMap R k ((insertion r k u).adjoint y) =
      (insertion r k (R u)).adjoint (symMap R (r + k) y) := by
  apply ext_inner_left ℂ
  intro w
  obtain ⟨w₀, rfl⟩ := (symMap R k).surjective w
  rw [adjoint_inner_right, ← symMap_insertion, LinearIsometryEquiv.inner_map_map,
    LinearIsometryEquiv.inner_map_map, adjoint_inner_right]

lemma mixedTerm_cov (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (r : ℕ) :
    conjSym R 1 (mixedTerm B u r) = mixedTerm (fun m => conjSym R m (B m)) (R u) r := by
  apply ContinuousLinearMap.ext
  intro y
  rw [conjSym_apply]
  simp only [mixedTerm, smul_apply, comp_apply, map_smul]
  rw [symMap_insertion_adjoint, conjSym_rel R (r + 1) (B (r + 1)), symMap_insertion R r 1 u,
    LinearIsometryEquiv.apply_symm_apply]

lemma pairTerm_cov (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) (r : ℕ) :
    symMap R 2 (Prop022TensorCompressionR115.pairTerm B u r) =
      Prop022TensorCompressionR115.pairTerm (fun m => conjSym R m (B m)) (R u) r := by
  simp only [Prop022TensorCompressionR115.pairTerm, map_smul]
  rw [symMap_insertion_adjoint, conjSym_apply]
  have h : symMap R (r + 2) (power (r + 2) u) = power (r + 2) (R u) := symMap_powerH R (r + 2) u
  rw [← h]
  simp only [conjSym_apply, LinearIsometryEquiv.symm_apply_apply]

/-- Conjugation of operators by `Γ_m(R)`, as a continuous linear map of the operator space. -/
def conjOp (m : ℕ) : (HN L m →L[ℂ] HN L m) →L[ℂ] (HN L m →L[ℂ] HN L m) :=
  ((ContinuousLinearMap.compL ℂ (HN L m) (HN L m) (HN L m))
      (symMap R m).toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((ContinuousLinearMap.compL ℂ (HN L m) (HN L m) (HN L m)).flip
      (symMap R m).symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma conjOp_apply (m : ℕ) (T : HN L m →L[ℂ] HN L m) : conjOp R m T = conjSym R m T := rfl

theorem numberCoefficient_cov (B : ∀ m, HN L m →L[ℂ] HN L m) (M A : ℝ) (hA : 0 ≤ A)
    (hB : FactorialBound B M A) (u : L2T L) (hu : ‖u‖ = 1) :
    conjSym R 1 (numberCoefficient B u) =
      numberCoefficient (fun m => conjSym R m (B m)) (R u) := by
  have hs := mixed_summable B M A hA hB u hu
  unfold numberCoefficient
  rw [← conjOp_apply, (conjOp R 1).map_tsum hs]
  exact tsum_congr (fun r => mixedTerm_cov R B u r)

theorem pairCoefficient_cov (B : ∀ m, HN L m →L[ℂ] HN L m) (u : L2T L) :
    symMap R 2 (pairCoefficient B u) =
      pairCoefficient (fun m => conjSym R m (B m)) (R u) := by
  unfold pairCoefficient
  have h : symMap R 2 (∑' r, Prop022TensorCompressionR115.pairTerm B u r) =
      ∑' r, symMap R 2 (Prop022TensorCompressionR115.pairTerm B u r) :=
    (symMap R 2).toContinuousLinearEquiv.map_tsum
  rw [h]
  exact tsum_congr (fun r => pairTerm_cov R B u r)

end QuantumNLS.Prop022ACovCoef

#print axioms QuantumNLS.Prop022ACovCoef.mixedTerm_cov
#print axioms QuantumNLS.Prop022ACovCoef.pairTerm_cov
#print axioms QuantumNLS.Prop022ACovCoef.numberCoefficient_cov
#print axioms QuantumNLS.Prop022ACovCoef.pairCoefficient_cov
