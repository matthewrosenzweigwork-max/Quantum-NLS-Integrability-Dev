import Mathlib
import QuantumNLS.Prop022BMain
import QuantumNLS.Prop022BExist
import QuantumNLS.Prop024WeylConventionR55

/-! PROP-022 route A, final corollary for the downstream consumers (PROP-021, PROP-024):
`Prop022PairInput_of_general` derives the fixed-implementation named input
`Prop024WeylConventionR55.Prop022PairInput` on the physical carrier `L2T L` and shows that the transported
propagator `V_H` of `Prop022AExact.PROP022_general_infinite_exact` (here `H = L2T L`, any unitary `U`) is exactly
the fixed R122 propagator `propagator` of the physical kernels.

* `Prop022PairInput` is, clause by clause, the conclusion of the frozen physical theorem
  `Prop022OMain.PROP022_physical_quadratic_propagator` (physical coordinates of the printed lemma: `numberOperator`,
  `pairKernel`, the Fourier-basis conjugation, `propagator`, `printedWeyl`, vacuum with `numberExpectation`);
* the general theorem's `V_H(t,s) = Γ(U)⁻¹ propagator Γ(U)` equals the fixed `propagator` for `U = refl` and, by the
  exact independence `VH_indep`, for every unitary `U` of `L2T L`: this is the fixed-propagator form of the vacuum and
  number-expectation clauses. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop022BPairInput
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors Prop022GTensor Prop022GClassical Prop022AFock Prop022ACovIndep
open Prop022BClass1 Prop022FockPropagatorR122 Prop022PositiveDataR126

variable {L : ℝ} [Fact (0 < L)]

lemma tensorMap_refl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (n : ℕ)
    (z : HilbertTensorPower ℂ E n) : tensorMap (LinearIsometryEquiv.refl ℂ E) n z = z := by
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (tensorMap _ n).continuous continuous_id
  | ih a =>
    rw [tensorMap_coe]
    congr 1
    induction a using AlgTensorPower.induction_on with
    | smul_ptprod r f => simp [map_smul, algMap_ptprod]
    | add x y hx hy => rw [map_add, hx, hy]

lemma fockMap_refl {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : FockSpace E) :
    fockMap (LinearIsometryEquiv.refl ℂ E) x = x :=
  lp.ext (funext fun n => Subtype.ext (tensorMap_refl n (x n : HilbertTensorPower ℂ E n)))

lemma conjSym_refl_L (m : ℕ) (T : HN L m →L[ℂ] HN L m) : conjSym (UI L) m T = T := by
  apply ContinuousLinearMap.ext
  intro y
  rw [conjSym_apply]
  have h : ∀ w : HN L m, symMap (UI L) m w = w := fun w => Subtype.ext (tensorMap_refl m _)
  have h' : ∀ w : HN L m, (symMap (UI L) m).symm w = w := fun w => by
    rw [LinearIsometryEquiv.symm_apply_eq]; exact (h w).symm
  rw [h, h']

/-- For `U = refl` the transported propagator is the fixed `propagator`. -/
theorem VH_refl_eq (K : Kernels (L2T L)) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A)
    (hs : KSelfAdj K) (u₀ : Prop001.Sphere (L2T L)) (t s : ℝ) (z : Fock L) :
    VH (UI L) K M A hA.le hK hs u₀.val u₀.property (zero_le_one.trans hM) t s z =
      propagator (positiveExtension K) M A (zero_le_one.trans hM) hA.le
        (positiveExtension_bound K M A hK) (positiveExtension_selfAdjoint K hs) u₀ s t z := by
  change (gam (UI L)).symm (propL (UI L) K M A hA.le hK hs u₀.val u₀.property
    (zero_le_one.trans hM) s t (gam (UI L) z)) = _
  have hg : ∀ w, gam (UI L) w = w := fun w => fockMap_refl w
  have hg' : ∀ w, (gam (UI L)).symm w = w := fun w => by
    rw [LinearIsometryEquiv.symm_apply_eq]; exact (hg w).symm
  rw [hg', hg]
  have hBL : BL (UI L) K = positiveExtension K := by
    funext m
    cases m with
    | zero => rfl
    | succ n => exact conjSym_refl_L (n + 1) (K n)
  exact congrArg (fun V : Fock L ≃ₗᵢ[ℂ] Fock L => V z)
    (Prop022BFock2.propagator_congr hBL M A _ hA.le _ _ _ _ _ _ (Subtype.ext rfl) s t)

/-- **`Prop022PairInput` from the general theorem's physical content (fixed implementation).**
(1) the named input `Prop022PairInput` on `L2T L` (the frozen physical form of the printed lemma);
(2) the transported propagator `V_H` of `PROP022_general_infinite_exact` (`H = L2T L`), for every unitary
`U` of `L2T L`, is the fixed `propagator` (exact independence `VH_indep` + `VH_refl_eq`). -/
theorem Prop022PairInput_of_general (K : Kernels (L2T L)) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : Prop001.Sphere (L2T L)) (T P : ℝ) (hP : 1 ≤ P) :
    Prop024WeylConventionR55.Prop022PairInput K M A hM hA hK hs u₀ T P hP ∧
    (∀ (U : L2T L ≃ₗᵢ[ℂ] L2T L) (t s : ℝ) (z : Fock L),
      VH U K M A hA.le hK hs u₀.val u₀.property (zero_le_one.trans hM) t s z =
        propagator (positiveExtension K) M A (zero_le_one.trans hM) hA.le
          (positiveExtension_bound K M A hK) (positiveExtension_selfAdjoint K hs) u₀ s t z) :=
  ⟨Prop022OMain.PROP022_physical_quadratic_propagator K M A hM hA hK hs u₀ T P hP,
    fun U t s z => by
      have h := congrArg (fun V : FockSpace (L2T L) ≃ₗᵢ[ℂ] FockSpace (L2T L) => V z)
        (VH_indep K M A hM hA hK hs u₀.val u₀.property (UI L) U t s)
      rw [h]
      exact VH_refl_eq K M A hM hA hK hs u₀ t s z⟩

#print axioms QuantumNLS.Prop022BPairInput.VH_refl_eq
#print axioms QuantumNLS.Prop022BPairInput.Prop022PairInput_of_general
end QuantumNLS.Prop022BPairInput
