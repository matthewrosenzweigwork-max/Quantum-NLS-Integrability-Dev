import Mathlib
import QuantumNLS.Prop022BCoef

/-! PROP-022 route A, round 5, stage D2: the INFINITE-dimensional coefficient pairing.

Frozen `Prop022AFock.aSym U ... t ∈ B(Sym¹ H)` and `bSym U ... t ∈ Sym² H` (the data of the quadratic
generator `QH`, `U : H ≃ₗᵢ L²(𝕋_L)`) are the back-conjugations of the physical number/pair coefficients.  The
printed `a_t` (complex-linear) and `b_t` (antilinear) are `Prop022GLinear.aH`, `bH`, the complex-linear and
antilinear parts of the Hessian `D(∇F_H)(u_t)` of the actual classical flow.  This module proves, in exactly the
form of the finite-dimensional `Prop022BCoef.aSymJ_rep`, `bSymJ_rep`:

* `aSym_rep`:  `⟪x^{⊗1}, aSym_t (y^{⊗1})⟫ = ⟪x, a_t y⟫`  (all `x, y ∈ H`);
* `bSym_rep`:  `⟪x, b_t y⟫ = ⟪y ⊗ x, bSym_t⟫`  (`⟪htmul y x, twoIso (bSym_t)⟫`, i.e. `b_t` is the antilinear
  operator whose pairing with `x` is the Hilbert tensor `y ⊗ x` against the pair vector `bSym_t ∈ Sym² H`);
* `aSym_unique`, `bSym_unique`: these pairings CHARACTERIZE `aSym_t`, `bSym_t` (any `a'` with the same one-particle
  pairing equals `aSym_t`, any `b' ∈ Sym² H` with the same pair pairing equals `bSym_t`), so the printed
  `a_t`, `b_t` determine the Fock-side coefficient data uniquely.

Both are intrinsic on `H` (no basis, no torus); the physical-carrier pairings `numberOperator_pairing` and the
`bH'_pair` argument of `Prop022BCoef` are the ingredients. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022DCoef
open TensorCarrier PhysicalTensor Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022GLinear
open Prop022GAntiHS Prop022BIso Prop022BCoef Prop022AFock
open Prop022FactorialCoefficientsR115 Prop022ActualProfileR117 Prop022PositiveDataR126
open Prop022PrintedCoefficientsR124 Prop022PairHSR122 Ext006PairDensityR40a Ext006KernelHilbertSchmidt
open Ext006PhysicalNormBridge.PairTensor Prop022TensorCompressionR115 BetheCoefficientTransform Ext025B3PhysicalSectors

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

section Data
variable (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
  (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1)

/-- `a_t` and its Fock-sector representative `aSym_t ∈ B(Sym¹ H)` agree on one-particle vectors. -/
theorem aSym_rep (t : ℝ) (x y : H) :
    ⟪powerH 1 x, aSym U K M A hA hK hs u₀ hu₀ t (powerH 1 y)⟫_ℂ =
      ⟪x, aH U K M A hA hK hs u₀ hu₀ t y⟫_ℂ := by
  rw [aH_eq, inner_pull]
  unfold aSym backConj
  change ⟪powerH 1 x, (symMap U 1).symm (numberCoefficient (BL U K)
    (profile (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t)
    (symMap U 1 (powerH 1 y)))⟫_ℂ = _
  rw [← (symMap U 1).inner_map_map, LinearIsometryEquiv.apply_symm_apply, symMap_powerH,
    symMap_powerH]
  exact (numberOperator_pairing (BL U K) _ (U x) (U y)).symm

/-- `b_t` and its Fock-sector representative `bSym_t ∈ Sym² H`: `⟪x, b_t y⟫ = ⟪y ⊗ x, bSym_t⟫`. -/
theorem bSym_rep (t : ℝ) (x y : H) :
    ⟪x, bH U K M A hA hK hs u₀ hu₀ t y⟫_ℂ =
      ⟪htmul y x, twoIso (E := H) (bSym U K M A hA hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2)⟫_ℂ := by
  rw [bH_eq, inner_pull]
  have h1 : ⟪U x, (PL U K M A hA hK hs u₀ hu₀ t) (U y)⟫_ℂ =
      ⟪htmul (U y) (U x), twoIso (E := L2T L)
        (pairCoefficient (BL U K) (profile (BL U K) M A hA (BL_bound U K M A hK)
          (BL_selfAdj U K hs) (sphL U u₀ hu₀) t) : HilbertTensorPower ℂ (L2T L) 2)⟫_ℂ := by
    change ⟪U x, contract (conjugation (physicalBasis L) (conjugation (physicalBasis L) (U y)))
      (twoIso (E := L2T L) (pairCoefficient (BL U K) (profile (BL U K) M A hA (BL_bound U K M A hK)
          (BL_selfAdj U K hs) (sphL U u₀ hu₀) t) : HilbertTensorPower ℂ (L2T L) 2))⟫_ℂ = _
    rw [conjugation_sq, inner_contract]
  rw [h1]
  have h2 : (pairCoefficient (BL U K) (profile (BL U K) M A hA (BL_bound U K M A hK)
      (BL_selfAdj U K hs) (sphL U u₀ hu₀) t) : HilbertTensorPower ℂ (L2T L) 2) =
      tensorMapI U.toLinearIsometry 2
        (bSym U K M A hA hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2) := by
    rw [tensorMapI_equiv]
    exact (congrArg Subtype.val ((symMap U 2).apply_symm_apply _)).symm
  rw [h2]
  exact inner_twoIso_tensorMapI U.toLinearIsometry x y _


/-- Vectors of the completed tensor square orthogonal to all elementary tensors vanish. -/
lemma eq_zero_of_inner_htmul (d : HilbertTensor ℂ H H) (hd : ∀ x y : H, ⟪htmul y x, d⟫_ℂ = 0) :
    d = 0 := by
  have hdense : Dense (Submodule.span ℂ (Set.range fun p : H × H =>
      (htmul p.1 p.2 : HilbertTensor ℂ H H)) : Set (HilbertTensor ℂ H H)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_htmul_dense
  have hf : (innerSL ℂ d : HilbertTensor ℂ H H →L[ℂ] ℂ) = 0 := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨⟨a, b⟩, rfl⟩
    change ⟪d, htmul a b⟫_ℂ = 0
    rw [← inner_conj_symm, hd b a, map_zero]
  have h := congrArg (fun f : HilbertTensor ℂ H H →L[ℂ] ℂ => f d) hf
  exact inner_self_eq_zero.mp h

/-- **Uniqueness of `bSym`.** The pair vector `bSym_t ∈ Sym² H` is the only vector of `Sym² H` whose pairing with
`y ⊗ x` is `⟪x, b_t y⟫`. -/
theorem bSym_unique (t : ℝ) (b' : SymSector ℂ H 2)
    (h : ∀ x y : H, ⟪x, bH U K M A hA hK hs u₀ hu₀ t y⟫_ℂ =
      ⟪htmul y x, twoIso (E := H) (b' : HilbertTensorPower ℂ H 2)⟫_ℂ) :
    b' = bSym U K M A hA hK hs u₀ hu₀ t := by
  have hd : twoIso (E := H) (b' : HilbertTensorPower ℂ H 2) -
      twoIso (E := H) (bSym U K M A hA hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2) = 0 := by
    apply eq_zero_of_inner_htmul
    intro x y
    rw [inner_sub_right, ← h, ← bSym_rep, sub_self]
  have h1 : (b' : HilbertTensorPower ℂ H 2) =
      (bSym U K M A hA hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2) := by
    apply (twoIso (E := H)).injective
    exact sub_eq_zero.mp hd
  exact Subtype.ext h1

/-- **Uniqueness of `aSym`.** `aSym_t` is the only `a ∈ B(Sym¹ H)` with `⟪x^{⊗1}, a (y^{⊗1})⟫ = ⟪x, a_t y⟫`. -/
theorem aSym_unique (t : ℝ) (a' : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1)
    (h : ∀ x y : H, ⟪powerH 1 x, a' (powerH 1 y)⟫_ℂ = ⟪x, aH U K M A hA hK hs u₀ hu₀ t y⟫_ℂ) :
    a' = aSym U K M A hA hK hs u₀ hu₀ t := by
  have hpow : ∀ g : L2T L, (symMap U 1).symm (power 1 g) = powerH 1 (U.symm g) := by
    intro g
    rw [LinearIsometryEquiv.symm_apply_eq, symMap_powerH, LinearIsometryEquiv.apply_symm_apply]
  have e : ∀ g' : L2T L, power (L := L) 1 g' = symMap U 1 (powerH 1 (U.symm g')) := by
    intro g'
    rw [symMap_powerH, LinearIsometryEquiv.apply_symm_apply]
  have key : ∀ (T : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (g g' : L2T L),
      ⟪power 1 g', conjSym U 1 T (power 1 g)⟫_ℂ =
        ⟪powerH 1 (U.symm g'), T (powerH 1 (U.symm g))⟫_ℂ := by
    intro T g g'
    rw [conjSym_apply, hpow, e g', LinearIsometryEquiv.inner_map_map]
  have hD : conjSym U 1 a' = conjSym U 1 (aSym U K M A hA hK hs u₀ hu₀ t) := by
    apply ContinuousLinearMap.ext_on (Prop022AWeyl.dense_powers (L := L) 1)
    rintro _ ⟨g, rfl⟩
    apply sub_eq_zero.mp
    apply Prop022ACoherent.powers_total
    intro g'
    rw [inner_sub_right, key, key, h, aSym_rep, sub_self]
  ext1 z
  apply (symMap U 1).injective
  have h2 := congrArg (fun T : HN L 1 →L[ℂ] HN L 1 => T (symMap U 1 z)) hD
  simp only [conjSym_apply, LinearIsometryEquiv.symm_apply_apply] at h2
  exact h2

end Data

end QuantumNLS.Prop022DCoef

#print axioms QuantumNLS.Prop022DCoef.aSym_rep
#print axioms QuantumNLS.Prop022DCoef.bSym_rep
#print axioms QuantumNLS.Prop022DCoef.aSym_unique
#print axioms QuantumNLS.Prop022DCoef.bSym_unique
