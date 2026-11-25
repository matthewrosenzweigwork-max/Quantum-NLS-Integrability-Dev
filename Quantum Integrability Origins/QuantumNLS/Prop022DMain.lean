import Mathlib
import QuantumNLS.Prop022DNumber
import QuantumNLS.Prop022DCoef
import QuantumNLS.Prop022DQuasi

/-! PROP-022 route A, round 5, stage D4: **`PROP022_general_intrinsic_v2`**.

The round-4 headline `Prop022CMain.PROP022_general_intrinsic` (first conjunct, unchanged) TOGETHER WITH the three
items flagged as open at the end of round 4:

1. **Infinite-dimensional coefficient pairing** (`Prop022DCoef.aSym_rep`, `bSym_rep`): for every unitary
   `U : H ≃ L²(𝕋_L)` and all times, `⟪x^{⊗1}, aSym_t (y^{⊗1})⟫ = ⟪x, a_t y⟫` and
   `⟪x, b_t y⟫ = ⟪y ⊗ x, bSym_t⟫`, with `a_t = aH`, `b_t = bH` the complex-linear / antilinear parts of the Hessian
   `D(∇F)(u_t)`; finite-dimensional `H` and isometry `J`: the frozen `Prop022BCoef.aSymJ_rep`, `bSymJ_rep`.
2. **QF predicate** (`Prop022DQuasi.QFAut`): every `S(t,s)` is a symplectic AUTOMORPHISM (bijective, symplectic,
   `S(t,s) S(s,t) = 1`), the evolved vacuum `V(t,0)Ω` is pure quasifree in the GROUP form of the Bogoliubov
   implementer (`PureQuasifreeG`, which implies the round-4 `PureQuasifreeH`), and the Heisenberg (field) form
   `V⁻¹ (a*(S v) - a(S v)) V = a*(v) - a(v)` holds weakly on the finite-particle core.
3. **`dΓ(1) = N`** (`Prop022DNumber`): `numberBlockE 1 n = n · 1`, sectorwise `dΓ(1) = N` on `Fock(H)`,
   `QRel 1 0 y z ↔ z = N y`, and `numExpH x = ∑ Re⟪x_n, (dΓ(1)x)_n⟫`. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
noncomputable section
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022DMain
open QuantumNLS.TensorCarrier QuantumNLS.Prop022GTensor QuantumNLS.Prop022CCanon QuantumNLS.Prop022CQuad
open QuantumNLS.Prop022CIntrinsic QuantumNLS.Prop022AFock QuantumNLS.Prop022DQuasi
open QuantumNLS.Prop022DNumber
open PhysicalTensor BetheCoefficientTransform
open Prop022GClassical Prop022GLinear Prop022BClass1 Prop022BClass2 Prop022BFock2 Prop022BFock3
open Prop022GAntiHS Ext006PhysicalNormBridge.PairTensor

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **PROP-022 (Q7B:lem:pair, fluctuations.tex:93), round-5 headline.**  The round-4 headline
(`Prop022CMain.PROP022_general_intrinsic`) together with the infinite-dimensional coefficient pairing, the
symplectic-automorphism / group-form quasifree / Heisenberg-form statement, and `dΓ(1) = N`. -/
theorem PROP022_general_intrinsic_v2 [TopologicalSpace.SeparableSpace H] (L : ℝ) [Fact (0 < L)]
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    type_of% (Prop022CMain.PROP022_general_intrinsic L K M A hM hA hK hs u₀ hu₀ T P hP e) ∧
    (¬ FiniteDimensional ℂ H → ∀ U : H ≃ₗᵢ[ℂ] L2T L,
      (∀ (t : ℝ) (x y : H), ⟪powerH 1 x, aSym U K M A hA.le hK hs u₀ hu₀ t (powerH 1 y)⟫_ℂ =
        ⟪x, aH U K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ) ∧
      (∀ (t : ℝ) (x y : H), ⟪x, bH U K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ =
        ⟪htmul y x, twoIso (E := H) (bSym U K M A hA.le hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2)⟫_ℂ) ∧
      (let hM0 : 0 ≤ M := by linarith
       QFAut (VH U K M A hA.le hK hs u₀ hu₀ hM0) (SH U K M A hA.le hK hs u₀ hu₀) (vacH U))) ∧
    (FiniteDimensional ℂ H → ∀ J : H →ₗᵢ[ℂ] L2T L,
      (∀ (t : ℝ) (x y : H), ⟪powerH 1 x, aSymJ J K M A hA hK hs u₀ hu₀ t (powerH 1 y)⟫_ℂ =
        ⟪x, aJ J K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ) ∧
      (∀ (t : ℝ) (x y : H), ⟪x, bJ J K M A hA.le hK hs u₀ hu₀ t y⟫_ℂ =
        ⟪htmul y x, twoIso (E := H) (bSymJ J K M A hA hK hs u₀ hu₀ t : HilbertTensorPower ℂ H 2)⟫_ℂ) ∧
      QFAut (VJ J K M A hM hA hK hs u₀ hu₀) (SJ J K M A hA.le hK hs u₀ hu₀) (vacJ J)) ∧
    ((∀ n : ℕ, numberBlockE (ContinuousLinearMap.id ℂ (SymSector ℂ H 1)) n =
        (n : ℂ) • ContinuousLinearMap.id ℂ (SymSector ℂ H n)) ∧
      (∀ x : FockSpace H, dGammaSeq (ContinuousLinearMap.id ℂ (SymSector ℂ H 1)) x = numSeq x) ∧
      (∀ y z : FockSpace H, QRel (ContinuousLinearMap.id ℂ (SymSector ℂ H 1)) (0 : SymSector ℂ H 2) y z ↔
        ∀ n : ℕ, z n = numSeq y n) ∧
      (∀ x : FockSpace H, numExpH x = ∑' n : ℕ, ENNReal.ofReal
        ((⟪x n, dGammaSeq (ContinuousLinearMap.id ℂ (SymSector ℂ H 1)) x n⟫_ℂ).re))) := by
  refine ⟨Prop022CMain.PROP022_general_intrinsic L K M A hM hA hK hs u₀ hu₀ T P hP e,
    fun _ U => ⟨fun t x y => Prop022DCoef.aSym_rep U K M A hA.le hK hs u₀ hu₀ t x y,
      fun t x y => Prop022DCoef.bSym_rep U K M A hA.le hK hs u₀ hu₀ t x y,
      QFAut_U U K M A hM hA hK hs u₀ hu₀ T P hP e⟩,
    fun _ J => ⟨fun t x y => Prop022BCoef.aSymJ_rep J K M A hM hA hK hs u₀ hu₀ t x y,
      fun t x y => Prop022BCoef.bSymJ_rep J K M A hM hA hK hs u₀ hu₀ t x y,
      QFAut_J J K M A hM hA hK hs u₀ hu₀ T P hP e⟩,
    numberBlockE_one, dGamma_one_eq_number, QRel_one_zero_iff, numExpH_eq_dGamma⟩

end QuantumNLS.Prop022DMain

#print axioms QuantumNLS.Prop022DMain.PROP022_general_intrinsic_v2
