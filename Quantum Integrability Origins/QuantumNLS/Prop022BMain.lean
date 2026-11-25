import Mathlib
import QuantumNLS.Prop022BClass3
import QuantumNLS.Prop022BIndep
import QuantumNLS.Prop022BExist
import QuantumNLS.Prop022AExact

/-! PROP-022 route A, final stage B5c: **the printed lemma Q7B:lem:pair (fluctuations.tex:93) on an arbitrary
complex separable Hilbert space `H`**, with exactly the printed hypotheses.

`Prop022BMain.PROP022_general` is the conjunction of
* (infinite-dimensional `H`) `Prop022AExact.PROP022_general_infinite_exact`: transport through every unitary
  `U : H ≃ₗᵢ[ℂ] L2T L`, with independence of `U` (exact for `V_H`, `Q_H`, `a_t`, `b_t`; `W_H`, `Ω_H`, QF);
* (finite-dimensional `H`) existence of an isometry `J : H →ₗᵢ[ℂ] L2T L` and, for EVERY isometry `J`, the six printed
  conclusions through `J` (`Prop022BClass3.PROP022_J_classical`, `Prop022BFock3.PROP022_fock_J`) together with the
  independence of `J` (`PROP022_J_indep`).

The hypotheses are those of the printed lemma (complex separable `H`, kernels `B_m` self-adjoint with
`‖B_m‖ ≤ M A^m/√(2m)!`, `M ≥ 1`, `A > 0`, unit `u₀`, the sup bound `P ≥ 1` inside conclusion 3); no further
hypothesis is added. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
open scoped InnerProductSpace Topology NNReal ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022BMain
open PhysicalTensor Prop022GTensor Prop022GAntiHS Prop022GClassical Prop022GLinear
open Prop022BIso Prop022BClass1 Prop022BClass2 Prop022BClass3 Prop022BFock1 Prop022BFock2 Prop022BFock3
open Prop022BIndep Prop022AFock

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- **Independence of the isometric embedding (finite-dimensional `H`).** -/
theorem PROP022_J_indep (hH : FiniteDimensional ℂ H) (J J' : H →ₗᵢ[ℂ] L2T L) (K : Kernels H)
    (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H)
    (hu₀ : ‖u₀‖ = 1) :
    (∀ v, WJ J' v = WJ J v) ∧ vacJ J' = vacJ J ∧
    (∀ t, QFJ J' (VJ J K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J))) ∧
    (∀ t s, VJ J' K M A hM hA hK hs u₀ hu₀ t s = VJ J K M A hM hA hK hs u₀ hu₀ t s) ∧
    (∀ t, aSymJ J' K M A hA hK hs u₀ hu₀ t = aSymJ J K M A hA hK hs u₀ hu₀ t ∧
      bSymJ J' K M A hA hK hs u₀ hu₀ t = bSymJ J K M A hA hK hs u₀ hu₀ t) ∧
    (∀ (a : TensorCarrier.SymSector ℂ H 1 →L[ℂ] TensorCarrier.SymSector ℂ H 1)
      (b : TensorCarrier.SymSector ℂ H 2) (y : FockSpace H), QJ J' a b y = QJ J a b y) := by
  obtain ⟨R, hR⟩ := Prop022BExist.exists_unitary_fixing hH J J'
  exact ⟨fun v => WJ_indep J J' R hR v, vacJ_indep J J' R hR,
    fun t => QFJ_indep J J' R hR K M A hM hA hK hs u₀ hu₀ t,
    fun t s => VJ_indep J J' R hR K M A hM hA hK hs u₀ hu₀ t s,
    fun t => ⟨aSymJ_indep J J' R hR K M A hM hA hK hs u₀ hu₀ t,
      bSymJ_indep J J' R hR K M A hM hA hK hs u₀ hu₀ t⟩,
    fun a b y => QJ_indep J J' R hR a b y⟩

/-- **PROP-022 (Q7B:lem:pair) for an arbitrary complex separable Hilbert space `H`**, exactly the printed
hypotheses.  Infinite-dimensional `H`: `Prop022AExact.PROP022_general_infinite_exact` (transport through every
unitary).  Finite-dimensional `H`: an isometry `J : H → L2T L` exists, and for every such `J` the classical
conclusions 1-3 (`PROP022_J_classical`), the Fock conclusions 4-6 (`PROP022_fock_J`) and the independence of `J`
(`PROP022_J_indep`) hold. -/
theorem PROP022_general [TopologicalSpace.SeparableSpace H] (L : ℝ) [Fact (0 < L)]
    (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (T P : ℝ) (hP : 1 ≤ P) {ι : Type*} (e : HilbertBasis ι ℂ H) :
    (∀ hH : ¬ FiniteDimensional ℂ H,
      type_of% (Prop022AExact.PROP022_general_infinite_exact hH L K M A hM hA hK hs u₀ hu₀ T P hP e)) ∧
    (FiniteDimensional ℂ H →
      Nonempty (H →ₗᵢ[ℂ] L2T L) ∧ ∀ J : H →ₗᵢ[ℂ] L2T L,
        type_of% (PROP022_J_classical J K M A hM hA hK hs u₀ hu₀ T P hP e) ∧
        type_of% (PROP022_fock_J J K M A hM hA hK hs u₀ hu₀ e T P hP) ∧
        (∀ J' : H →ₗᵢ[ℂ] L2T L,
          (∀ v, WJ J' v = WJ J v) ∧ vacJ J' = vacJ J ∧
          (∀ t, QFJ J' (VJ J K M A hM hA hK hs u₀ hu₀ t 0 (vacJ J))) ∧
          (∀ t s, VJ J' K M A hM hA hK hs u₀ hu₀ t s = VJ J K M A hM hA hK hs u₀ hu₀ t s) ∧
          (∀ t, aSymJ J' K M A hA hK hs u₀ hu₀ t = aSymJ J K M A hA hK hs u₀ hu₀ t ∧
            bSymJ J' K M A hA hK hs u₀ hu₀ t = bSymJ J K M A hA hK hs u₀ hu₀ t) ∧
          (∀ (a : TensorCarrier.SymSector ℂ H 1 →L[ℂ] TensorCarrier.SymSector ℂ H 1)
            (b : TensorCarrier.SymSector ℂ H 2) (y : FockSpace H), QJ J' a b y = QJ J a b y))) := by
  refine ⟨fun hH => Prop022AExact.PROP022_general_infinite_exact hH L K M A hM hA hK hs u₀ hu₀ T P hP e,
    fun hH => ⟨Prop022BExist.exists_isometry_fin hH L, fun J => ⟨?_, ?_, fun J' => ?_⟩⟩⟩
  · exact PROP022_J_classical J K M A hM hA hK hs u₀ hu₀ T P hP e
  · exact PROP022_fock_J J K M A hM hA hK hs u₀ hu₀ e T P hP
  · exact PROP022_J_indep hH J J' K M A hM hA hK hs u₀ hu₀

end QuantumNLS.Prop022BMain

#print axioms QuantumNLS.Prop022BMain.PROP022_J_indep
#print axioms QuantumNLS.Prop022BMain.PROP022_general
