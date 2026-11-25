import QuantumNLS.Prop021GeneralR134
import QuantumNLS.Prop024FinalR135
import QuantumNLS.Prop022DMain

/-! Bind Q7B:thm:main to the accepted quadratic propagator and to the
exact intrinsic statement of Q7B:lem:remainder. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace ENNReal
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

universe uH

namespace QuantumNLS.Prop021FinalR135
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022GClassical Prop022GLinear Prop022GHilbert Prop022AIsoTensor
open Prop022BClass1 Prop022BClass2 Prop022BExist Prop022BFock1 Prop022BFock2 Prop022BFock3
open Prop022AFock Prop022CWeyl Prop022PositiveDataR126 Prop022OVacuum
open Prop021ManyBodyTransportR132 Prop021MarginalTransportR132 Prop021MomentsR132
open Prop021StatementR132 Prop021UnitaryR132 Prop024FinalR135
open Prop024FinalH1 (printedConstant printedConstant_nonneg)

variable {L : ℝ} [Fact (0 < L)]

private theorem pair_family : Prop021AssemblyR131.Prop022PairFamily (L := L) := by
  intro A M hA hM K hK hs u₀ T P hP
  exact (Prop022BPairInput.Prop022PairInput_of_general K M A hM hA hK hs u₀ T P hP).1

/-- Recover the strong action needed for the Duhamel estimate by applying
the intrinsic remainder to the torus and moving its Weyl unitary to the right. -/
theorem remainder_torus (hRem : PrintedRemainder.{0}) (A : ℝ) (hA : 0 < A) :
    Prop021RemainderInputR131.RemainderEstimate (L := L) A (printedConstant A) := by
  intro B M hM hB hs N Q hQ hNQ u hu x hx
  let _ : TopologicalSpace.SeparableSpace (L2T L) := Prop022BExist.sep
  let J := (UI L).toLinearIsometry
  let K : Kernels (L2T L) := fun n => B (n+1)
  have hK : KBound K M A := fun n => hB (n+1) (Nat.succ_pos n)
  have hsK : KSelfAdj K := fun n => hs (n+1)
  have hm := (numberMoments_torus Q x).mpr hx
  have hSmooth := Prop021RemainderInputR131.smooth_of_numberMoments Q x hx
  have h₂ := (Prop021DisplacementR129.common_domain x).mp hSmooth 2
  have huJ : J u = u := rfl
  have hMap (y : Fock L) : fockMapI J y = y :=
    (fockMapI_equiv (UI L) y).trans (gam_refl y)
  have hAdj (y : Fock L) : gamAdj J y = y := by
    simpa only [hMap] using gamAdj_gam J y
  have hExtend : extendKernels J K = K := by
    funext n
    apply ContinuousLinearMap.ext
    intro y
    have hId (z : HN L (n+1)) : symMapI J (n+1) z = z :=
      (symMapI_unitary (UI L) (n+1) z).trans (symMap_refl (n+1) z)
    calc
      extendKernels J K n y = extendKernels J K n (symMapI J (n+1) y) :=
        congrArg (extendKernels J K n) (hId y).symm
      _ = symMapI J (n+1) (K n y) := extend_apply_image _ _ _
      _ = K n y := hId _
  have hLow := Prop024WickTransportR133.lowOrders_eq_compression J K N
    (particleNumber_pos hA hQ hNQ) u hu x Q M A (zero_le_one.trans hM) hA hQ hK hsK hm
  have hLow' : Prop021RemainderInputR131.lowOrders B N u x hSmooth h₂ =
      Prop024WickTransportR133.lowOrders K N u x := by
    have hPositive : Prop021RemainderInputR131.lowOrders (positiveExtension K) N u x hSmooth h₂ =
        Prop024WickTransportR133.lowOrders K N u x := by
      simpa only [Prop021ContractsR132.lowOrders, hExtend, hMap, hAdj, huJ] using hLow
    exact hPositive
  let v := (Real.sqrt N : ℂ) • u
  let W := printedWeyl v
  have hWJ : WJ J v = W := by
    apply LinearIsometryEquiv.ext
    intro y
    have h := gam_compress J W (Weyl_commutes J v) y
    change fockMapI J (WJ J v y) = W (fockMapI J y) at h
    simpa only [hMap] using h
  have hW : IsWeylOp v W := hWJ ▸ WJ_isWeylOp J v
  obtain ⟨_, _, hAction⟩ :=
    to_wickR134 hRem A hA (L2T L) K M hM hK hsK N Q hQ hNQ u hu x hm
  obtain ⟨hd, R, hact, hbound⟩ := hAction W hW
  refine ⟨hSmooth, h₂, (Prop024TransferR133.torus_domain K N (W x)).mpr hd, R, ?_, hbound⟩
  rw [← hLow'] at hact
  have h := congrArg (fun z : Fock L => W z) hact
  change W (W.symm (hamiltonian K N (W x) hd)) =
    W (Prop021RemainderInputR131.lowOrders B N u x hSmooth h₂ + R) at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact (Prop024TransferR133.torus_action K N (W x) hd).trans h

/-- Identify the very coefficients used in the R134 intrinsic evolution
with the classical linearization along the same trajectory. -/
def LinearizationAt {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (J : H →ₗᵢ[ℂ] L2T L) (A : ℝ) (hA : 0 < A) : Prop :=
  ∀ (K : Kernels H) (M : ℝ), 1 ≤ M → ∀ (hK : KBound K M A) (hs : KSelfAdj K)
    (u₀ : H) (hu₀ : ‖u₀‖ = 1) (t : ℝ),
    let a := aSymJ J K M A hA hK hs u₀ hu₀ t
    let b := bSymJ J K M A hA hK hs u₀ hu₀ t
    Represents a b (aJ J K M A hA.le hK hs u₀ hu₀ t) (bJ J K M A hA.le hK hs u₀ hu₀ t) ∧
    ∀ U : H ≃ₗᵢ[ℂ] L2T L,
      Represents a b (aH U K M A hA.le hK hs u₀ hu₀ t) (bH U K M A hA.le hK hs u₀ hu₀ t)

private theorem linearization {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (J : H →ₗᵢ[ℂ] L2T L) (A : ℝ) (hA : 0 < A) : LinearizationAt J A hA := by
  intro K M hM hK hs u₀ hu₀ t
  have hAccepted := Prop022DMain.PROP022_general_intrinsic_v2 L K M A hM hA hK hs u₀ hu₀
    0 1 le_rfl (TraceClass.refBasis H)
  refine ⟨?_, fun U => ?_⟩
  · by_cases hFin : FiniteDimensional ℂ H
    · obtain ⟨ha, hb, _⟩ := hAccepted.2.2.1 hFin J
      exact ⟨ha t, hb t⟩
    · exact represents_isometry J K M A hM hA hK hs u₀ hu₀ J t
  · have hInf : ¬ FiniteDimensional ℂ H := by
      intro hFin
      let _ : FiniteDimensional ℂ H := hFin
      exact L2T_not_finiteDimensional L
        (FiniteDimensional.of_injective U.symm.toLinearEquiv.toLinearMap U.symm.injective)
    obtain ⟨ha, hb⟩ := unitary_coefficients J K M A hM hA hK hs u₀ hu₀ U t
    obtain ⟨hARep, hBRep, _⟩ := hAccepted.2.1 hInf U
    change Represents (aSymJ J K M A hA hK hs u₀ hu₀ t) (bSymJ J K M A hA hK hs u₀ hu₀ t)
      (aH U K M A hA.le hK hs u₀ hu₀ t) (bH U K M A hA.le hK hs u₀ hu₀ t)
    rw [ha, hb]
    exact ⟨hARep t, hBRep t⟩

/-- The printed bounds with the intrinsic R134 evolution and its identified
classical coefficients. Constants are uniform over separable carriers. -/
def Conclusion (L : ℝ) [Fact (0 < L)] : Prop :=
  ∀ (A : ℝ) (hA : 0 < A), ∃ cA : ℝ, ∀ T : ℝ, 0 < T → ∃ CAT : ℝ,
  ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
    Nonempty (H →ₗᵢ[ℂ] L2T L) ∧
    ∀ J : H →ₗᵢ[ℂ] L2T L, Prop021GeneralR134.AtConstants J A hA cA T CAT ∧ LinearizationAt J A hA

/-- The estimates in any positive-length reference chart. -/
theorem prop021_in_chart (hRem : PrintedRemainder.{0}) : Conclusion.{uH} L := by
  have hPair := pair_family (L := L)
  have hPhysical : Prop021RemainderInputR131.Prop024RemainderInput (L := L) :=
    fun A hA => ⟨printedConstant A, printedConstant_nonneg A, remainder_torus hRem A hA⟩
  have hTorus := (torus_statement (L := L)).mpr (Prop021AssemblyR131.prop021 hPair hPhysical)
  intro A hA
  obtain ⟨cA, hcA⟩ := hTorus A hA
  obtain ⟨C, hC, hRemA⟩ := hPhysical A hA
  let cutoff := 256 * Real.exp 1 * A
  refine ⟨max cA cutoff, fun T hT => ?_⟩
  obtain ⟨CAT, hCAT⟩ := hcA T hT
  let estimate := max CAT (T*C)
  have h : TorusAtConstants (L := L) A hA (max cA cutoff) T estimate := by
    -- Reuse the constant enlargement from the pinned R134 proof.
    run_tac Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let name := Lean.mkPrivateNameCore `QuantumNLS.Prop021GeneralR134
        `QuantumNLS.Prop021GeneralR134.enlarge_constants
      goal.apply (← Lean.Meta.mkConstWithFreshMVarLevels name)
    exact le_max_left cA cutoff
    exact le_max_left CAT (T*C)
    exact hCAT
  refine ⟨estimate, fun H _ _ _ _ => ⟨?_, fun J => ⟨?_, linearization J A hA⟩⟩⟩
  · by_cases hH : FiniteDimensional ℂ H
    · exact exists_isometry_fin hH L
    · obtain ⟨U⟩ := exists_unitary_L2T L hH
      exact ⟨U.toLinearIsometry⟩
  · -- Reuse the intrinsic R134 transfer, with the newly derived remainder.
    run_tac Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let name := Lean.mkPrivateNameCore `QuantumNLS.Prop021GeneralR134
        `QuantumNLS.Prop021GeneralR134.transfer_at_constants
      goal.apply (← Lean.Meta.mkConstWithFreshMVarLevels name)
    exact hT
    exact hC
    exact le_max_right cA cutoff
    exact le_max_right CAT (T*C)
    exact h
    exact hPair
    exact hRemA

/-- The printed conclusion, with the reference length chosen internally. -/
def PrintedConclusion : Prop :=
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  Conclusion.{uH} 1

/-- PROP-021 with the exact Q7B:lem:remainder as its sole named input,
specialized in the proof to the reference Hilbert space. -/
theorem prop021 (hRem : PrintedRemainder.{0}) : PrintedConclusion.{uH} := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  exact prop021_in_chart.{uH} (L := 1) hRem

theorem prop021_final : PrintedConclusion.{uH} := prop021 Prop024FinalR135.prop024

/-- The full R134 conclusion at the same constants and on the same charts. -/
theorem to_r134 (h : Conclusion.{uH} L) : Prop021GeneralR134.Prop021.{uH} L := by
  intro A hA
  obtain ⟨cA, hcA⟩ := h A hA
  refine ⟨cA, fun T hT => ?_⟩
  obtain ⟨CAT, hCAT⟩ := hcA T hT
  refine ⟨CAT, fun H _ _ _ _ => ?_⟩
  obtain ⟨hJ, hAt⟩ := hCAT H
  exact ⟨hJ, fun J => (hAt J).1⟩

end QuantumNLS.Prop021FinalR135

#print axioms QuantumNLS.Prop021FinalR135.prop021
#print axioms QuantumNLS.Prop021FinalR135.prop021_final
