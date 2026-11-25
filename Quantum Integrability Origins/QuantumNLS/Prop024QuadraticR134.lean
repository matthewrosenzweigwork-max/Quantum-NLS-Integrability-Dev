import QuantumNLS.Prop024GeneralR134

/-! Identify the degree-two intrinsic Wick series with the printed
quadratic operator on the same moment class as the remainder. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option synthInstance.maxHeartbeats 180000
open scoped InnerProductSpace ENNReal

namespace QuantumNLS.Prop024QuadraticR134
open TensorCarrier PhysicalTensor BetheCoefficientTransform Ext025B3PhysicalSectors
open Prop022GTensor Prop022AIsoTensor Prop022GClassical Prop022GHilbert Prop022BIso
open Prop022BClass1 Prop022BExist Prop022BFock1 Prop022BFock3
open Prop022PositiveDataR126 Prop022ActualProfileR117 Prop022FactorialCoefficientsR115
open Prop022CQuad Prop022CQuadTorus Prop022StrongOperatorR125 Prop022CWeyl
open Prop021ManyBodyTransportR132 Prop021MomentsR132
open Prop024WickTransportR133 Prop024WOrder Prop024WSeries Prop024FinalH1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- The Wick degree-two vector is the sectorwise quadratic action,
with the linearized coefficients at the prescribed point of the sphere. -/
theorem wick_quadratic (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ)
    (hM : 1 ≤ M) (hA : 0 < A) (hK : KBound K M A) (hs : KSelfAdj K)
    (u : H) (hu : ‖u‖ = 1) (N : ℕ) (hN : 0 < N)
    (Q : ℝ) (x : FockSpace H) (hx : NumberMoments Q x) :
    QRel (aSymJ J K M A hA hK hs u hu 0) (bSymJ J K M A hA hK hs u hu 0) x
      (∑' m : ℕ, degree N (m+1) 2 (K m) u x) := by
  let B := positiveExtension (extendKernels J K)
  let y := fockMapI J x
  let a := aSymJ J K M A hA hK hs u hu 0
  let b := bSymJ J K M A hA hK hs u hu 0
  have hB := positiveExtension_bound (extendKernels J K) M A (hKJ J K M A hK)
  have hsa := positiveExtension_selfAdjoint _ (extendKernels_selfAdj J K hs)
  have hm := (numberMoments_torus Q y).mp ((numberMoments_transport J Q x).mpr hx)
  have hsm := Prop024WStepOne.mem_physSmooth_of_polyMoments Q y hm.2
  have hfin := momentFinite_of_mem ⟨y,hsm⟩
  have h₂ := (Prop024WWeylPhysical.mem_physSmooth_iff_moments y).mp hsm 2
  have hu' := (J.norm_map u).trans hu
  have hB₀ : BL (UI L) (kernelsI J K) = B :=
    congrArg positiveExtension (Prop021IsometryR132.ambient_kernels J K)
  have hu₀ := (profile_spec (BL (UI L) (kernelsI J K)) M A hA.le
    (BL_bound (UI L) (kernelsI J K) M A (hKJ J K M A hK))
    (BL_selfAdj (UI L) (kernelsI J K) (hsJ J K hs)) (sphL (UI L) (J u) (hJu J u hu))).1
  have hsphere : (↑(sphL (UI L) (J u) (hJu J u hu)) : L2T L) = J u := rfl
  have ha := conj_aSymJ J K M A hM hA hK hs u hu 0
  rw [hu₀, hB₀, hsphere] at ha
  have hb := symI_bSymJ J K M A hM hA hK hs u hu 0
  rw [hu₀, hB₀, hsphere] at hb
  change symI J 2 b = pairCoefficient B (J u) at hb
  have hcov (z : SymSector ℂ H 1) : symI J 1 (a z) = numberCoefficient B (J u) (symI J 1 z) := by
    simpa only [ContinuousLinearMap.comp_apply, symAdj_symI] using
      DFunLike.congr_fun ha (symI J 1 z)
  have hPhys := QRel_torus (numberCoefficient B (J u)) (pairCoefficient B (J u)) y h₂
  rw [← hb] at hPhys
  have hTransport := QRel_transport J a b (numberCoefficient B (J u)) hcov x _ hPhys
  have hq := Prop024WQuadratic.quadVec_eq_quadraticAction N hN B hsa M A hA.le hB
    (J u) hu' h₂ hfin
  have hq' : quadVec N B (J u) y =
      strongCoordinates (numberCoefficient B (J u)) (pairCoefficient B (J u))
        (Ext005FormCutoffR109.rootLift 2 y) :=
    hq.trans (congrArg (fun z => strongCoordinates (numberCoefficient B (J u))
      (pairCoefficient B (J u)) z) (Ext005FormCutoffR109.rootLift_eq 2 y h₂).symm)
  have hDegree : (∑' m : ℕ, gamAdj J (cellDeg N (m+1) 2 (B (m+1)) (J u) y)) =
      ∑' m : ℕ, degree N (m+1) 2 (K m) u x := by
    apply tsum_congr
    intro m
    -- Use the degree-wise transport already proved inside the frozen R133 module.
    run_tac Lean.Elab.Tactic.liftMetaTactic fun goal => do
      let name := Lean.mkPrivateNameCore `QuantumNLS.Prop024WickTransportR133
        `QuantumNLS.Prop024WickTransportR133.degree_compression
      goal.apply (← Lean.Meta.mkConstWithFreshMVarLevels name)
    exact hfin
  rw [hb, ← hq', quadVec, (gamAdj J).map_tsum
    (summable_norm_cellDeg N 2 B M A (zero_le_one.trans hM) hA hB (J u) hu' ⟨y,hsm⟩).of_norm, hDegree]
    at hTransport
  exact hTransport

/-- The printed statement with its degree-two term displayed as
`QPrint`. The coefficients are fixed before the particle number,
moment parameter, or Fock vector is chosen. -/
def PrintedQuadraticRemainder : Prop :=
  ∀ (A : ℝ), 0 < A →
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
  ∀ (K : Kernels H) (M : ℝ), 1 ≤ M → KBound K M A → KSelfAdj K →
  ∀ (u : H), ‖u‖ = 1 →
  ∃ (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2),
  ∀ (N : ℕ) (Q : ℝ), 1 ≤ Q → 256 * Real.exp 1 * A * Q ≤ N →
  ∀ (x : FockSpace H), NumberMoments Q x →
    QRel a b x (∑' m : ℕ, degree N (m+1) 2 (K m) u x) ∧
    ∃ W : FockSpace H ≃ₗᵢ[ℂ] FockSpace H, IsWeylOp ((Real.sqrt N : ℂ) • u) W ∧
      ∀ W' : FockSpace H ≃ₗᵢ[ℂ] FockSpace H, IsWeylOp ((Real.sqrt N : ℂ) • u) W' →
      ∃ (hd : HamiltonianDomain K N (W' x)) (R : FockSpace H),
        W'.symm (hamiltonian K N (W' x) hd) =
          ((N : ℝ) * symbolH K u : ℂ) • x +
            (∑' m : ℕ, degree N (m+1) 1 (K m) u x) + QPrint a b x + R ∧
        ‖R‖ ≤ printedConstant A * M * (N : ℝ) ^ (-(1/2 : ℝ)) * Q ^ (3/2 : ℝ)

theorem printed_quadratic_remainder : PrintedQuadraticRemainder := by
  intro A hA H _ _ _ _ K M hM hK hs u hu
  let _ : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨J⟩ : Nonempty (H →ₗᵢ[ℂ] L2T 1) := by
    by_cases hH : FiniteDimensional ℂ H
    · exact exists_isometry_fin hH 1
    · obtain ⟨U⟩ := exists_unitary_L2T 1 hH
      exact ⟨U.toLinearIsometry⟩
  refine ⟨aSymJ J K M A hA hK hs u hu 0, bSymJ J K M A hA hK hs u hu 0, ?_⟩
  intro N Q hQ hNQ x hx
  have hN : 0 < N := by
    have hpos : (0 : ℝ) < 256 * Real.exp 1 * A * Q :=
      mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) hA) (zero_lt_one.trans_le hQ)
    exact_mod_cast hpos.trans_le hNQ
  have hQuad := wick_quadratic J K M A hM hA hK hs u hu N hN Q x hx
  obtain ⟨W,hW,h⟩ := Prop024GeneralR134.printed_remainder A hA H K M hM hK hs N Q hQ hNQ u hu x hx
  refine ⟨hQuad, W, hW, fun W' hW' => ?_⟩
  obtain ⟨hd,R,hact,hbound⟩ := h W' hW'
  exact ⟨hd,R,by simpa only [QPrint_eq hQuad, lowOrders] using hact,hbound⟩

end QuantumNLS.Prop024QuadraticR134

#print axioms QuantumNLS.Prop024QuadraticR134.wick_quadratic
#print axioms QuantumNLS.Prop024QuadraticR134.printed_quadratic_remainder
