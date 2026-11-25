import QuantumNLS.Prop024QuadraticR134
import QuantumNLS.Prop022DCoef

/-! Q7B:lem:remainder with the quadratic coefficients of the classical
linearization at the displacement point. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 200000
open scoped InnerProductSpace
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

universe uH

namespace QuantumNLS.Prop024FinalR135
open TensorCarrier PhysicalTensor BetheCoefficientTransform
open Prop022GTensor Prop022GClassical Prop022GLinear Prop022GHilbert Prop022AIsoTensor
open Prop022BClass1 Prop022BClass2 Prop022BClass3 Prop022BExist Prop022BFock3 Prop022AFock
open Prop022CQuad Prop022CWeyl Ext006PhysicalNormBridge.PairTensor
open Prop021ManyBodyTransportR132 Prop021MomentsR132 Prop024WickTransportR133 Prop024FinalH1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sector coefficients represent the complex-linear and antilinear
parts of the classical Hessian in the one- and two-particle pairings. -/
def Represents (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2)
    (a₀ b₀ : H →L[ℝ] H) : Prop :=
  (∀ x y, ⟪powerH 1 x, a (powerH 1 y)⟫_ℂ = ⟪x, a₀ y⟫_ℂ) ∧
  (∀ x y, ⟪x, b₀ y⟫_ℂ = ⟪htmul y x, twoIso (E := H) (b : HilbertTensorPower ℂ H 2)⟫_ℂ)

section Coefficients

variable {L : ℝ} [Fact (0 < L)]
variable (J : H →ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hM : 1 ≤ M) (hA : 0 < A)
  (hK : KBound K M A) (hs : KSelfAdj K) (u : H) (hu : ‖u‖ = 1)
include hM

theorem represents_isometry (J' : H →ₗᵢ[ℂ] L2T L) (t : ℝ) :
    Represents (aSymJ J K M A hA hK hs u hu t) (bSymJ J K M A hA hK hs u hu t)
      (aJ J' K M A hA.le hK hs u hu t) (bJ J' K M A hA.le hK hs u hu t) := by
  have hh := hessJ_indep J J' K M A hA.le hK hs
  have hp := profJ_indep J J' K M A hA.le hK hs u hu
  have ha : aJ J' K M A hA.le hK hs u hu t = aJ J K M A hA.le hK hs u hu t := by
    unfold aJ
    rw [hh, hp]
  have hb : bJ J' K M A hA.le hK hs u hu t = bJ J K M A hA.le hK hs u hu t := by
    unfold bJ
    rw [hh, hp]
  rw [ha, hb]
  exact ⟨Prop022BCoef.aSymJ_rep J K M A hM hA hK hs u hu t,
    Prop022BCoef.bSymJ_rep J K M A hM hA hK hs u hu t⟩

/-- The isometric transfer uses the same coefficients as the accepted
unitary form of the quadratic Hamiltonian, at every time. -/
theorem unitary_coefficients (U : H ≃ₗᵢ[ℂ] L2T L) (t : ℝ) :
    aSymJ J K M A hA hK hs u hu t = aSym U K M A hA.le hK hs u hu t ∧
    bSymJ J K M A hA hK hs u hu t = bSym U K M A hA.le hK hs u hu t := by
  have hg : gradJ J K = gradH U K := funext fun v => eq_of_realDual
    ((hasFDerivAt_symbol J K M A hA.le hK hs v).unique
      (symbolH_hasFDerivAt U K M A hA.le hK hs v))
  obtain ⟨h0, hprof⟩ := profJ_spec J K M A hA.le hK hs u hu
  have hp := profH_unique U K M A hA.le hK hs u hu _ h0 (by
    simpa only [hg] using hprof)
  have hh : hessJ J K = hessH U K := by
    funext v
    unfold hessJ hessH
    rw [hg]
  have ha : aJ J K M A hA.le hK hs u hu t = aH U K M A hA.le hK hs u hu t := by
    unfold aJ aH
    rw [hh, hp]
  have hb : bJ J K M A hA.le hK hs u hu t = bH U K M A hA.le hK hs u hu t := by
    unfold bJ bH
    rw [hh, hp]
  have h := represents_isometry J K M A hM hA hK hs u hu J t
  unfold Represents at h
  rw [ha, hb] at h
  exact ⟨Prop022DCoef.aSym_unique U K M A hA.le hK hs u hu t _ h.1,
    Prop022DCoef.bSym_unique U K M A hA.le hK hs u hu t _ h.2⟩

theorem represents_unitary (U : H ≃ₗᵢ[ℂ] L2T L) (t : ℝ) :
    Represents (aSymJ J K M A hA hK hs u hu t) (bSymJ J K M A hA hK hs u hu t)
      (aH U K M A hA.le hK hs u hu t) (bH U K M A hA.le hK hs u hu t) := by
  obtain ⟨ha, hb⟩ := unitary_coefficients J K M A hM hA hK hs u hu U t
  rw [ha, hb]
  exact ⟨Prop022DCoef.aSym_rep U K M A hA.le hK hs u hu t,
    Prop022DCoef.bSym_rep U K M A hA.le hK hs u hu t⟩

end Coefficients

theorem particleNumber_pos {A Q : ℝ} {N : ℕ} (hA : 0 < A) (hQ : 1 ≤ Q)
    (hNQ : 256 * Real.exp 1 * A * Q ≤ N) : 0 < N := by
  have hpos : (0 : ℝ) < 256 * Real.exp 1 * A * Q :=
    mul_pos (mul_pos (mul_pos (by norm_num) (Real.exp_pos 1)) hA) (zero_lt_one.trans_le hQ)
  exact_mod_cast hpos.trans_le hNQ

/-- The degree-two relation and strong conjugation identity of Q7B:lem:remainder. -/
def RemainderAt (K : Kernels H) (M A : ℝ) (u : H)
    (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2) : Prop :=
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

/-- The printed hypotheses determine coefficients before N, Q and the input
Fock vector are chosen. The two chart quantifiers identify their intrinsic
classical meaning. The reference length is fixed internally. -/
def PrintedRemainder : Prop :=
  ∀ (A : ℝ) (hA : 0 < A),
  ∀ (H : Type uH) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H],
  ∀ (K : Kernels H) (M : ℝ) (hM : 1 ≤ M) (hK : KBound K M A) (hs : KSelfAdj K)
    (u : H) (hu : ‖u‖ = 1),
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  ∃ (a : SymSector ℂ H 1 →L[ℂ] SymSector ℂ H 1) (b : SymSector ℂ H 2),
    (∀ J : H →ₗᵢ[ℂ] L2T 1, Represents a b
      (aJ J K M A hA.le hK hs u hu 0) (bJ J K M A hA.le hK hs u hu 0)) ∧
    (∀ U : H ≃ₗᵢ[ℂ] L2T 1, Represents a b
      (aH U K M A hA.le hK hs u hu 0) (bH U K M A hA.le hK hs u hu 0)) ∧
    RemainderAt K M A u a b

/-- PROP-024, with the accepted classical coefficient identification. -/
theorem prop024 : PrintedRemainder.{uH} := by
  intro A hA H _ _ _ _ K M hM hK hs u hu
  let _ : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨J⟩ : Nonempty (H →ₗᵢ[ℂ] L2T 1) := by
    by_cases hH : FiniteDimensional ℂ H
    · exact exists_isometry_fin hH 1
    · obtain ⟨U⟩ := exists_unitary_L2T 1 hH
      exact ⟨U.toLinearIsometry⟩
  refine ⟨aSymJ J K M A hA hK hs u hu 0, bSymJ J K M A hA hK hs u hu 0,
    fun J' => represents_isometry J K M A hM hA hK hs u hu J' 0,
    fun U => represents_unitary J K M A hM hA hK hs u hu U 0, ?_⟩
  intro N Q hQ hNQ x hx
  have hQuad := Prop024QuadraticR134.wick_quadratic J K M A hM hA hK hs u hu N
    (particleNumber_pos hA hQ hNQ) Q x hx
  obtain ⟨W, hW, h⟩ :=
    Prop024GeneralR134.printed_remainder A hA H K M hM hK hs N Q hQ hNQ u hu x hx
  refine ⟨hQuad, W, hW, fun W' hW' => ?_⟩
  obtain ⟨hd, R, hact, hbound⟩ := h W' hW'
  exact ⟨hd, R, by simpa only [QPrint_eq hQuad, lowOrders] using hact, hbound⟩

/-- Forgetting coefficient identification gives exactly the R134 quadratic statement. -/
theorem to_quadraticR134 (h : PrintedRemainder.{uH}) :
    Prop024QuadraticR134.PrintedQuadraticRemainder.{uH} := by
  intro A hA H _ _ _ _ K M hM hK hs u hu
  obtain ⟨a, b, _, _, hRem⟩ := h A hA H K M hM hK hs u hu
  exact ⟨a, b, hRem⟩

/-- The degree-two relation rewrites the same vector into the R134 Wick form. -/
theorem to_wickR134 (h : PrintedRemainder.{uH}) : Prop024GeneralR134.PrintedRemainder.{uH} := by
  intro A hA H _ _ _ _ K M hM hK hs N Q hQ hNQ u hu x hx
  obtain ⟨a, b, hRem⟩ := to_quadraticR134 h A hA H K M hM hK hs u hu
  obtain ⟨hQuad, W, hW, hAction⟩ := hRem N Q hQ hNQ x hx
  refine ⟨W, hW, fun W' hW' => ?_⟩
  obtain ⟨hd, R, hact, hbound⟩ := hAction W' hW'
  exact ⟨hd, R, by simpa only [QPrint_eq hQuad, lowOrders] using hact, hbound⟩

end QuantumNLS.Prop024FinalR135

#print axioms QuantumNLS.Prop024FinalR135.prop024
