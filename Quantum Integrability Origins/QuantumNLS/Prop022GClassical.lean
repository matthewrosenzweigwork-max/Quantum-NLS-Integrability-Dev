import Mathlib
import QuantumNLS.Prop022GTensor
import QuantumNLS.Prop022GAntiHS
import QuantumNLS.Prop022PositiveDataR126
import QuantumNLS.Prop022PrintedCoefficientsR124

/-! PROP-022 general-scope transport, stage G3b: the classical side on a general complex
Hilbert space `H` (fluctuations.tex:14-28, 43-53).

Data on `H`: positive-rank kernels `K n = B_{n+1}` on the symmetric sectors `Sym^{n+1} H`
(`TensorCarrier.SymSector ℂ H (n+1)`), self-adjoint, with the printed factorial bound.

* `symbolH K u = ∑_{m≥1} ⟪u^{⊗m}, B_m u^{⊗m}⟫` is defined on `H` with no basis or unitary.
* For a unitary `U : H ≃ₗᵢ[ℂ] L2T L` the kernels are transported by `symMap` (G1):
  `kernelsL U K n = Γ_{n+1}(U) K n Γ_{n+1}(U)⁻¹`; they keep the factorial bound and
  self-adjointness, and `symbolH K = F_L ∘ U` (`symbolH_eq`).
* `gradH U K u := U⁻¹ ∇F_L(U u)` is the intrinsic gradient: `dF_H(u)[h] = 2 Re⟪gradH u, h⟫`
  (`symbolH_hasFDerivAt`); hence it does not depend on `U` (`gradH_indep`).
* `flowH = U⁻¹ Φ_L U` solves `u̇ = -i ∇F_H(u)` and preserves the norm (`flowH_spec`).
* `profH`: the unit-sphere trajectory from `u₀`; it is the UNIQUE unit-norm solution of the
  intrinsic equation (`profH_unique`), hence independent of `U` (`profH_indep`). -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped InnerProductSpace
open ContinuousLinearMap
attribute [local instance 1100] NormedSpace.complexToReal Module.complexToReal
attribute [local instance 2000] InnerProductSpace.complexToReal

namespace QuantumNLS.Prop022GClassical
open TensorCarrier PhysicalTensor BetheCoefficientTransform Prop022GTensor
open Prop022TensorCompressionR115 Prop022FactorialCoefficientsR115 Prop022ActualProfileR117
open Prop022GradientR118 Prop022ClassicalTimeR116 Prop022TensorCalculusR116
open Prop022PositiveDataR126 Prop022ClassicalFlowR126 Prop022FlowDifferentialR126

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {L : ℝ} [Fact (0 < L)]

/-- Positive-rank source kernels on `H`: `K n = B_{n+1}` on `Sym^{n+1} H`. -/
abbrev Kernels (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  ∀ n : ℕ, SymSector ℂ H (n+1) →L[ℂ] SymSector ℂ H (n+1)

/-- `u^{⊗m}` in `Sym^m H`. -/
def powerH (m : ℕ) (u : H) : SymSector ℂ H m := ⟨htpow m u, htpow_mem_symSector m u⟩

/-- **The printed classical Hamiltonian on `H`**, `F(u) = ∑_{m≥1} ⟪u^{⊗m}, B_m u^{⊗m}⟫`
(real part; the summands are real for self-adjoint `B_m`). -/
def symbolH (K : Kernels H) (u : H) : ℝ :=
  ∑' n, (⟪powerH (n+1) u, K n (powerH (n+1) u)⟫_ℂ).re

/-! ### Transport of kernels -/

/-- `Γ_m(U) T Γ_m(U)⁻¹` on the physical sector. -/
def conjSym (U : H ≃ₗᵢ[ℂ] L2T L) (m : ℕ) (T : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    HN L m →L[ℂ] HN L m :=
  (symMap U m).toContinuousLinearEquiv.toContinuousLinearMap ∘L T ∘L
    (symMap U m).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma conjSym_apply (U : H ≃ₗᵢ[ℂ] L2T L) (m : ℕ) (T : SymSector ℂ H m →L[ℂ] SymSector ℂ H m)
    (y : HN L m) : conjSym U m T y = symMap U m (T ((symMap U m).symm y)) := rfl

lemma norm_conjSym_le (U : H ≃ₗᵢ[ℂ] L2T L) (m : ℕ) (T : SymSector ℂ H m →L[ℂ] SymSector ℂ H m) :
    ‖conjSym U m T‖ ≤ ‖T‖ := by
  refine opNorm_le_bound _ (norm_nonneg T) (fun y => ?_)
  rw [conjSym_apply, LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using T.le_opNorm ((symMap U m).symm y)

lemma conjSym_adjoint (U : H ≃ₗᵢ[ℂ] L2T L) (m : ℕ) (T : SymSector ℂ H m →L[ℂ] SymSector ℂ H m)
    (hT : T.adjoint = T) : (conjSym U m T).adjoint = conjSym U m T := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [conjSym_apply, conjSym_apply, LinearIsometryEquiv.inner_map_eq_flip]
  have h := (symMap U m).symm.inner_map_eq_flip x (T ((symMap U m).symm y))
  rw [LinearIsometryEquiv.symm_symm] at h
  rw [← h]
  calc ⟪T ((symMap U m).symm x), (symMap U m).symm y⟫_ℂ
      = ⟪(symMap U m).symm x, T.adjoint ((symMap U m).symm y)⟫_ℂ :=
        (ContinuousLinearMap.adjoint_inner_right T _ _).symm
    _ = _ := by rw [hT]

/-- The transported positive-rank kernels on the physical sectors. -/
def kernelsL (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) : ∀ n, HN L (n+1) →L[ℂ] HN L (n+1) :=
  fun n => conjSym U (n+1) (K n)

/-- The transported full kernel family (rank zero set to zero, as in the frozen torus theorem). -/
def BL (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) : ∀ m, HN L m →L[ℂ] HN L m :=
  positiveExtension (kernelsL U K)

/-- Hypotheses on `H`: the literal factorial bound and self-adjointness. -/
def KBound (K : Kernels H) (M A : ℝ) : Prop :=
  ∀ n, ‖K n‖ ≤ M * A^(n+1) / Real.sqrt ((2*(n+1)).factorial : ℝ)

def KSelfAdj (K : Kernels H) : Prop := ∀ n, (K n).adjoint = K n

lemma BL_bound (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hK : KBound K M A) :
    FactorialBound (BL U K) M A :=
  positiveExtension_bound (kernelsL U K) M A (fun n => (norm_conjSym_le U (n+1) (K n)).trans (hK n))

lemma BL_selfAdj (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (hs : KSelfAdj K) :
    ∀ m, (BL U K m).adjoint = BL U K m :=
  positiveExtension_selfAdjoint (kernelsL U K) (fun n => conjSym_adjoint U (n+1) (K n) (hs n))

lemma symMap_powerH (U : H ≃ₗᵢ[ℂ] L2T L) (m : ℕ) (u : H) :
    symMap U m (powerH m u) = power m (U u) := by
  apply Subtype.ext
  rw [symMap_coe]
  exact tensorMap_htpow U m u

/-- **`F_H = F_L ∘ U`.** -/
theorem symbolH_eq (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (u : H) :
    symbolH K u = classicalSeries (BL U K) (U u) := by
  unfold symbolH classicalSeries
  congr 1
  funext n
  change _ = (⟪power (n+1) (U u), conjSym U (n+1) (K n) (power (n+1) (U u))⟫_ℂ).re
  rw [← symMap_powerH, conjSym_apply, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.inner_map_map]

/-! ### Gradient -/

/-- `h ↦ 2 Re⟪g, h⟫`. -/
def realDual (g : H) : H →L[ℝ] ℝ :=
  (2 : ℝ) • (Complex.reCLM ∘L (innerSL ℂ g).restrictScalars ℝ)

lemma realDual_apply (g h : H) : realDual g h = 2 * (⟪g, h⟫_ℂ).re := rfl

lemma eq_of_realDual {g g' : H} (h : realDual g = realDual g') : g = g' := by
  apply ext_inner_right ℝ
  intro v
  have hv := congrArg (fun D : H →L[ℝ] ℝ => D v) h
  simp only [realDual_apply] at hv
  change (⟪g, v⟫_ℂ).re = (⟪g', v⟫_ℂ).re
  linarith

/-- The unitary as a bounded real-linear map. -/
def UR (U : H ≃ₗᵢ[ℂ] L2T L) : H →L[ℝ] L2T L :=
  U.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

def URinv (U : H ≃ₗᵢ[ℂ] L2T L) : L2T L →L[ℝ] H :=
  U.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ

@[simp] lemma UR_apply (U : H ≃ₗᵢ[ℂ] L2T L) (x : H) : UR U x = U x := rfl
@[simp] lemma URinv_apply (U : H ≃ₗᵢ[ℂ] L2T L) (y : L2T L) : URinv U y = U.symm y := rfl

/-- `∇F_H(u) := U⁻¹ ∇F_L(U u)`; intrinsic by `symbolH_hasFDerivAt` and `gradH_indep`. -/
def gradH (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (u : H) : H :=
  U.symm (gradient (BL U K) (U u))

lemma inner_symm_left (U : H ≃ₗᵢ[ℂ] L2T L) (y : L2T L) (h : H) :
    ⟪U.symm y, h⟫_ℂ = ⟪y, U h⟫_ℂ := by
  rw [← LinearIsometryEquiv.inner_map_map U, LinearIsometryEquiv.apply_symm_apply]

/-- **Intrinsic gradient**: `dF_H(u)[h] = 2 Re⟪∇F_H(u), h⟫` (printed convention). -/
theorem symbolH_hasFDerivAt (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u : H) :
    HasFDerivAt (symbolH K) (realDual (gradH U K u)) u := by
  have hf : symbolH K = fun x => classicalSeries (BL U K) (UR U x) :=
    funext (fun x => symbolH_eq U K x)
  have h1 := classicalSeries_hasFDerivAt (BL U K) (BL_selfAdj U K hs) M A hA
    (BL_bound U K M A hK) (UR U u)
  have hc := h1.comp u (UR U).hasFDerivAt
  have hD : seriesD (BL U K) (UR U u) ∘L UR U = realDual (gradH U K u) := by
    ext h
    rw [ContinuousLinearMap.comp_apply,
      seriesD_eq_gradient (BL U K) (BL_selfAdj U K hs) M A hA (BL_bound U K M A hK),
      realDual_apply, gradH, inner_symm_left]
    all_goals rfl
  rw [hD] at hc
  rw [hf]
  exact hc

/-- The gradient does not depend on the transporting unitary. -/
theorem gradH_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u : H) : gradH U K u = gradH U' K u :=
  eq_of_realDual ((symbolH_hasFDerivAt U K M A hA hK hs u).unique
    (symbolH_hasFDerivAt U' K M A hA hK hs u))

/-! ### The classical flow on `H` -/

/-- `Φ_H(t) = U⁻¹ Φ_L(t) U` (frozen R126 ambient flow for the transported kernels). -/
def flowH (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
    (hs : KSelfAdj K) (t : ℝ) (x : H) : H :=
  U.symm (classicalFlow (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) t (U x))

lemma hasDerivAt_symm (U : H ≃ₗᵢ[ℂ] L2T L) {f : ℝ → L2T L} {f' : L2T L} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun r => U.symm (f r)) (U.symm f') t :=
  (URinv U).hasFDerivAt.comp_hasDerivAt t hf

lemma hasDerivAt_map (U : H ≃ₗᵢ[ℂ] L2T L) {f : ℝ → H} {f' : H} {t : ℝ}
    (hf : HasDerivAt f f' t) : HasDerivAt (fun r => U (f r)) (U f') t :=
  (UR U).hasFDerivAt.comp_hasDerivAt t hf

/-- **`Φ_H` solves `u̇ = -i∇F_H(u)`**, starts at the identity and preserves the norm. -/
theorem flowH_spec (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (x : H) :
    flowH U K M A hA hK hs 0 x = x ∧ ∀ t,
      HasDerivAt (fun r => flowH U K M A hA hK hs r x)
        ((-Complex.I) • gradH U K (flowH U K M A hA hK hs t x)) t ∧
      ‖flowH U K M A hA hK hs t x‖ = ‖x‖ := by
  obtain ⟨h0, ht⟩ := classicalFlow_spec (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (U x)
  refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
  · rw [flowH, h0, LinearIsometryEquiv.symm_apply_apply]
  · have hd := hasDerivAt_symm U (ht t).1
    rw [velocity_eq_neg_I_gradient, map_smul] at hd
    simpa only [flowH, gradH, LinearIsometryEquiv.apply_symm_apply] using hd
  · rw [flowH, LinearIsometryEquiv.norm_map, (ht t).2, LinearIsometryEquiv.norm_map]

/-! ### The trajectory -/

/-- `U u₀` on the physical unit sphere. -/
def sphL (U : H ≃ₗᵢ[ℂ] L2T L) (u₀ : H) (hu₀ : ‖u₀‖ = 1) : Prop001.Sphere (L2T L) :=
  ⟨U u₀, by rw [LinearIsometryEquiv.norm_map]; exact hu₀⟩

/-- The trajectory `u_t` on `H`. -/
def profH (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A) (hK : KBound K M A)
    (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (t : ℝ) : H :=
  U.symm (profile (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) t)

theorem profH_spec (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) :
    profH U K M A hA hK hs u₀ hu₀ 0 = u₀ ∧ ∀ t, ‖profH U K M A hA hK hs u₀ hu₀ t‖ = 1 ∧
      HasDerivAt (profH U K M A hA hK hs u₀ hu₀)
        ((-Complex.I) • gradH U K (profH U K M A hA hK hs u₀ hu₀ t)) t := by
  obtain ⟨h0, -, hn, hd, -⟩ := profile_spec (BL U K) M A hA (BL_bound U K M A hK)
    (BL_selfAdj U K hs) (sphL U u₀ hu₀)
  refine ⟨?_, fun t => ⟨?_, ?_⟩⟩
  · rw [profH, h0]
    exact LinearIsometryEquiv.symm_apply_apply U u₀
  · rw [profH, LinearIsometryEquiv.norm_map, hn t]
  · have h := hasDerivAt_symm U (hd t)
    rw [velocity_eq_neg_I_gradient, map_smul] at h
    rw [show profH U K M A hA hK hs u₀ hu₀ = fun r => U.symm (profile (BL U K) M A hA
      (BL_bound U K M A hK) (BL_selfAdj U K hs) (sphL U u₀ hu₀) r) from rfl]
    simpa only [gradH, LinearIsometryEquiv.apply_symm_apply] using h

/-- **Uniqueness**: the trajectory is the only unit-norm solution of `u̇ = -i∇F_H(u)`,
`u(0) = u₀`. -/
theorem profH_unique (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (γ : ℝ → H)
    (h0 : γ 0 = u₀)
    (hγ : ∀ t, ‖γ t‖ = 1 ∧ HasDerivAt γ ((-Complex.I) • gradH U K (γ t)) t) :
    γ = profH U K M A hA hK hs u₀ hu₀ := by
  have hu := (Prop001.trajectory_spec (classicalData (BL U K) M A hA (BL_bound U K M A hK)
    (BL_selfAdj U K hs)) (sphL U u₀ hu₀)).2.2.2 (fun t => U (γ t))
    (by show U (γ 0) = U u₀; rw [h0]) (fun t => ⟨by rw [LinearIsometryEquiv.norm_map]; exact (hγ t).1, by
      have h := hasDerivAt_map U (hγ t).2
      rw [map_smul, gradH, LinearIsometryEquiv.apply_symm_apply] at h
      exact h⟩)
  funext t
  have ht := congrFun hu t
  change U (γ t) = profile (BL U K) M A hA (BL_bound U K M A hK) (BL_selfAdj U K hs)
    (sphL U u₀ hu₀) t at ht
  rw [profH, ← ht, LinearIsometryEquiv.symm_apply_apply]

/-- The trajectory does not depend on the transporting unitary. -/
theorem profH_indep (U U' : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) :
    profH U K M A hA hK hs u₀ hu₀ = profH U' K M A hA hK hs u₀ hu₀ := by
  obtain ⟨h0, hd⟩ := profH_spec U K M A hA hK hs u₀ hu₀
  apply profH_unique U' K M A hA hK hs u₀ hu₀ _ h0
  intro t
  rw [← gradH_indep U U' K M A hA hK hs]
  exact hd t

/-- `Φ_H(t-s)(u_s) = u_t`. -/
theorem flowH_profH (U : H ≃ₗᵢ[ℂ] L2T L) (K : Kernels H) (M A : ℝ) (hA : 0 ≤ A)
    (hK : KBound K M A) (hs : KSelfAdj K) (u₀ : H) (hu₀ : ‖u₀‖ = 1) (s t : ℝ) :
    flowH U K M A hA hK hs (t - s) (profH U K M A hA hK hs u₀ hu₀ s) =
      profH U K M A hA hK hs u₀ hu₀ t := by
  rw [flowH, profH, LinearIsometryEquiv.apply_symm_apply, classicalFlow_along_profile]
  rfl

end QuantumNLS.Prop022GClassical

#print axioms QuantumNLS.Prop022GClassical.symbolH_eq
#print axioms QuantumNLS.Prop022GClassical.symbolH_hasFDerivAt
#print axioms QuantumNLS.Prop022GClassical.gradH_indep
#print axioms QuantumNLS.Prop022GClassical.flowH_spec
#print axioms QuantumNLS.Prop022GClassical.profH_unique
#print axioms QuantumNLS.Prop022GClassical.profH_indep
#print axioms QuantumNLS.Prop022GClassical.flowH_profH
