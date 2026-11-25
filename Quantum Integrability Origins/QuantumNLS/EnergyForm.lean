/-
QuantumNLS.EnergyForm — GENERIC bounded-weight form realization and energy trace norm
(owner: opus_tensor).

Source: DEF-031 (definitions.tex:187) "The additive energy trace norm of a difference D is
‖A_k^{1/2} D A_k^{1/2}‖₁, defined through the corresponding trace-class form realization";
energy_trace.tex:112–118 (`B = A_k^{-1/2} C A_k^{-1/2}`).

GENERIC vs ACTUAL (exact distinction):
* Everything here is for an ARBITRARY bounded weight `W : E →L[ℂ] E` on a complex Hilbert space,
  with explicit hypotheses: `W` injective and with dense range; additionally self-adjoint where
  stated.  The intended ACTUAL instance is `W = A_k^{-1/2}` (the formalization's `EnergyMultiplier`,
  `invCLM` of the kinetic weight).  It is NOT imported here because no stable EnergyMultiplier
  hash was published when this was written.  Hence nothing about the actual `A_k` is claimed.
* "Form realization" of `D` is a bounded `T` with `D = W T W` (i.e. `T = A_k^{1/2} D A_k^{1/2}`).
  Its EXISTENCE is NOT assumed anywhere.  `energyTraceNorm W D` is defined as the infimum of
  `‖T‖₁` over all realizations; it is `⊤` when none exists (`energyTraceNorm_eq_top`).  Existence
  of realizations for the actual source objects (e.g. `ρ ≥ 0` with `Tr(A_k ρ) < ∞`,
  energy_trace.tex:14–25) is a separate obligation, not proved here.

Frozen import, read-only: TraceIdeal TI1 (sha256 7eb19026…26b3), which brings TraceCompact,
FD3 and TC6.
-/
import QuantumNLS.TraceIdeal

open scoped InnerProductSpace ENNReal
open QuantumNLS.TraceClass QuantumNLS.TraceCompact QuantumNLS.TraceIdeal Filter Topology

noncomputable section

namespace QuantumNLS.EnergyForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {W : E →L[ℂ] E}

/-! ## Uniqueness of the form realization -/

omit [CompleteSpace E] in
/-- **Uniqueness.** For injective `W` with dense range, `W T₁ W = W T₂ W` implies `T₁ = T₂`. -/
theorem eq_of_mul_mul_eq (hinj : Function.Injective W) (hdense : DenseRange W)
    {T₁ T₂ : E →L[ℂ] E} (h : W * T₁ * W = W * T₂ * W) : T₁ = T₂ := by
  have h1 : ∀ x, T₁ (W x) = T₂ (W x) := fun x => hinj (by
    have := congrArg (fun S : E →L[ℂ] E => S x) h
    simpa only [ContinuousLinearMap.mul_apply] using this)
  ext y
  exact hdense.induction_on y (isClosed_eq T₁.continuous T₂.continuous) h1

/-! ## The energy trace norm (infimum over realizations; `⊤` if none) -/

/-- `‖W⁻¹ D W⁻¹‖₁` in form-realization sense: the infimum of `‖T‖₁` over all bounded `T` with
`D = W T W`.  No realization is assumed to exist. -/
def energyTraceNorm (W D : E →L[ℂ] E) : ℝ≥0∞ :=
  ⨅ (T : E →L[ℂ] E) (_ : D = W * T * W), traceNorm T

theorem energyTraceNorm_eq (hinj : Function.Injective W) (hdense : DenseRange W)
    {D T : E →L[ℂ] E} (h : D = W * T * W) : energyTraceNorm W D = traceNorm T := by
  refine le_antisymm (iInf₂_le T h) (le_iInf₂ fun T' hT' => ?_)
  rw [eq_of_mul_mul_eq hinj hdense (h.symm.trans hT')]

theorem energyTraceNorm_eq_top {D : E →L[ℂ] E} (hno : ∀ T : E →L[ℂ] E, D ≠ W * T * W) :
    energyTraceNorm W D = ⊤ := by
  simp [energyTraceNorm, hno]

theorem energyTraceNorm_zero (hinj : Function.Injective W) (hdense : DenseRange W) :
    energyTraceNorm W 0 = 0 := by
  rw [energyTraceNorm_eq hinj hdense (T := 0) (by simp)]
  exact (traceNorm_eq_zero_iff 0).mpr rfl

/-- Faithfulness: `energyTraceNorm W D = 0 ↔ D = 0`. -/
theorem energyTraceNorm_eq_zero_iff (hinj : Function.Injective W) (hdense : DenseRange W)
    (D : E →L[ℂ] E) : energyTraceNorm W D = 0 ↔ D = 0 := by
  constructor
  · intro h
    by_cases hex : ∃ T, D = W * T * W
    · obtain ⟨T, hT⟩ := hex
      rw [energyTraceNorm_eq hinj hdense hT, traceNorm_eq_zero_iff] at h
      rw [hT, h]; simp
    · simp only [not_exists] at hex
      rw [energyTraceNorm_eq_top hex] at h
      exact absurd h ENNReal.top_ne_zero
  · rintro rfl
    exact energyTraceNorm_zero hinj hdense

/-- Triangle inequality. -/
theorem energyTraceNorm_add_le (hinj : Function.Injective W) (hdense : DenseRange W)
    (D₁ D₂ : E →L[ℂ] E) :
    energyTraceNorm W (D₁ + D₂) ≤ energyTraceNorm W D₁ + energyTraceNorm W D₂ := by
  by_cases h1 : ∃ T, D₁ = W * T * W
  · by_cases h2 : ∃ T, D₂ = W * T * W
    · obtain ⟨T₁, hT₁⟩ := h1
      obtain ⟨T₂, hT₂⟩ := h2
      have h12 : D₁ + D₂ = W * (T₁ + T₂) * W := by rw [hT₁, hT₂, mul_add, add_mul]
      rw [energyTraceNorm_eq hinj hdense hT₁, energyTraceNorm_eq hinj hdense hT₂,
        energyTraceNorm_eq hinj hdense h12]
      exact traceNorm_add_le _ _
    · simp only [not_exists] at h2
      rw [energyTraceNorm_eq_top h2, add_top]
      exact le_top
  · simp only [not_exists] at h1
    rw [energyTraceNorm_eq_top h1, top_add]
    exact le_top

/-- Homogeneity: `energyTraceNorm W (c • D) = |c| · energyTraceNorm W D`. -/
theorem energyTraceNorm_smul (hinj : Function.Injective W) (hdense : DenseRange W) (c : ℂ)
    (D : E →L[ℂ] E) :
    energyTraceNorm W (c • D) = ENNReal.ofReal ‖c‖ * energyTraceNorm W D := by
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul, energyTraceNorm_zero hinj hdense, norm_zero, ENNReal.ofReal_zero, zero_mul]
  by_cases hex : ∃ T, D = W * T * W
  · obtain ⟨T, hT⟩ := hex
    have hcT : c • D = W * (c • T) * W := by rw [hT, mul_smul_comm, smul_mul_assoc]
    rw [energyTraceNorm_eq hinj hdense hcT, energyTraceNorm_eq hinj hdense hT, traceNorm_smul]
  · simp only [not_exists] at hex
    have hex' : ∀ T, c • D ≠ W * T * W := by
      intro T hT
      apply hex (c⁻¹ • T)
      rw [mul_smul_comm, smul_mul_assoc, ← hT, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [energyTraceNorm_eq_top hex, energyTraceNorm_eq_top hex',
      ENNReal.mul_top (by simpa using norm_pos_iff.mpr hc)]

/-! ## Comparison with the trace norm (DEF-031 interface) -/

/-- **Comparison.** `‖D‖₁ ≤ ‖W‖² · energyTraceNorm W D`. -/
theorem traceNorm_le_energyTraceNorm (hinj : Function.Injective W) (hdense : DenseRange W)
    (D : E →L[ℂ] E) :
    traceNorm D ≤ ENNReal.ofReal (‖W‖ ^ 2) * energyTraceNorm W D := by
  by_cases hex : ∃ T, D = W * T * W
  · obtain ⟨T, hT⟩ := hex
    rw [energyTraceNorm_eq hinj hdense hT]
    exact traceNorm_le_weighted hT
  · simp only [not_exists] at hex
    rw [energyTraceNorm_eq_top hex]
    by_cases hW : ‖W‖ = 0
    · have hW0 : W = 0 := norm_eq_zero.mp hW
      have hall : ∀ x : E, x = 0 := fun x => hinj (by rw [hW0]; simp)
      have hD0 : D = 0 := by ext x; rw [hall (D x)]; simp
      rw [hD0, (traceNorm_eq_zero_iff 0).mpr rfl]
      exact zero_le
    · rw [ENNReal.mul_top (ENNReal.ofReal_pos.mpr
        (pow_pos (lt_of_le_of_ne (norm_nonneg W) (Ne.symm hW)) 2)).ne']
      exact le_top

/-- **Energy-norm convergence implies trace-norm convergence.** -/
theorem tendsto_traceNorm_of_energy (hinj : Function.Injective W) (hdense : DenseRange W)
    {α : Type*} {l : Filter α} {D : E →L[ℂ] E} {DN : α → E →L[ℂ] E}
    (h : Tendsto (fun n => energyTraceNorm W (DN n - D)) l (𝓝 0)) :
    Tendsto (fun n => traceNorm (DN n - D)) l (𝓝 0) := by
  have hc : Tendsto (fun n => ENNReal.ofReal (‖W‖ ^ 2) * energyTraceNorm W (DN n - D)) l
      (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (‖W‖ ^ 2)) h
      (Or.inr ENNReal.ofReal_ne_top)
    rwa [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun n => zero_le)
    fun n => traceNorm_le_energyTraceNorm hinj hdense _

/-! ## Positivity transfers to the realization (self-adjoint weight) -/

/-- If `W` is self-adjoint with dense range and `D = W T W ≥ 0`, then `T ≥ 0`.
(Source: `A_k^{1/2} ρ A_k^{1/2}` is positive for positive `ρ`.) -/
theorem isPositive_of_realization (hsa : IsSelfAdjoint W) (hdense : DenseRange W)
    {D T : E →L[ℂ] E} (hD : D.IsPositive) (h : D = W * T * W) : T.IsPositive := by
  have hW : ∀ x y, ⟪W x, y⟫_ℂ = ⟪x, W y⟫_ℂ := fun x y => by
    rw [← ContinuousLinearMap.adjoint_inner_right, hsa.adjoint_eq]
  have hkey : ∀ x y, ⟪T (W x), W y⟫_ℂ = ⟪D x, y⟫_ℂ := by
    intro x y
    rw [h, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hW]
  have hsym : ∀ u v, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ := by
    intro u v
    refine hdense.induction_on u (p := fun u => ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ)
      (isClosed_eq ((T.continuous.inner continuous_const)) (continuous_id.inner continuous_const))
      fun x => ?_
    refine hdense.induction_on v (p := fun v => ⟪T (W x), v⟫_ℂ = ⟪W x, T v⟫_ℂ)
      (isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner T.continuous))
      fun y => ?_
    rw [hkey, ← inner_conj_symm (W x), hkey, inner_conj_symm]
    exact hD.isSymmetric x y
  rw [ContinuousLinearMap.isPositive_def]
  refine ⟨hsym, fun u => ?_⟩
  refine hdense.induction_on u (p := fun u => 0 ≤ T.reApplyInnerSelf u)
    (isClosed_le continuous_const T.reApplyInnerSelf_continuous) fun x => ?_
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, hkey]
  exact hD.re_inner_nonneg_left x

/-- For positive `D` with a realization, the energy trace norm is the trace of the realization:
`energyTraceNorm W D = Tr(A_k^{1/2} D A_k^{1/2})`. -/
theorem energyTraceNorm_eq_posTrace (hinj : Function.Injective W) (hdense : DenseRange W)
    (hsa : IsSelfAdjoint W) {D T : E →L[ℂ] E} (hD : D.IsPositive) (h : D = W * T * W) :
    energyTraceNorm W D = posTrace T := by
  rw [energyTraceNorm_eq hinj hdense h,
    traceNorm_of_isPositive (isPositive_of_realization hsa hdense hD h)]

/-! ## Non-vacuity of the generic hypotheses -/

/-- `W = id` satisfies all weight hypotheses, and then the energy trace norm is the trace norm. -/
theorem energyTraceNorm_id (D : E →L[ℂ] E) :
    Function.Injective (ContinuousLinearMap.id ℂ E) ∧ DenseRange (ContinuousLinearMap.id ℂ E) ∧
      IsSelfAdjoint (ContinuousLinearMap.id ℂ E) ∧
      energyTraceNorm (ContinuousLinearMap.id ℂ E) D = traceNorm D := by
  have hinj : Function.Injective (ContinuousLinearMap.id ℂ E) := fun x y h => h
  have hdense : DenseRange (ContinuousLinearMap.id ℂ E) :=
    Function.Surjective.denseRange fun x => ⟨x, rfl⟩
  refine ⟨hinj, hdense, ?_, energyTraceNorm_eq hinj hdense (by ext x; rfl)⟩
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_id]

end QuantumNLS.EnergyForm

#print axioms QuantumNLS.EnergyForm.eq_of_mul_mul_eq
#print axioms QuantumNLS.EnergyForm.energyTraceNorm_eq
#print axioms QuantumNLS.EnergyForm.energyTraceNorm_eq_zero_iff
#print axioms QuantumNLS.EnergyForm.energyTraceNorm_add_le
#print axioms QuantumNLS.EnergyForm.energyTraceNorm_smul
#print axioms QuantumNLS.EnergyForm.traceNorm_le_energyTraceNorm
#print axioms QuantumNLS.EnergyForm.tendsto_traceNorm_of_energy
#print axioms QuantumNLS.EnergyForm.isPositive_of_realization
#print axioms QuantumNLS.EnergyForm.energyTraceNorm_eq_posTrace
#print axioms QuantumNLS.EnergyForm.energyTraceNorm_id
