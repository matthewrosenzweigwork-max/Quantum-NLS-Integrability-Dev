import Mathlib
import QuantumNLS.RootHilbertConv
import QuantumNLS.RealFourierInfra

/-!
# R-064239ED: Parseval energy bounds for the truncated Hilbert convolutions

With `Eρ δ := ∫ (2 min(4, 2π|ξ|δ))² |ρ̂(ξ)|² dξ`:
* `energy_diff`: for `0 < a' ≤ a ≤ R`, `Gc a' R - Gc a R ∈ L²` and `∫ ‖Gc a' R - Gc a R‖² ≤ Eρ (a - a')`;
* `energy_Gc`: `∫ ‖Gc a R‖² ≤ 64 ∫ ‖ρ‖²`;
* `tendsto_Eρ`: `Eρ δ → 0` as `δ ↓ 0` (dominated convergence).
Fourier ingredients: convolution theorem (Mathlib), multiplier bounds (`HilbertMultiplier`), Plancherel on `L¹ ∩ L²`
(`RealFourierInfra`).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

open MeasureTheory Set Filter Topology
open scoped FourierTransform ENNReal NNReal Convolution

namespace QuantumNLS.RootHilbert

theorem fourier_sub_pt {f g : ℝ → ℂ} (hf : Integrable f (volume : Measure ℝ))
    (hg : Integrable g (volume : Measure ℝ)) (ξ : ℝ) : 𝓕 (f - g) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  simp only [Real.fourier_eq, Pi.sub_apply, smul_sub]
  exact integral_sub ((Real.fourierIntegral_convergent_iff ξ).2 hf)
    ((Real.fourierIntegral_convergent_iff ξ).2 hg)

theorem integrable_Gc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Integrable (Gc ρ a b) (volume : Measure ℝ) :=
  (integrable_Kc ha).integrable_convolution (ContinuousLinearMap.lsmul ℂ ℂ) (integrable_rhoc hρ)

theorem memLp_Gc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    MemLp (Gc ρ a b) 2 (volume : Measure ℝ) :=
  memLp_two_of_bdd (integrable_Gc hρ ha b) ((∫ y, ρ y) / a) (Eventually.of_forall (norm_Gc_le hρ ha b))

theorem fourier_Gc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {a : ℝ} (ha : 0 < a) (b ξ : ℝ) :
    𝓕 (Gc ρ a b) ξ = 𝓕 (Kc a b) ξ * 𝓕 (rhoc ρ) ξ := by
  have := Real.fourier_smul_convolution_eq (integrable_Kc (b := b) ha) (integrable_rhoc hρ) ξ
  simpa [Gc] using this

theorem continuous_fourier_rhoc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) : Continuous (𝓕 (rhoc ρ)) := by
  have := VectorFourier.fourierIntegral_continuous (e := Real.fourierChar) (μ := (volume : Measure ℝ))
    (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop) (integrable_rhoc hρ)
  exact this

theorem integrable_sq_fourier_rhoc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) :
    Integrable (fun ξ => ‖𝓕 (rhoc ρ) ξ‖ ^ 2) (volume : Measure ℝ) := by
  have h := (QuantumNLS.RealFourier.parseval_L1L2 (integrable_rhoc hρ) (memLp_rhoc hρ)).1
  exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).1 h

/-- The energy `Eρ δ = ∫ (2 min(4, 2π|ξ|δ))² |ρ̂(ξ)|² dξ`. -/
def Eρ (ρ : ℝ → ℝ) (δ : ℝ) : ℝ :=
  ∫ ξ, (2 * min 4 (2 * Real.pi * |ξ| * δ)) ^ 2 * ‖𝓕 (rhoc ρ) ξ‖ ^ 2

theorem integrable_Eρ_integrand {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun ξ => (2 * min 4 (2 * Real.pi * |ξ| * δ)) ^ 2 * ‖𝓕 (rhoc ρ) ξ‖ ^ 2)
      (volume : Measure ℝ) := by
  have hc : Continuous (fun ξ : ℝ => (2 * min 4 (2 * Real.pi * |ξ| * δ)) ^ 2 * ‖𝓕 (rhoc ρ) ξ‖ ^ 2) := by
    have := continuous_fourier_rhoc hρ
    fun_prop
  refine Integrable.mono' ((integrable_sq_fourier_rhoc hρ).const_mul 64) hc.aestronglyMeasurable
    (Eventually.of_forall (fun ξ => ?_))
  have h0 : 0 ≤ min 4 (2 * Real.pi * |ξ| * δ) :=
    le_min (by norm_num) (by positivity)
  have h1 : min 4 (2 * Real.pi * |ξ| * δ) ≤ 4 := min_le_left _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have : (2 * min 4 (2 * Real.pi * |ξ| * δ)) ^ 2 ≤ 64 := by nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

theorem energy_diff {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {a' a R : ℝ} (ha' : 0 < a') (h1 : a' ≤ a)
    (h2 : a ≤ R) :
    Integrable (fun x => ‖Gc ρ a' R x - Gc ρ a R x‖ ^ 2) (volume : Measure ℝ) ∧
      ∫ x, ‖Gc ρ a' R x - Gc ρ a R x‖ ^ 2 ≤ Eρ ρ (a - a') := by
  have ha : 0 < a := lt_of_lt_of_le ha' h1
  have hG1 := integrable_Gc hρ ha' R
  have hG2 := integrable_Gc hρ ha R
  have hD : Integrable (Gc ρ a' R - Gc ρ a R) (volume : Measure ℝ) := hG1.sub hG2
  have hmem : MemLp (Gc ρ a' R - Gc ρ a R) 2 (volume : Measure ℝ) :=
    (memLp_Gc hρ ha' R).sub (memLp_Gc hρ ha R)
  have hsq : Integrable (fun x => ‖Gc ρ a' R x - Gc ρ a R x‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).1 hmem
  refine ⟨hsq, ?_⟩
  obtain ⟨hFmem, hpars⟩ := QuantumNLS.RealFourier.parseval_L1L2 hD hmem
  have hFint : Integrable (fun ξ => ‖𝓕 (Gc ρ a' R - Gc ρ a R) ξ‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hFmem.aestronglyMeasurable).1 hFmem
  have hEint := integrable_Eρ_integrand hρ (sub_nonneg.2 h1)
  have key : ∫ x, ‖Gc ρ a' R x - Gc ρ a R x‖ ^ 2 =
      ∫ ξ, ‖𝓕 (Gc ρ a' R - Gc ρ a R) ξ‖ ^ 2 := by
    rw [hpars]; rfl
  rw [key]
  refine integral_mono hFint hEint (fun ξ => ?_)
  rw [fourier_sub_pt hG1 hG2, fourier_Gc hρ ha' R, fourier_Gc hρ ha R, ← sub_mul, norm_mul, mul_pow]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have := norm_fourier_Kc_sub_le ha' h1 h2 ξ
  have h0 : 0 ≤ ‖𝓕 (Kc a' R) ξ - 𝓕 (Kc a R) ξ‖ := norm_nonneg _
  exact pow_le_pow_left₀ h0 this 2

theorem energy_Gc {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) {a R : ℝ} (ha : 0 < a) (h : a ≤ R) :
    ∫ x, ‖Gc ρ a R x‖ ^ 2 ≤ 64 * ∫ x, ‖rhoc ρ x‖ ^ 2 := by
  have hG := integrable_Gc hρ ha R
  have hmem := memLp_Gc hρ ha R
  obtain ⟨hFmem, hpars⟩ := QuantumNLS.RealFourier.parseval_L1L2 hG hmem
  have hFint : Integrable (fun ξ => ‖𝓕 (Gc ρ a R) ξ‖ ^ 2) (volume : Measure ℝ) :=
    (memLp_two_iff_integrable_sq_norm hFmem.aestronglyMeasurable).1 hFmem
  obtain ⟨-, hpρ⟩ := QuantumNLS.RealFourier.parseval_L1L2 (integrable_rhoc hρ) (memLp_rhoc hρ)
  rw [← hpars, ← hpρ, ← integral_const_mul]
  refine integral_mono hFint ((integrable_sq_fourier_rhoc hρ).const_mul 64) (fun ξ => ?_)
  rw [fourier_Gc hρ ha R, norm_mul, mul_pow]
  have := norm_fourier_Kc_le ha h ξ
  have h0 : 0 ≤ ‖𝓕 (Kc a R) ξ‖ := norm_nonneg _
  have : ‖𝓕 (Kc a R) ξ‖ ^ 2 ≤ 64 := by nlinarith
  exact mul_le_mul_of_nonneg_right this (by positivity)

theorem tendsto_Eρ {ρ : ℝ → ℝ} (hρ : HilbertHyp ρ) : Tendsto (Eρ ρ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlim : Tendsto (fun δ => ∫ ξ, (2 * min 4 (2 * Real.pi * |ξ| * δ)) ^ 2 * ‖𝓕 (rhoc ρ) ξ‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ξ : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ξ => 64 * ‖𝓕 (rhoc ρ) ξ‖ ^ 2) ?_ ?_ ((integrable_sq_fourier_rhoc hρ).const_mul 64) ?_
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact (integrable_Eρ_integrand hρ (le_of_lt hδ)).1
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      refine Eventually.of_forall (fun ξ => ?_)
      have h0 : 0 ≤ min 4 (2 * Real.pi * |ξ| * δ) :=
        le_min (by norm_num) (by have : (0 : ℝ) < δ := hδ; positivity)
      have h1 : min 4 (2 * Real.pi * |ξ| * δ) ≤ 4 := min_le_left _ _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have : (2 * min 4 (2 * Real.pi * |ξ| * δ)) ^ 2 ≤ 64 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · refine Eventually.of_forall (fun ξ => ?_)
      have hc : Continuous (fun δ : ℝ => (2 * min 4 (2 * Real.pi * |ξ| * δ)) ^ 2 * ‖𝓕 (rhoc ρ) ξ‖ ^ 2) := by
        fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
  rw [integral_zero] at hlim
  exact hlim

end QuantumNLS.RootHilbert
