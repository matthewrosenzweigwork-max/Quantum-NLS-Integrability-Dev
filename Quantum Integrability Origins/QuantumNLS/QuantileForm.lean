import Mathlib
import QuantumNLS.BulkResponseForm
import QuantumNLS.FormCoreCalculus

/-!
# R-8F7E0394 (`F03.tex`, `CC:F03:deterministic`): the quantile transport

Source: the paragraph before `CC:F03:core` ("`h ↦ h∘Q` is an isometric bijection from `L²(μ)` onto `L²(0,1)`") and "Write `𝒟` for the pullback of `𝒟_μ` under the quantile map" (`CC:F03:limit-form`).
Objects: `BulkResponseForm.uI`, `formEnergy`, `quot` (read-only), `QuantileTransport.quantile / qm / map_quantile`, `FormCore.formN` (the `μ`-side form norm).

* `cdf_quantile_eq`: for an atomless probability `σ`, `H(Q(s)) = s` on `(0,1)` (`H` the distribution function).
* `formL2_pull`, `formEnergy_pull`: for measurable `h`, `∫_0^1 h(Q)² dt = ∫ h² dσ` and `formEnergy Q (h∘Q) = E_σ(h)` (the double integral over `(0,1)²` is the image of the double integral over `σ ⊗ σ` under `Q × Q`).
* `ofReal_norm_sq`: `ofReal ‖F‖² = ∫⁻ F² dt` in `L²(0,1)`.
* `formEnergy_congr`: `formEnergy` depends only on a.e. classes of `Q` and `F`.
* `exists_pullback`: (`σ` atomless) every measurable `F` is `h ∘ Q` a.e. with `h = F ∘ H`; `formN σ h = ∫ F² + formEnergy Q F`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal ContDiff Real

noncomputable section

namespace QuantumNLS.QuantileForm

open QuantumNLS.QuantileTransport (quantile qm map_qm map_quantile measurable_qm qm_of_mem le_cdf_quantile
  lt_quantile_iff toReal_Iic_eq_cdf leb01)
open QuantumNLS.BulkResponseForm (formEnergy quot L2Unit)

/-- The Lebesgue measure on `(0,1)` of `BulkResponseForm`. -/
abbrev uI : Measure ℝ := QuantumNLS.BulkResponseForm.unitInterval

instance : IsProbabilityMeasure QuantumNLS.BulkResponseForm.unitInterval :=
  inferInstanceAs (IsProbabilityMeasure leb01)
open QuantumNLS.FormCore (dq formE formL2 formN)

theorem uI_eq : uI = leb01 := rfl

/-! ### `H ∘ Q = id` for an atomless probability -/

theorem cdf_quantile_eq (σ : Measure ℝ) [IsProbabilityMeasure σ] (hna : ∀ x, σ {x} = 0) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) : cdf σ (quantile σ s) = s := by
  refine le_antisymm ?_ (le_cdf_quantile σ hs)
  set y := quantile σ s with hy
  have h1 : (cdf σ).measure {y} = ENNReal.ofReal (cdf σ y - Function.leftLim (cdf σ) y) :=
    StieltjesFunction.measure_singleton (cdf σ) y
  rw [measure_cdf] at h1
  rw [hna y, eq_comm, ENNReal.ofReal_eq_zero] at h1
  have h2 : Function.leftLim (cdf σ) y ≤ s := by
    refine le_of_tendsto ((cdf σ).mono.tendsto_leftLim y) ?_
    refine eventually_nhdsWithin_of_forall fun x hx => ?_
    have hx' : x < quantile σ s := hx
    rw [lt_quantile_iff σ hs, toReal_Iic_eq_cdf] at hx'
    exact hx'.le
  linarith

/-! ### Pullback of the forms -/

theorem formL2_pull (σ : Measure ℝ) [IsProbabilityMeasure σ] {h : ℝ → ℝ} (hh : Measurable h) :
    ∫⁻ t, ENNReal.ofReal (h (qm σ t) ^ 2) ∂leb01 = formL2 σ h := by
  unfold formL2
  conv_rhs => rw [← map_qm σ]
  exact (lintegral_map (ENNReal.measurable_ofReal.comp (hh.pow_const 2)) (measurable_qm σ)).symm

theorem formEnergy_pull (σ : Measure ℝ) [IsProbabilityMeasure σ] {h : ℝ → ℝ} (hh : Measurable h) :
    formEnergy (qm σ) (fun t => h (qm σ t)) = formE σ h := by
  unfold formEnergy formE
  have hQ := measurable_qm σ
  have e : ∀ p : ℝ × ℝ, ENNReal.ofReal ((quot (qm σ) (fun t => h (qm σ t)) p.1 p.2) ^ 2) =
      ENNReal.ofReal (dq h (Prod.map (qm σ) (qm σ) p)) := fun p => by
    simp only [quot, dq, div_pow, Prod.map]
  simp_rw [e]
  have hm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (dq h p) :=
    ENNReal.measurable_ofReal.comp (QuantumNLS.FormCore.measurable_dq hh)
  rw [← lintegral_map hm (hQ.prodMap hQ), ← Measure.map_prod_map _ _ hQ hQ]
  have : uI.map (qm σ) = σ := map_qm σ
  rw [this]

/-! ### The `L²(0,1)` norm -/

theorem ofReal_norm_sq (F : L2Unit) :
    ENNReal.ofReal (‖F‖ ^ 2) = ∫⁻ t, ENNReal.ofReal ((F : ℝ → ℝ) t ^ 2) ∂uI := by
  have h1 : ‖F‖ ^ 2 = ∫ t, (F : ℝ → ℝ) t ^ 2 ∂uI := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [inner, sq]
  rw [h1]
  have hi : Integrable (fun t => (F : ℝ → ℝ) t ^ 2) uI := by
    have := (Lp.memLp F).integrable_sq
    exact this
  rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun t => sq_nonneg _)]

theorem formEnergy_congr {Q Q' F F' : ℝ → ℝ} (hQ : Q =ᵐ[uI] Q') (hF : F =ᵐ[uI] F') :
    formEnergy Q F = formEnergy Q' F' := by
  unfold formEnergy
  refine lintegral_congr_ae ?_
  have h1 : ∀ᵐ p ∂(uI.prod uI), Q p.1 = Q' p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := uI) (ν := uI)).ae hQ
  have h2 : ∀ᵐ p ∂(uI.prod uI), Q p.2 = Q' p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := uI) (ν := uI)).ae hQ
  have h3 : ∀ᵐ p ∂(uI.prod uI), F p.1 = F' p.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := uI) (ν := uI)).ae hF
  have h4 : ∀ᵐ p ∂(uI.prod uI), F p.2 = F' p.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := uI) (ν := uI)).ae hF
  filter_upwards [h1, h2, h3, h4] with p a b c d
  simp [quot, a, b, c, d]

theorem quantile_ae_qm (σ : Measure ℝ) [IsProbabilityMeasure σ] : quantile σ =ᵐ[uI] qm σ := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact (qm_of_mem σ hs).symm

/-! ### Every `L²(0,1)` function is a pullback -/

theorem exists_pullback (σ : Measure ℝ) [IsProbabilityMeasure σ] (hna : ∀ x, σ {x} = 0) (F : ℝ → ℝ)
    (hF : Measurable F) :
    ∃ h : ℝ → ℝ, Measurable h ∧ (∀ t ∈ Ioo (0 : ℝ) 1, h (qm σ t) = F t) := by
  refine ⟨fun x => F (cdf σ x), hF.comp (cdf σ).mono.measurable, fun t ht => ?_⟩
  show F (cdf σ (qm σ t)) = F t
  rw [qm_of_mem σ ht, cdf_quantile_eq σ hna ht]

end QuantumNLS.QuantileForm

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.QuantileForm.cdf_quantile_eq
#print axioms QuantumNLS.QuantileForm.formEnergy_pull
#print axioms QuantumNLS.QuantileForm.ofReal_norm_sq
#print axioms QuantumNLS.QuantileForm.formEnergy_congr
#print axioms QuantumNLS.QuantileForm.exists_pullback
