import Mathlib

/-!
# Total variation norm of a difference of finite measures (R-0C33082D, `prop:D05-total-variation`)

`tvNorm μ ν := |μ - ν|(univ)` for the signed measure `μ - ν` (Mathlib's Jordan total variation), the norm `‖σ‖_TV = |σ|(ℝ)` of the source.

* `tvNorm_mutuallySingular`: `μ ⟂ ν` gives `tvNorm μ ν = μ(univ) + ν(univ)` (positive and negative parts of `μ - ν`).
* `tvNorm_le_density`: if `μ = f dm`, `ν = g dm` with `f, g ≥ 0` integrable, then `tvNorm μ ν ≤ ∫ |f - g| dm`.
* `tvNorm_zero_right`: `tvNorm μ 0 = μ(univ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace QuantumNLS.TotalVariation

variable {α : Type*} [MeasurableSpace α]

/-- `‖μ - ν‖_TV = |μ - ν|(univ)`. -/
def tvNorm (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : ℝ≥0∞ :=
  (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ

theorem tvNorm_mutuallySingular (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ ⟂ₘ ν) : tvNorm μ ν = μ Set.univ + ν Set.univ := by
  have hj : (μ.toSignedMeasure - ν.toSignedMeasure).toJordanDecomposition =
      (⟨μ, ν, h⟩ : JordanDecomposition α) :=
    SignedMeasure.toJordanDecomposition_eq rfl
  unfold tvNorm SignedMeasure.totalVariation
  rw [hj]
  simp [Measure.add_apply]

theorem tvNorm_zero_right (μ : Measure α) [IsFiniteMeasure μ] :
    tvNorm μ (0 : Measure α) = μ Set.univ := by
  rw [tvNorm_mutuallySingular μ 0 Measure.MutuallySingular.zero_right]
  simp

theorem tvNorm_le_density {m : Measure α} {f g : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Integrable f m) (hg : Integrable g m) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : μ = m.withDensity (fun x => ENNReal.ofReal (f x)))
    (hν : ν = m.withDensity (fun x => ENNReal.ofReal (g x))) :
    tvNorm μ ν ≤ ENNReal.ofReal (∫ x, |f x - g x| ∂m) := by
  have hfg : Integrable (fun x => |f x - g x|) m := (hf.sub hg).abs
  have hreal : ∀ E : Set α, MeasurableSet E → μ.real E - ν.real E = ∫ x in E, (f x - g x) ∂m := by
    intro E hE
    have h1 : μ.real E = ∫ x in E, f x ∂m := by
      rw [measureReal_def, hμ, withDensity_apply _ hE,
        ← ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Eventually.of_forall fun x => hf0 x)]
      exact ENNReal.toReal_ofReal (integral_nonneg fun x => hf0 x)
    have h2 : ν.real E = ∫ x in E, g x ∂m := by
      rw [measureReal_def, hν, withDensity_apply _ hE,
        ← ofReal_integral_eq_lintegral_ofReal hg.integrableOn (Eventually.of_forall fun x => hg0 x)]
      exact ENNReal.toReal_ofReal (integral_nonneg fun x => hg0 x)
    rw [h1, h2, integral_sub hf.integrableOn hg.integrableOn]
  set M : Measure α := m.withDensity (fun x => ENNReal.ofReal |f x - g x|) with hM
  have hle : (μ.toSignedMeasure - ν.toSignedMeasure).variation ≤ M := by
    refine VectorMeasure.variation_le_of_forall_enorm_le fun E hE => ?_
    rw [Measure.toSignedMeasure_sub_apply hE, hreal E hE, Real.enorm_eq_ofReal_abs, hM,
      withDensity_apply _ hE]
    have hint : IntegrableOn (fun x => |f x - g x|) E m := hfg.integrableOn
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => abs_nonneg _)]
    have hn := norm_integral_le_integral_norm (μ := m.restrict E) (fun x => f x - g x)
    exact ENNReal.ofReal_le_ofReal (by simpa [Real.norm_eq_abs] using hn)
  unfold tvNorm
  rw [SignedMeasure.totalVariation_eq_variation]
  refine le_trans (hle Set.univ) ?_
  rw [hM, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hfg (Eventually.of_forall fun x => abs_nonneg _)]

end QuantumNLS.TotalVariation

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.TotalVariation.tvNorm_mutuallySingular
#print axioms QuantumNLS.TotalVariation.tvNorm_zero_right
#print axioms QuantumNLS.TotalVariation.tvNorm_le_density
