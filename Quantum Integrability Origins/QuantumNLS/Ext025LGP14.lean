import Mathlib

/-!
# EXT-025 layer A: contract theorem for FIN-EXT025-GP-14 (REPAIRED text)

Exact source text: `implementation/ops/contracts/OWNER_CONTRACT_REPAIRS_2026-11-16.md`
(sha256 7af859909fd84fa7...; section "FIN-EXT025-GP-14 (corrected)").  The historical
record in FINAL_EXTERNAL_THEOREM_INSTANCES.json (sha256
82876b0400535292c74c814f70269d4dea6778fb05d4d3066b73e8a3d0d13782) is not edited.

* Hypotheses: `(μ, ν)` σ-finite (SFinite) measures on measurable spaces `X`, `Y`.
  * (T) Tonelli branch: `f : X × Y → [0, ∞]` is (AE-)measurable for `μ ⊗ ν`.
  * (F) Fubini branch: `f : X × Y → ℂ` (or a Banach space) is integrable for `μ ⊗ ν`.
* Conclusion (T): `x ↦ ∫⁻ f(x,y) dν` is measurable, and
  `∫⁻ f d(μ⊗ν) = ∫⁻∫⁻ f(x,y) dν dμ`, and symmetrically in `y`.
* Conclusion (F), with section qualifiers: for `μ`-a.e. `x` the section `y ↦ f(x,y)` is
  `ν`-integrable; `x ↦ ∫ f(x,y) dν` is `μ`-integrable; and
  `∫ f d(μ⊗ν) = ∫∫ f(x,y) dν dμ`, and symmetrically.
* Lean reference forms: `MeasureTheory.lintegral_prod`, `integral_prod`,
  `Integrable.prod_right_ae`, `Integrable.integral_prod_left`.

Lean reading of "(AE-)measurable".  The parenthesis is read as two branches of the
Tonelli clause: (T1) `f` measurable, and then the inner integral functions are
measurable; (T2) `f` only `AEMeasurable` for `μ.prod ν`, and then the inner integral
functions are `AEMeasurable` (the word "measurable" in the conclusion cannot be kept
literally in this branch: modifying `f` on a `μ⊗ν`-null set `A × Y` with `A` a
non-measurable subset of a `μ`-null set changes `x ↦ ∫⁻ f(x,y) dν` to a non-measurable
function).  Both branches carry both orders of integration and the section clauses.  The
Fubini clause is for an arbitrary real Banach space (so `ℂ` is the case
`E = ℂ`), with `Integrable` including a.e. strong measurability, exactly as printed.
`SFinite` is the only hypothesis on the measures (`SigmaFinite` implies it).
`HeldGP14Tonelli` is NOT used; no extra measurability or integrability hypothesis is added.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace QuantumNLS.Ext025L

universe u v w

/-- FIN-EXT025-GP-14 (corrected), as one Lean theorem: both Tonelli branches and the
Fubini branch with section qualifiers. -/
theorem contract_GP14 :
    -- (T1) Tonelli, f measurable
    (∀ (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : X × Y → ℝ≥0∞),
      Measurable f →
      (∀ x, Measurable (fun y => f (x, y))) ∧ (∀ y, Measurable (fun x => f (x, y))) ∧
      Measurable (fun x => ∫⁻ y, f (x, y) ∂ν) ∧ Measurable (fun y => ∫⁻ x, f (x, y) ∂μ) ∧
      (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ ∧
      (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν) ∧
    -- (T2) Tonelli, f only AE-measurable for μ ⊗ ν
    (∀ (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : X × Y → ℝ≥0∞),
      AEMeasurable f (μ.prod ν) →
      (∀ᵐ x ∂μ, AEMeasurable (fun y => f (x, y)) ν) ∧
      (∀ᵐ y ∂ν, AEMeasurable (fun x => f (x, y)) μ) ∧
      AEMeasurable (fun x => ∫⁻ y, f (x, y) ∂ν) μ ∧
      AEMeasurable (fun y => ∫⁻ x, f (x, y) ∂μ) ν ∧
      (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ ∧
      (∫⁻ z, f z ∂μ.prod ν) = ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν) ∧
    -- (F) Fubini, f integrable for μ ⊗ ν, with section qualifiers
    (∀ (X : Type u) (Y : Type v) [MeasurableSpace X] [MeasurableSpace Y]
      (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
      (E : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      (f : X × Y → E),
      Integrable f (μ.prod ν) →
      (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν) ∧
      (∀ᵐ y ∂ν, Integrable (fun x => f (x, y)) μ) ∧
      Integrable (fun x => ∫ y, f (x, y) ∂ν) μ ∧
      Integrable (fun y => ∫ x, f (x, y) ∂μ) ν ∧
      (∫ z, f z ∂μ.prod ν) = ∫ x, ∫ y, f (x, y) ∂ν ∂μ ∧
      (∫ z, f z ∂μ.prod ν) = ∫ y, ∫ x, f (x, y) ∂μ ∂ν) := by
  refine ⟨?_, ?_, ?_⟩
  · intro X Y _ _ μ ν _ _ f hf
    exact ⟨fun x => hf.comp (measurable_const.prodMk measurable_id),
      fun y => hf.comp (measurable_id.prodMk measurable_const),
      hf.lintegral_prod_right', hf.lintegral_prod_left',
      lintegral_prod f hf.aemeasurable, lintegral_prod_symm f hf.aemeasurable⟩
  · intro X Y _ _ μ ν _ _ f hf
    have hf' := hf
    obtain ⟨g, hg, hfg⟩ := hf
    have h1 : ∀ᵐ x ∂μ, AEMeasurable (fun y => f (x, y)) ν := by
      filter_upwards [Measure.ae_ae_of_ae_prod hfg] with x hx
      exact ⟨fun y => g (x, y), hg.comp (measurable_const.prodMk measurable_id), hx⟩
    have h2 : ∀ᵐ y ∂ν, AEMeasurable (fun x => f (x, y)) μ := by
      have hs : f ∘ Prod.swap =ᵐ[ν.prod μ] g ∘ Prod.swap := by
        exact (Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae_eq_comp hfg
      filter_upwards [Measure.ae_ae_of_ae_prod hs] with y hy
      exact ⟨fun x => g (x, y), hg.comp (measurable_id.prodMk measurable_const), hy⟩
    exact ⟨h1, h2, hf'.lintegral_prod_right', hf'.lintegral_prod_left',
      lintegral_prod f hf', lintegral_prod_symm f hf'⟩
  · intro X Y _ _ μ ν _ _ E _ _ _ f hf
    exact ⟨hf.prod_right_ae, hf.prod_left_ae, hf.integral_prod_left, hf.integral_prod_right,
      integral_prod f hf, integral_prod_symm f hf⟩

end QuantumNLS.Ext025L

#print axioms QuantumNLS.Ext025L.contract_GP14
