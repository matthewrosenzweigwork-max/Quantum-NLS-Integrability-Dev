import NlsGge.Birkhoff.F05Identity38f

/-! # F05, file g: `γ_m^F` is the Gaussian `γ_m` itself, and realization on `H^s`

`𝓕⁻¹ : z ↦ (-z_{-n})` preserves the product Gaussian `γ_m` because the rates `a_{m,n}` are even and
the complex Gaussian is symmetric (`complexGaussian_map_neg`).  This is the content of L06.08(b)(1):
`γ_m^F = gammaM38 m β`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.Ramer.General Filter Topology
open scoped ENNReal

/-- The reflection `z ↦ (-z_{-n})` preserves a product complex Gaussian with even rates. -/
theorem countableComplexGaussian_map_reflect38 (q : ℤ → ℝ) (hq : ∀ n, q (-n) = q n) :
    (countableComplexGaussian q).map reflect38 = countableComplexGaussian q := by
  have h1 := Measure.infinitePi_map_pi (μ := fun n : ℤ => complexGaussian (q n))
    (Y := fun _ : ℤ => ℂ) (f := fun _ (z : ℂ) => -z) (fun _ => measurable_complexNeg)
  have h2 := Measure.infinitePi_map_piCongrLeft (μ := fun n : ℤ => complexGaussian (q n))
    (X := fun _ : ℤ => ℂ) (Equiv.neg ℤ)
  simp only [complexGaussian_map_neg] at h1
  have hq' : (fun i : ℤ => complexGaussian (q ((Equiv.neg ℤ) i))) =
      fun i => complexGaussian (q i) := by
    funext i; simp [hq]
  simp only [hq'] at h2
  have hneg : Measurable (fun (z : ℤ → ℂ) (n : ℤ) => -z n) := by
    refine measurable_pi_iff.2 fun n => ?_
    exact (measurable_pi_apply n).neg
  have hrefl : reflect38 = (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℂ) (Equiv.neg ℤ)) ∘
      (fun (z : ℤ → ℂ) (n : ℤ) => -z n) := by
    funext z n
    simp [reflect38, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  unfold countableComplexGaussian
  rw [hrefl, ← Measure.map_map
    (MeasurableEquiv.piCongrLeft (fun _ : ℤ => ℂ) (Equiv.neg ℤ)).measurable hneg, h1]
  exact h2

theorem measurable_reflect38 : Measurable reflect38 := by
  refine measurable_pi_iff.2 fun n => ?_
  exact (measurable_pi_apply (-n)).neg

theorem gammaM38_map_reflect38 (m : ℕ) (β : ℕ → ℝ) :
    (gammaM38 m β).map reflect38 = gammaM38 m β :=
  countableComplexGaussian_map_reflect38 _ (fun n => finiteHierarchyRate38_neg m β n)

theorem reflect38_reflect38 (z : ℤ → ℂ) : reflect38 (reflect38 z) = z := by
  funext n; simp [reflect38]

section Realization

variable (m : ℕ)

/-- `FinvH ∘ gr = gr ∘ reflect`. -/
theorem FinvH38_gaussianRealization38 (z : ℤ → ℂ) :
    FinvH38 m (gaussianRealization38 m z) = gaussianRealization38 m (reflect38 z) := by
  by_cases hz : Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2)
  · have hz' : Summable (fun n : ℤ => sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖reflect38 z n‖ ^ 2) :=
      (mem_seqSobolev38_iff _ _).1 (reflect38_mem ((mem_seqSobolev38_iff _ _).2 hz))
    apply Subtype.ext
    funext n
    have e1 := seqRealization_apply38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) z hz (-n)
    have e2 := seqRealization_apply38 (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) (reflect38 z) hz' n
    show -(show WeightedHilbert (sobolevModeWeight ((m - 1 : ℕ) : ℝ)) from
        gaussianRealization38 m z) (-n) = _
    unfold gaussianRealization38
    rw [e1]
    exact e2.symm
  · have hz' : ¬ Summable (fun n : ℤ =>
        sobolevModeWeight ((m - 1 : ℕ) : ℝ) n * ‖reflect38 z n‖ ^ 2) := fun h => by
      have := (mem_seqSobolev38_iff _ _).1 (reflect38_mem ((mem_seqSobolev38_iff _ _).2 h))
      rw [reflect38_reflect38] at this
      exact hz this
    unfold gaussianRealization38
    rw [seqRealization_of_not_summable38 _ z hz, seqRealization_of_not_summable38 _ _ hz']
    apply Subtype.ext
    funext n
    show -(0 : ℂ) = 0
    simp

theorem measurable_FinvH38 : Measurable (FinvH38 m) := (continuous_FinvH38 m).measurable

/-- **L06.08(b)(1).** `γ_m^F = (𝓕⁻¹)_# γ_m` is the Gaussian `γ_m` itself (realized in `H^{m-1}`). -/
theorem gammaFM38_eq_realization (β : ℕ → ℝ) :
    gammaFM38 m β = (gammaM38 m β).map (gaussianRealization38 m) := by
  unfold gammaFM38
  rw [Measure.map_map (measurable_FinvH38 m) (measurable_gaussianRealization38)]
  have : FinvH38 m ∘ gaussianRealization38 m = gaussianRealization38 m ∘ reflect38 :=
    funext (FinvH38_gaussianRealization38 m)
  rw [this, ← Measure.map_map (measurable_gaussianRealization38) measurable_reflect38,
    gammaM38_map_reflect38]

end Realization

end NlsGge.Birkhoff
