import NlsGge.Birkhoff.F05Identity38i

/-! # F05, file j: the split sub-claim L06.08(b), the finite-gap identification at `m = 2`

User decision D4: for `β = alQ4Beta38 β₀ β₁ β₂` (`β_j > 0`),
1. `γ₂^F = (𝓕⁻¹)_# γ₂ = gammaM38 2 β` (as laws on `SobolevHilbert s`, any `s`);
2. `V₂ = alV2_38 β₁ β₂` on `H¹`;
3. `μ₂ = alQ4Rho38 s β₀ β₁ β₂` on `SobolevHilbert s` and `Z₂ = alQ4Z2_38 β₀ β₁ β₂`.
The weak convergence of the Fourier-truncated Gibbs measures (clause (a) of L06.08, v2 `C:thm:bare`
at `m = 2`) is not part of F05: it belongs with F07.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

namespace NlsGge.Birkhoff

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 NlsGge.SpectralFoundations
  NlsGge.HierarchyRiccati.Core NlsGge.AblowitzLadik Filter Topology
open scoped ENNReal

/-- The coefficient sequence of an element of `SobolevHilbert r`. -/
def coeffSeq38 (r : ℝ) (y : SobolevHilbert r) : ℤ → ℂ :=
  fun n => (show WeightedHilbert (sobolevModeWeight r) from y) n

/-- The realization of the coefficients of `y ∈ H^r` in `H^s` (junk `0` if not in `H^s`). -/
def reSob38 (r s : ℝ) (y : SobolevHilbert r) : SobolevHilbert s :=
  seqRealization38 (sobolevModeWeight s) (coeffSeq38 r y)

theorem measurable_coeffSeq38 (r : ℝ) : Measurable (coeffSeq38 r) := by
  refine measurable_pi_iff.2 fun n => ?_
  exact (continuous_carrierCoe_apply38 r n).measurable

theorem measurable_reSob38 (r s : ℝ) : Measurable (reSob38 r s) :=
  (measurable_seqRealization38 _).comp (measurable_coeffSeq38 r)

theorem sobolevModeWeight_two_sub_one38 :
    sobolevModeWeight ((2 - 1 : ℕ) : ℝ) = sobolevModeWeight 1 := by
  have : ((2 - 1 : ℕ) : ℝ) = 1 := by norm_num
  rw [this]

theorem summable_coeffSeq38 (r : ℝ) (y : SobolevHilbert r) :
    Summable (fun n : ℤ => sobolevModeWeight r n * ‖coeffSeq38 r y n‖ ^ 2) :=
  (weightedHilbert_hasSum (sobolevModeWeight r) (show WeightedHilbert (sobolevModeWeight r) from y)).summable

theorem coeffSeq_reSob38 (r s : ℝ) (y : SobolevHilbert r)
    (hy : Summable (fun n : ℤ => sobolevModeWeight s n * ‖coeffSeq38 r y n‖ ^ 2)) (n : ℤ) :
    coeffSeq38 s (reSob38 r s y) n = coeffSeq38 r y n :=
  seqRealization_apply38 (sobolevModeWeight s) (coeffSeq38 r y) hy n

theorem reSob38_realization (r s : ℝ) (z : ℤ → ℂ)
    (hz : Summable (fun n : ℤ => sobolevModeWeight r n * ‖z n‖ ^ 2)) :
    reSob38 r s (seqRealization38 (sobolevModeWeight r) z) = seqRealization38 (sobolevModeWeight s) z := by
  unfold reSob38
  congr 1
  funext n
  exact seqRealization_apply38 (sobolevModeWeight r) z hz n

/-- `V₂ = alV2` in the coordinates of `H^{(2-1)}`. -/
theorem Vm2_eq_alV2_reSob38 (β₀ β₁ β₂ : ℝ) (u : Hm1 2) :
    Vm38 2 (alQ4Beta38 β₀ β₁ β₂) u = alV2_38 β₁ β₂ (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u) := by
  have hs : Summable (fun n : ℤ => sobolevModeWeight 1 n * ‖coeffSeq38 ((2 - 1 : ℕ) : ℝ) u n‖ ^ 2) := by
    rw [← sobolevModeWeight_two_sub_one38]; exact summable_coeffSeq38 _ u
  have h1 : castDown38 (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u) = u := by
    apply Subtype.ext
    funext n
    show coeffSeq38 1 (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u) n = coeffSeq38 ((2 - 1 : ℕ) : ℝ) u n
    exact coeffSeq_reSob38 _ _ u hs n
  have := Vm2_eq_alV2 β₀ β₁ β₂ (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u)
  rwa [h1] at this

/-- `(μ.map g).withDensity f = (μ.withDensity (f ∘ g)).map g`. -/
theorem withDensity_map38 {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ] (μ : Measure α)
    {g : α → γ} (hg : Measurable g) {f : γ → ℝ≥0∞} (hf : Measurable f) :
    (μ.map g).withDensity f = (μ.withDensity (f ∘ g)).map g := by
  ext A hA
  rw [withDensity_apply _ hA, Measure.map_apply hg hA, withDensity_apply _ (hg hA),
    ← lintegral_indicator hA, lintegral_map (hf.indicator hA) hg, ← lintegral_indicator (hg hA)]
  refine lintegral_congr fun x => ?_
  by_cases hx : g x ∈ A
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ g ⁻¹' A from hx)]; rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ g ⁻¹' A from hx)]


theorem hβ_alQ4Beta38 {β₀ β₁ β₂ : ℝ} (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) :
    ∀ j ≤ 2, 0 < alQ4Beta38 β₀ β₁ β₂ j := by
  intro j hj
  interval_cases j <;> simp [alQ4Beta38, h0, h1, h2]

/-- **L06.08(b), conditional on `B`, `O`** (user decision D4; F05 at `m = 2`).  For
`β = alQ4Beta38 β₀ β₁ β₂` with `β₀, β₁, β₂ > 0` and every real `s`:
1. the pushed Birkhoff Gaussian `γ₂^F = (𝓕⁻¹)_# γ₂`, realized in `H^s`, is `gammaM38 2 β` realized
   in `H^s`;
2. `V₂ = alV2_38 β₁ β₂` (on the `H¹` realization of the coefficients);
3. the finite-gap relative partition function is `Z₂ = alQ4Z2_38 β₀ β₁ β₂`, and the finite-gap law
   `μ₂`, regarded in `H^s`, is `alQ4Rho38 s β₀ β₁ β₂`. -/
theorem L06_08b_38 (B : BirkhoffInput38) (O : OneSmoothingInput38 B) {β₀ β₁ β₂ : ℝ}
    (h0 : 0 < β₀) (h1 : 0 < β₁) (h2 : 0 < β₂) (s : ℝ) :
    (((gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map reflect38).map
        (seqRealization38 (sobolevModeWeight s)) =
      (gammaM38 2 (alQ4Beta38 β₀ β₁ β₂)).map (seqRealization38 (sobolevModeWeight s))) ∧
    (∀ u : Hm1 2, Vm38 2 (alQ4Beta38 β₀ β₁ β₂) u =
      alV2_38 β₁ β₂ (reSob38 ((2 - 1 : ℕ) : ℝ) 1 u)) ∧
    ZM38 B 2 (alQ4Beta38 β₀ β₁ β₂) = alQ4Z2_38 β₀ β₁ β₂ ∧
    (muM38 B 2 (alQ4Beta38 β₀ β₁ β₂)).map (reSob38 ((2 - 1 : ℕ) : ℝ) s) =
      alQ4Rho38 s β₀ β₁ β₂ := by
  set β := alQ4Beta38 β₀ β₁ β₂ with hβdef
  have hβ := hβ_alQ4Beta38 h0 h1 h2
  refine ⟨by rw [gammaM38_map_reflect38], fun u => Vm2_eq_alV2_reSob38 β₀ β₁ β₂ u, ?_⟩
  obtain ⟨-, -, hI, hmu⟩ := F05_identity38 B O (m := 2) (β := β) le_rfl hβ
  rw [gammaFM38_eq_realization] at hI hmu
  have hae := ae_summable38 (m := 2) (β := β) le_rfl (fun j hj => (hβ j hj).le)
    (hβ 0 (Nat.zero_le _)) (hβ 2 le_rfl)
  have hgr := measurable_gaussianRealization38 (m := 2)
  -- the density, in terms of the coefficient sequence
  have hV : ∀ᵐ z ∂(gammaM38 2 β), Vm38 2 β (gaussianRealization38 2 z) =
      alQ4V2Seq38 β₁ β₂ z := by
    filter_upwards [hae] with z hz
    rw [Vm2_eq_alV2_reSob38 β₀ β₁ β₂]
    unfold alQ4V2Seq38 gaussianRealization38
    congr 1
    have hz' : Summable (fun n : ℤ => sobolevModeWeight ((2 - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2) := hz
    exact reSob38_realization _ _ z hz'
  have hZ : ZM38 B 2 β = alQ4Z2_38 β₀ β₁ β₂ := by
    have e : ∫ u, Real.exp (-(Vm38 2 β u)) ∂((gammaM38 2 β).map (gaussianRealization38 2)) =
        ∫ z, Real.exp (-(Vm38 2 β (gaussianRealization38 2 z))) ∂(gammaM38 2 β) :=
      integral_map (f := fun u => Real.exp (-(Vm38 2 β u))) hgr.aemeasurable
        (Real.measurable_exp.comp (continuous_Vm38 le_rfl hβ).measurable.neg).aestronglyMeasurable
    rw [← hI, e]
    unfold alQ4Z2_38
    refine integral_congr_ae ?_
    filter_upwards [hV] with z hz
    rw [hz]
  refine ⟨hZ, ?_⟩
  have hVc := continuous_Vm38 (m := 2) (β := β) le_rfl hβ
  have hf : Measurable (fun u : Hm1 2 =>
      ENNReal.ofReal ((ZM38 B 2 β)⁻¹ * Real.exp (-(Vm38 2 β u)))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp hVc.measurable.neg))
  have hV2 : Measurable (alQ4V2Seq38 β₁ β₂) := measurable_alQ4V2Seq38 β₁ β₂
  have hg2 : Measurable (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (-(alQ4V2Seq38 β₁ β₂ z)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hV2.neg)
  have hZpos := (B.ZM38_pos_le_one (m := 2) (β := β) le_rfl hβ).1
  rw [hmu, withDensity_map38 _ hgr hf, Measure.map_map (measurable_reSob38 _ s) hgr]
  -- density: `f ∘ gr = Z⁻¹ · e^{-V₂(z)}` a.e.
  have hdens : ((fun u : Hm1 2 => ENNReal.ofReal ((ZM38 B 2 β)⁻¹ *
        Real.exp (-(Vm38 2 β u)))) ∘ gaussianRealization38 2) =ᵐ[gammaM38 2 β]
      (ENNReal.ofReal (ZM38 B 2 β)⁻¹ •
        (fun z : ℤ → ℂ => ENNReal.ofReal (Real.exp (-(alQ4V2Seq38 β₁ β₂ z))))) := by
    filter_upwards [hV] with z hz
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [hz, ENNReal.ofReal_mul (inv_nonneg.2 hZpos.le)]
  have hreal : (reSob38 ((2 - 1 : ℕ) : ℝ) s ∘ gaussianRealization38 2) =ᵐ[gammaM38 2 β]
      seqRealization38 (sobolevModeWeight s) := by
    filter_upwards [hae] with z hz
    have hz' : Summable (fun n : ℤ => sobolevModeWeight ((2 - 1 : ℕ) : ℝ) n * ‖z n‖ ^ 2) := hz
    exact reSob38_realization _ s z hz'
  rw [withDensity_congr_ae hdens, withDensity_smul _ hg2, Measure.map_smul]
  unfold alQ4Rho38
  rw [hZ]
  congr 1
  · exact Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le hreal)
  · exact ((measurable_reSob38 _ s).comp hgr).aemeasurable

end NlsGge.Birkhoff
