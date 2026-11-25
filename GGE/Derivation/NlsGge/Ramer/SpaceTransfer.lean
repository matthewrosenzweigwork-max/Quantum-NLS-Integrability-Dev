import NlsGge.Ramer.RamerDensity

/-!
# Transfer layer between `(ℤ → ℂ, γ)` and `(E_s, γ_E)` (plan target R0)

`coordE : E_s → (ℤ → ℂ)` sends a vector to its coordinate sequence.  Then
`R ∘ coordE = id`, `coordE ∘ R = id` `γ`-a.s., `R_* γ = γ_E` and `(coordE)_* γ_E = γ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace NlsGge.Ramer

open NlsGge.Pilot NlsGge.Analysis.RegularizedDeterminant

variable {lower upper : ℝ}

/-- Coordinates of a vector of `E_s`. -/
def coordE (c : BoundedCoefficients lower upper) (s : ℝ) :
    FullWeightedHilbert c s → (ℤ → ℂ) :=
  fun x n => (show WeightedHilbert (fullModeWeight c s) from x) n

theorem coordE_apply (c : BoundedCoefficients lower upper) (s : ℝ)
    (x : FullWeightedHilbert c s) (n : ℤ) :
    coordE c s x n = (show WeightedHilbert (fullModeWeight c s) from x) n := rfl

theorem continuous_coordE_apply (c : BoundedCoefficients lower upper) (s : ℝ) (n : ℤ) :
    Continuous (fun x : FullWeightedHilbert c s => coordE c s x n) := by
  have h : ∀ x : FullWeightedHilbert c s, coordE c s x n =
      (weightedIsometry (fullModeWeight c s)
        (show WeightedHilbert (fullModeWeight c s) from x) n) /
        (Real.sqrt (fullModeWeight c s n) : ℂ) := by
    intro x
    have hne := weightSqrt_ne_zero (fullModeWeight c s) n
    rw [weightedIsometry_apply, coordE_apply]
    unfold weightedCoordinates
    field_simp
  simp_rw [h]
  have h1 : Continuous (fun x : FullWeightedHilbert c s =>
      weightedIsometry (fullModeWeight c s)
        (show WeightedHilbert (fullModeWeight c s) from x)) :=
    (weightedIsometry (fullModeWeight c s)).continuous
  have h2 : Continuous (fun y : lp (fun _ : ℤ => ℂ) 2 => (y : ℤ → ℂ) n) :=
    (LipschitzWith.of_dist_le_mul (K := 1) (fun a b => by
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      have := lp.norm_apply_le_norm (p := (2 : ENNReal)) (by norm_num) (a - b) n
      simpa using this)).continuous
  exact (h2.comp h1).div_const _

theorem measurable_coordE (c : BoundedCoefficients lower upper) (s : ℝ) :
    Measurable (coordE c s) :=
  measurable_pi_iff.mpr fun n => (continuous_coordE_apply c s n).measurable

theorem weightedSquareSummable_coordE (c : BoundedCoefficients lower upper) (s : ℝ)
    (x : FullWeightedHilbert c s) :
    WeightedSquareSummable (sourceRate c) s (coordE c s x) :=
  (fullWeightedHilbert_membership_iff c s _).1
    (show WeightedHilbert (fullModeWeight c s) from x).2

theorem realization_coordE (c : BoundedCoefficients lower upper) (s : ℝ)
    (x : FullWeightedHilbert c s) :
    NlsGge.Measure.fullWeightedSequenceRealization c s (coordE c s x) = x := by
  have hz := weightedSquareSummable_coordE c s x
  apply Subtype.ext
  funext n
  exact NlsGge.Measure.fullWeightedSequenceRealization_apply c s _ hz n

theorem coordE_realization_ae (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    ∀ᵐ z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val,
      coordE c s (NlsGge.Measure.fullWeightedSequenceRealization c s z) = z := by
  filter_upwards [NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs] with z hz
  funext n
  exact hz n

theorem measurePreserving_realization (c : BoundedCoefficients lower upper) (s : ℝ) :
    MeasurePreserving (NlsGge.Measure.fullWeightedSequenceRealization c s)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
  ⟨NlsGge.Measure.measurable_fullWeightedSequenceRealization c s, rfl⟩

theorem measurePreserving_coordE (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    MeasurePreserving (coordE c s) (NlsGge.Measure.fullWeightedSequenceGaussian c s)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
  refine ⟨measurable_coordE c s, ?_⟩
  unfold NlsGge.Measure.fullWeightedSequenceGaussian
  rw [Measure.map_map (measurable_coordE c s)
    (NlsGge.Measure.measurable_fullWeightedSequenceRealization c s)]
  have : Measure.map (coordE c s ∘ NlsGge.Measure.fullWeightedSequenceRealization c s)
      (NlsGge.Measure.fullWeightSequenceGaussian c.val) =
      Measure.map id (NlsGge.Measure.fullWeightSequenceGaussian c.val) :=
    Measure.map_congr (coordE_realization_ae c s hs)
  rw [this, Measure.map_id]

theorem ae_of_ae_coordE (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) {P : (ℤ → ℂ) → Prop}
    (h : ∀ᵐ z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val, P z) :
    ∀ᵐ x ∂NlsGge.Measure.fullWeightedSequenceGaussian c s, P (coordE c s x) :=
  (measurePreserving_coordE c s hs).quasiMeasurePreserving.ae h

theorem integral_comp_coordE (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) {f : (ℤ → ℂ) → ℝ}
    (hf : AEStronglyMeasurable f (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :
    ∫ x, f (coordE c s x) ∂NlsGge.Measure.fullWeightedSequenceGaussian c s =
      ∫ z, f z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val := by
  have := (measurePreserving_coordE c s hs).map_eq
  rw [← this] at hf ⊢
  rw [integral_map (measurable_coordE c s).aemeasurable hf]

theorem lintegral_comp_coordE (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) {f : (ℤ → ℂ) → ℝ≥0∞}
    (hf : AEMeasurable f (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :
    ∫⁻ x, f (coordE c s x) ∂NlsGge.Measure.fullWeightedSequenceGaussian c s =
      ∫⁻ z, f z ∂NlsGge.Measure.fullWeightSequenceGaussian c.val := by
  have := (measurePreserving_coordE c s hs).map_eq
  rw [← this] at hf ⊢
  rw [lintegral_map' hf (measurable_coordE c s).aemeasurable]

theorem tendstoInMeasure_comp_coordE (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) {ι : Type*} {l : Filter ι} {E : Type*} [PseudoEMetricSpace E]
    {f : ι → (ℤ → ℂ) → E} {g : (ℤ → ℂ) → E}
    (h : TendstoInMeasure (NlsGge.Measure.fullWeightSequenceGaussian c.val) f l g) :
    TendstoInMeasure (NlsGge.Measure.fullWeightedSequenceGaussian c s)
      (fun i x => f i (coordE c s x)) l (fun x => g (coordE c s x)) := by
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ => zero_le) (fun i => ?_)
  have hmp := measurePreserving_coordE c s hs
  have := Measure.le_map_apply (measurable_coordE c s).aemeasurable
    (μ := NlsGge.Measure.fullWeightedSequenceGaussian c s)
    {z | ε ≤ edist (f i z) (g z)}
  rw [hmp.map_eq] at this
  exact this

/-- The Ramer density as a function on `E_s`. -/
def ramerJE (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (δK : (ℤ → ℂ) → ℝ)
    (x : FullWeightedHilbert c s) : ℝ :=
  ramerJ c s hs K δK (coordE c s x)

theorem ramerJE_eq (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (δK : (ℤ → ℂ) → ℝ)
    (x : FullWeightedHilbert c s) :
    ramerJE c s hs K δK x =
      |det2 (hsDerivH c s hs K x)| *
        Real.exp (-(δK (coordE c s x)) - ‖K x‖ ^ 2 / 2) := by
  unfold ramerJE ramerJ
  rw [realization_coordE]

theorem aestronglyMeasurable_ramerJE (c : BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (K : FullWeightedHilbert c s → ActualCM c) (hK : ContDiff ℝ 1 K)
    (δK : (ℤ → ℂ) → ℝ)
    (hδ : AEStronglyMeasurable δK (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :
    AEStronglyMeasurable (ramerJE c s hs K δK)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
  AEStronglyMeasurable.comp_quasiMeasurePreserving
    (aestronglyMeasurable_ramerJ c s hs K hK δK hδ)
    (measurePreserving_coordE c s hs).quasiMeasurePreserving

theorem ramerJE_pos (c : BoundedCoefficients lower upper) (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (T : FullWeightedHilbert c s ≃ₜ FullWeightedHilbert c s)
    (K K' : FullWeightedHilbert c s → ActualCM c)
    (hT : ∀ x, T x = x + cmToFullWeightedHilbert c s (le_of_lt (by linarith : 0 < s)) (K x))
    (hTs : ∀ y, T.symm y = y + cmToFullWeightedHilbert c s
      (le_of_lt (by linarith : 0 < s)) (K' y))
    (hK : ContDiff ℝ 1 K) (hK' : ContDiff ℝ 1 K')
    (δK : (ℤ → ℂ) → ℝ) (x : FullWeightedHilbert c s) :
    0 < ramerJE c s hs K δK x :=
  ramerJ_pos c s hs T K K' hT hTs hK hK' δK (coordE c s x)

end NlsGge.Ramer
