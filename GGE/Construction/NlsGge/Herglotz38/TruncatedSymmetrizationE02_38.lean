import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace NlsGge.SpectralFoundations

/-! # S02 symmetrization (campaign 38): truncated Hilbert pairing against a monotone weight -/

/-- The truncated kernel `1_{δ<|t-l|} v(l) v(t)/(l-t)` on `ℝ × ℝ`. -/
def truncKernelE02_38 (v : ℝ → ℝ) (δ : ℝ) (p : ℝ × ℝ) : ℝ :=
  Set.indicator {q : ℝ × ℝ | δ < |q.2 - q.1|} (fun q => v q.1 * v q.2 / (q.1 - q.2)) p

theorem truncKernelE02_38_swap (v : ℝ → ℝ) (δ : ℝ) (p : ℝ × ℝ) :
    truncKernelE02_38 v δ p.swap = - truncKernelE02_38 v δ p := by
  unfold truncKernelE02_38
  by_cases h : δ < |p.2 - p.1|
  · have h' : δ < |p.swap.2 - p.swap.1| := by simpa [abs_sub_comm] using h
    rw [Set.indicator_of_mem (show p.swap ∈ {q : ℝ × ℝ | δ < |q.2 - q.1|} from h'),
      Set.indicator_of_mem (show p ∈ {q : ℝ × ℝ | δ < |q.2 - q.1|} from h)]
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [show p.2 - p.1 = -(p.1 - p.2) by ring, div_neg]; ring
  · have h' : ¬ δ < |p.swap.2 - p.swap.1| := by simpa [abs_sub_comm] using h
    rw [Set.indicator_of_notMem (show p.swap ∉ {q : ℝ × ℝ | δ < |q.2 - q.1|} from h'),
      Set.indicator_of_notMem (show p ∉ {q : ℝ × ℝ | δ < |q.2 - q.1|} from h), neg_zero]

theorem measurable_truncKernelE02_38 (v : ℝ → ℝ) (hv : Continuous v) (δ : ℝ) :
    Measurable (truncKernelE02_38 v δ) := by
  unfold truncKernelE02_38
  apply Measurable.indicator
  · exact ((hv.comp continuous_fst).mul (hv.comp continuous_snd)).measurable.div
      (continuous_fst.sub continuous_snd).measurable
  · exact measurableSet_lt measurable_const
      ((continuous_snd.sub continuous_fst).abs.measurable)

/-- Symmetrization: for nonnegative continuous `v` supported in `[-A,A]` and monotone `φ`,
the truncated Hilbert pairing is nonnegative. -/
theorem truncatedHilbert_pairing_nonneg_E02_38 (v φ : ℝ → ℝ) (hv : Continuous v)
    (hv0 : ∀ t, 0 ≤ v t) (A : ℝ) (hsupp : ∀ t, A < |t| → v t = 0) (hφ : Monotone φ)
    (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ ∫ l, φ l * v l * ∫ t in {t | δ < |t - l|}, v t / (l - t) := by
  set K := truncKernelE02_38 v δ
  -- bounds
  obtain ⟨V, hV⟩ := (isCompact_Icc (a := -A) (b := A)).exists_bound_of_continuousOn hv.continuousOn
  have hvb : ∀ t, |v t| ≤ |V| := by
    intro t
    by_cases ht : A < |t|
    · rw [hsupp t ht, abs_zero]; exact abs_nonneg _
    · push Not at ht
      exact (hV t (abs_le.mp ht |> fun h => ⟨h.1, h.2⟩)).trans (le_abs_self _)
  set Φ := max |φ (-A)| |φ A|
  have hφb : ∀ t ∈ Set.Icc (-A) A, |φ t| ≤ Φ := by
    intro t ht
    have h1 := hφ ht.1; have h2 := hφ ht.2
    rw [abs_le]; constructor
    · have := neg_abs_le (φ (-A)); have := le_max_left |φ (-A)| |φ A|; linarith
    · have := le_abs_self (φ A); have := le_max_right |φ (-A)| |φ A|; linarith
  -- the integrand on the product
  let G : ℝ × ℝ → ℝ := fun p => φ p.1 * K p
  have hKsupp : ∀ p : ℝ × ℝ, K p ≠ 0 → p ∈ Set.Icc (-A) A ×ˢ Set.Icc (-A) A := by
    intro p hp
    have h1 : v p.1 ≠ 0 ∧ v p.2 ≠ 0 := by
      constructor <;> intro h <;> apply hp <;>
        simp [K, truncKernelE02_38, Set.indicator, h]
    refine ⟨?_, ?_⟩
    · by_contra hc; apply h1.1; apply hsupp
      simp only [Set.mem_Icc, not_and_or, not_le] at hc
      rcases hc with hc | hc
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
      · exact lt_of_lt_of_le hc (le_abs_self _)
    · by_contra hc; apply h1.2; apply hsupp
      simp only [Set.mem_Icc, not_and_or, not_le] at hc
      rcases hc with hc | hc
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
      · exact lt_of_lt_of_le hc (le_abs_self _)
  have hKb : ∀ p : ℝ × ℝ, |K p| ≤ |V|^2 / δ := by
    intro p
    simp only [K, truncKernelE02_38, Set.indicator]
    split_ifs with h
    · rw [abs_div, abs_mul]
      have hd : δ ≤ |p.1 - p.2| := by rw [abs_sub_comm]; exact h.le
      calc |v p.1| * |v p.2| / |p.1 - p.2| ≤ |V|^2 / |p.1 - p.2| := by
            apply div_le_div_of_nonneg_right _ (abs_nonneg _)
            rw [sq]; exact mul_le_mul (hvb _) (hvb _) (abs_nonneg _) (abs_nonneg _)
        _ ≤ |V|^2 / δ := div_le_div_of_nonneg_left (sq_nonneg _) hδ hd
    · simp; positivity
  have hKm : Measurable K := measurable_truncKernelE02_38 v hv δ
  have hKi : Integrable K (volume.prod volume) := by
    have hon : IntegrableOn K (Set.Icc (-A) A ×ˢ Set.Icc (-A) A) (volume.prod volume) := by
      refine Measure.integrableOn_of_bounded (M := |V|^2 / δ) ?_ hKm.aestronglyMeasurable ?_
      · rw [Measure.prod_prod, Real.volume_Icc]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      · exact Filter.Eventually.of_forall (fun p => by rw [Real.norm_eq_abs]; exact hKb p)
    exact (integrableOn_iff_integrable_of_support_subset (fun p hp => hKsupp p hp)).mp hon
  have hGi : Integrable G (volume.prod volume) := by
    have : G = fun p => (Set.indicator (Set.Icc (-A) A) φ p.1) * K p := by
      funext p
      by_cases hK : K p = 0
      · simp [G, hK]
      · simp [G, Set.indicator_of_mem (hKsupp p hK).1]
    rw [this]
    refine hKi.bdd_mul (c := Φ) ?_ ?_
    · exact ((hφ.measurable.indicator measurableSet_Icc).comp measurable_fst).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => by
        by_cases hp : p.1 ∈ Set.Icc (-A) A
        · rw [Set.indicator_of_mem hp, Real.norm_eq_abs]; exact hφb _ hp
        · rw [Set.indicator_of_notMem hp, norm_zero]; exact le_max_of_le_left (abs_nonneg _)
  -- rewrite the pairing as the integral of G
  have hpair : (∫ l, φ l * v l * ∫ t in {t | δ < |t - l|}, v t / (l - t)) = ∫ p, G p := by
    rw [Measure.volume_eq_prod, integral_prod G hGi]
    apply integral_congr_ae
    filter_upwards with l
    have hS : MeasurableSet {t : ℝ | δ < |t - l|} :=
      measurableSet_lt measurable_const ((continuous_id.sub continuous_const).abs.measurable)
    rw [← integral_indicator hS, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    simp only [G, K, truncKernelE02_38, Set.indicator, Set.mem_setOf_eq]
    split_ifs <;> ring
  -- swap symmetry
  have hswap : ∫ p, G p = ∫ p, -(φ p.2 * K p) := by
    rw [Measure.volume_eq_prod, ← integral_prod_swap]
    apply integral_congr_ae
    filter_upwards with p
    simp only [G, Prod.fst_swap]
    rw [show K p.swap = truncKernelE02_38 v δ p.swap from rfl, truncKernelE02_38_swap]; ring
  have hH : Integrable (fun p : ℝ × ℝ => φ p.2 * K p) (volume.prod volume) := by
    have hs := hGi.swap
    have : (fun p : ℝ × ℝ => φ p.2 * K p) = fun p => -((G ∘ Prod.swap) p) := by
      funext p
      simp only [Function.comp, G, Prod.fst_swap]
      rw [show K p.swap = truncKernelE02_38 v δ p.swap from rfl, truncKernelE02_38_swap]; ring
    rw [this]; exact hs.neg
  have htwo : 2 * ∫ p, G p = ∫ p, (φ p.1 - φ p.2) * K p := by
    have h1 : ∫ p, -(φ p.2 * K p) = -∫ p, φ p.2 * K p := integral_neg _
    calc 2 * ∫ p, G p = (∫ p, G p) + ∫ p, -(φ p.2 * K p) := by rw [← hswap]; ring
      _ = ∫ p, (G p + -(φ p.2 * K p)) := (integral_add hGi hH.neg).symm
      _ = ∫ p, (φ p.1 - φ p.2) * K p := by
          apply integral_congr_ae; filter_upwards with p; simp only [G]; ring
  have hnn : 0 ≤ ∫ p, (φ p.1 - φ p.2) * K p := by
    apply integral_nonneg
    intro p
    simp only [K, truncKernelE02_38, Set.indicator]
    split_ifs with h
    · have hvv : 0 ≤ v p.1 * v p.2 := mul_nonneg (hv0 _) (hv0 _)
      rcases lt_trichotomy p.2 p.1 with hlt | heq | hgt
      · have hφ' : 0 ≤ φ p.1 - φ p.2 := sub_nonneg.mpr (hφ hlt.le)
        exact mul_nonneg hφ' (div_nonneg hvv (by linarith))
      · exfalso
        have h' : δ < |p.2 - p.1| := h
        rw [heq, sub_self, abs_zero] at h'; linarith
      · have hφ' : φ p.1 - φ p.2 ≤ 0 := sub_nonpos.mpr (hφ hgt.le)
        exact mul_nonneg_of_nonpos_of_nonpos hφ' (div_nonpos_of_nonneg_of_nonpos hvv (by linarith))
    · simp
  rw [hpair]
  linarith

end NlsGge.SpectralFoundations
end
