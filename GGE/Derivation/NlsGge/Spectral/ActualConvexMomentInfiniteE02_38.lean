import NlsGge.Spectral.ActualHilbertSplitE02_38
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis

/-! # S02-∞: the convex spectral inequality for infinite-gap H¹ fields, truncated form (campaign 38)

At a band cut `L` (`v = 0` on `L - d < |t| < L + d`), for convex C² `W` and `f(x) = W(2x)`:
`∫_{[-L,L]} (f - f∘p) v ≥ -(1/π)(1/d)(∫_{[-L,L]} |f'∘p| v)(∫_{|t|>L} v)`.
Proof: tangent inequality, the split Hilbert formula H∞, nonnegativity of the symmetrized pairing for the compact
part `v_L` (finite-gap S02 argument), and the bound `|∫ (v - v_L)(t)/(l - t) dt| ≤ (1/d)∫(v - v_L)` for `|l| ≤ L`. -/

/-- The pv-Hilbert transform of a Plemelj-admissible function is strongly measurable. -/
theorem stronglyMeasurable_pvHilbert_E02_38 {v : ℝ → ℝ} {H A : ℝ} (hv : Continuous v) (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hsupp : ∀ t, t ∉ Icc (-A) A → v t = 0)
    (hhol : ∀ s t, |v s - v t| ≤ H * √|s - t|) :
    StronglyMeasurable (pvHilbert v) := by
  refine stronglyMeasurable_of_tendsto (𝓝[>] (0:ℝ))
    (f := fun δ l => ∫ t in {t | δ < |t - l|}, v t / (l - t))
    (fun δ => stronglyMeasurable_truncHilbert_E02_38 v hv δ) ?_
  exact tendsto_pi_nhds.mpr fun l => tendsto_pvHilbert_E02_38 hv hH hA hsupp hhol l

/-- The far Cauchy integral `J(l) = ∫ w(t)/(l - t) dt` is strongly measurable. -/
theorem stronglyMeasurable_farHilbert_E02_38 (w : ℝ → ℝ) (hw : Continuous w) :
    StronglyMeasurable (fun l : ℝ => ∫ t, w t / (l - t)) := by
  have hG : StronglyMeasurable (fun q : ℝ × ℝ => w q.2 / (q.1 - q.2)) :=
    ((hw.comp continuous_snd).measurable.div
      (continuous_fst.sub continuous_snd).measurable).stronglyMeasurable
  exact hG.integral_prod_right' (ν := (volume : Measure ℝ))

theorem abs_farHilbert_le_E02_38 {u : PhysicalL2} {L d : ℝ} (h : IsBandCutE02_38 u L d)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) (l : ℝ) (hl : |l| ≤ L) :
    |∫ t, gapTailE02_38 u L t / (l - t)| ≤ (1/d) * ∫ t, gapTailE02_38 u L t := by
  have hd0 : 0 < d := h.1
  have hwi := integrable_gapTailE02_38 u hu L d h
  have hb : ∀ t, ‖gapTailE02_38 u L t / (l - t)‖ ≤ (1/d) * gapTailE02_38 u L t := by
    intro t
    have := norm_tail_div_le_E02_38 h l hl t (l:ℂ) (by simp)
    rw [norm_div, Complex.norm_real] at this
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    have e : ‖(t:ℂ) - (l:ℂ)‖ = |l - t| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    rw [e] at this
    rw [Real.norm_eq_abs] at this
    calc |gapTailE02_38 u L t| / |l - t| ≤ gapTailE02_38 u L t / d := this
      _ = (1/d) * gapTailE02_38 u L t := by ring
  have := norm_integral_le_of_norm_le (hwi.const_mul (1/d)) (Eventually.of_forall hb)
  rw [integral_const_mul, Real.norm_eq_abs] at this
  exact this

/-- **S02-∞, truncated form.** -/
theorem convexTrunc_E02_38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (W : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hconv : ConvexOn ℝ Set.univ W)
    (L d : ℝ) (h : IsBandCutE02_38 u L d) :
    -((1/Real.pi) * (1/d) *
        (∫ x in Icc (-L) L, |deriv (fun y => W (2*y)) (actualQuasimomentumRealPartE02_38 u x)| *
          actualGapHeightE02_38 u x) * (∫ t, gapTailE02_38 u L t)) ≤
      ∫ x in Icc (-L) L, (W (2*x) - W (2 * actualQuasimomentumRealPartE02_38 u x)) *
        actualGapHeightE02_38 u x := by
  set v := actualGapHeightE02_38 u with hvdef
  set p := actualQuasimomentumRealPartE02_38 u with hpdef
  set vL := gapCutE02_38 u L
  set w := gapTailE02_38 u L
  have hL : 0 ≤ L := by linarith [h.1, h.2.1]
  have hd0 : 0 < d := h.1
  have hvc : Continuous v := continuous_actualGapHeightE02_38 u
  have hv0 : ∀ t, 0 ≤ v t := actualGapHeightE02_38_nonneg u
  have hpc : Continuous p := continuous_actualQuasimomentumRealPartE02_38 u
  have hpm : Monotone p := monotone_actualQuasimomentumRealPartE02_38 u
  have hvLc : Continuous vL := continuous_gapCutE02_38 u L
  have hvL0 : ∀ t, 0 ≤ vL t := fun t => hv0 _
  obtain ⟨H, hH, hhol⟩ := gapCut_holder_E02_38 u L hL
  have hsupp := h.cut_supp
  have hsupp' : ∀ t, L < |t| → vL t = 0 := fun t ht => h.cut_eq_zero t (by linarith)
  have hvLcs : HasCompactSupport vL :=
    HasCompactSupport.intro (isCompact_Icc (a := -L) (b := L)) fun t ht => hsupp t ht
  have hvLi : Integrable vL := hvLc.integrable_of_hasCompactSupport hvLcs
  have hwi := integrable_gapTailE02_38 u hu L d h
  -- f and φ
  let f : ℝ → ℝ := fun x => W (2*x)
  have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hfd : Differentiable ℝ f := hWd.comp (differentiable_id.const_mul 2)
  have hfc : Continuous f := hfd.continuous
  have hfconv : ConvexOn ℝ Set.univ f := by
    have := hconv.comp_linearMap ((2:ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    simpa [f, Function.comp_def] using this
  have hfmono : Monotone (deriv f) := by
    have h' := hfconv.monotoneOn_deriv (fun x _ => hfd x)
    exact fun x y hxy => h' (Set.mem_univ x) (Set.mem_univ y) hxy
  have hderivf : Continuous (deriv f) := by
    have h1 : ContDiff ℝ 2 f := hW.comp (contDiff_const.mul contDiff_id)
    exact h1.continuous_deriv (by norm_num)
  have htan : ∀ x y : ℝ, f x + deriv f x * (y - x) ≤ f y := by
    intro x y
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · have h' := hfconv.deriv_le_slope (Set.mem_univ x) (Set.mem_univ y) hxy (hfd x)
      rw [slope_def_field, le_div_iff₀ (by linarith)] at h'; linarith
    · rw [hxy]; simp
    · have h' := hfconv.slope_le_deriv (Set.mem_univ y) (Set.mem_univ x) hxy (hfd x)
      rw [slope_def_field, div_le_iff₀ (by linarith)] at h'; linarith
  let φ : ℝ → ℝ := fun l => deriv f (p l)
  have hφ : Monotone φ := hfmono.comp hpm
  have hφc : Continuous φ := hderivf.comp hpc
  -- Hilbert transform of the compact part
  obtain ⟨M, hM⟩ := truncatedHilbert_bound_E02_38 hvLc hH hL hsupp hhol
  have hpvb : ∀ l, |pvHilbert vL l| ≤ M := by
    intro l
    have ht := tendsto_pvHilbert_E02_38 hvLc hH hL hsupp hhol l
    exact le_of_tendsto ht.abs (eventually_nhdsWithin_of_forall fun δ hδ => hM l δ hδ)
  have hpvm : StronglyMeasurable (pvHilbert vL) :=
    stronglyMeasurable_pvHilbert_E02_38 hvLc hH hL hsupp hhol
  set Φ := max |φ (-L)| |φ L|
  have hΦ0 : 0 ≤ Φ := le_trans (abs_nonneg _) (le_max_left _ _)
  have hφb : ∀ l ∈ Icc (-L) L, |φ l| ≤ Φ := by
    intro l hlI
    have h1 := hφ hlI.1; have h2 := hφ hlI.2
    rw [abs_le]; constructor
    · have := neg_abs_le (φ (-L)); have := le_max_left |φ (-L)| |φ L|; linarith
    · have := le_abs_self (φ L); have := le_max_right |φ (-L)| |φ L|; linarith
  have hφbL : ∀ l, vL l ≠ 0 → |φ l| ≤ Φ := by
    intro l hl
    exact hφb l (by by_contra hc; exact hl (hsupp l hc))
  have hPint : Integrable (fun l => φ l * vL l * pvHilbert vL l) := by
    refine (hvLi.norm.const_mul (Φ * M)).mono'
      ((hφc.aestronglyMeasurable.mul hvLc.aestronglyMeasurable).mul hpvm.aestronglyMeasurable)
      (Eventually.of_forall fun l => ?_)
    by_cases hl : vL l = 0
    · simp [hl]
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, Real.norm_eq_abs]
      have h1 := hφbL l hl; have h2 := hpvb l
      calc |φ l| * |vL l| * |pvHilbert vL l| ≤ Φ * |vL l| * M := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2
              (abs_nonneg _) (by positivity)
        _ = Φ * M * |vL l| := by ring
  have hlimit : Tendsto (fun δ : ℝ => ∫ l, φ l * vL l * ∫ t in {t | δ < |t - l|}, vL t / (l - t))
      (𝓝[>] 0) (𝓝 (∫ l, φ l * vL l * pvHilbert vL l)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun l => Φ * M * |vL l|)
    · exact Eventually.of_forall fun δ =>
        ((hφc.aestronglyMeasurable.mul hvLc.aestronglyMeasurable).mul
          (stronglyMeasurable_truncHilbert_E02_38 vL hvLc δ).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact Eventually.of_forall fun l => by
        by_cases hl : vL l = 0
        · simp [hl]
        · rw [Real.norm_eq_abs, abs_mul, abs_mul]
          have h1 := hφbL l hl; have h2 := hM l δ hδ
          calc |φ l| * |vL l| * |∫ t in {t | δ < |t - l|}, vL t / (l - t)| ≤ Φ * |vL l| * M := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (abs_nonneg _)) h2
                  (abs_nonneg _) (by positivity)
            _ = Φ * M * |vL l| := by ring
    · exact hvLi.norm.const_mul _
    · exact Eventually.of_forall fun l =>
        ((tendsto_pvHilbert_E02_38 hvLc hH hL hsupp hhol l).const_mul (φ l * vL l))
  have hpos : 0 ≤ ∫ l, φ l * vL l * pvHilbert vL l := by
    apply ge_of_tendsto hlimit
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact truncatedHilbert_pairing_nonneg_E02_38 vL φ hvLc hvL0 L hsupp' hφ δ hδ
  have hposI : 0 ≤ ∫ l in Icc (-L) L, φ l * v l * pvHilbert vL l := by
    have e1 : ∫ l in Icc (-L) L, φ l * v l * pvHilbert vL l =
        ∫ l in Icc (-L) L, φ l * vL l * pvHilbert vL l := by
      refine setIntegral_congr_fun measurableSet_Icc fun l hl => ?_
      rw [show vL l = v l from h.cut_eq_of_mem l (abs_le.mpr hl)]
    have e2 : ∫ l in Icc (-L) L, φ l * vL l * pvHilbert vL l = ∫ l, φ l * vL l * pvHilbert vL l :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun l hl => by rw [show vL l = 0 from hsupp l hl]; ring
    rw [e1, e2]; exact hpos
  -- the far part
  set J : ℝ → ℝ := fun l => ∫ t, w t / (l - t)
  have hJm : StronglyMeasurable J := stronglyMeasurable_farHilbert_E02_38 w (continuous_gapTailE02_38 u L)
  set Tw := ∫ t, w t
  have hJb : ∀ l ∈ Icc (-L) L, |J l| ≤ (1/d) * Tw := fun l hl =>
    abs_farHilbert_le_E02_38 h hu l (abs_le.mpr hl)
  -- integrability on Icc
  have hIfin : volume (Icc (-L) L) < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hφv : IntegrableOn (fun l => φ l * v l) (Icc (-L) L) :=
    (hφc.mul hvc).continuousOn.integrableOn_Icc
  have hφva : IntegrableOn (fun l => |φ l| * v l) (Icc (-L) L) :=
    (hφc.abs.mul hvc).continuousOn.integrableOn_Icc
  have hI1 : IntegrableOn (fun l => φ l * v l * pvHilbert vL l) (Icc (-L) L) := by
    refine Integrable.mono' (hφv.norm.const_mul M)
      (hφv.aestronglyMeasurable.mul hpvm.aestronglyMeasurable.restrict)
      (Eventually.of_forall fun l => ?_)
    rw [norm_mul _ (pvHilbert vL l), Real.norm_eq_abs (pvHilbert vL l), mul_comm M]
    exact mul_le_mul_of_nonneg_left (hpvb l) (norm_nonneg _)
  have hI2 : IntegrableOn (fun l => φ l * v l * J l) (Icc (-L) L) := by
    refine Integrable.mono' (hφv.norm.const_mul ((1/d) * Tw))
      (hφv.aestronglyMeasurable.mul hJm.aestronglyMeasurable.restrict) ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun l hl => ?_)
    rw [norm_mul _ (J l), Real.norm_eq_abs (J l), mul_comm ((1/d) * Tw)]
    exact mul_le_mul_of_nonneg_left (hJb l hl) (norm_nonneg _)
  -- assemble
  have hsplit : ∫ l in Icc (-L) L, φ l * (l - p l) * v l =
      (1/Real.pi) * ((∫ l in Icc (-L) L, φ l * v l * pvHilbert vL l) +
        (∫ l in Icc (-L) L, φ l * v l * J l)) := by
    rw [← integral_add hI1 hI2, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun l hl => ?_
    rw [realPart_sub_split_E02_38 u hu L d h l (abs_le.mpr hl)]
    ring
  have hcross : -((1/d) * Tw * ∫ l in Icc (-L) L, |φ l| * v l) ≤
      ∫ l in Icc (-L) L, φ l * v l * J l := by
    have hb : ∀ l ∈ Icc (-L) L, -((1/d) * Tw * (|φ l| * v l)) ≤ φ l * v l * J l := by
      intro l hl
      have h1 := hJb l hl
      have h2 : |φ l * v l * J l| ≤ (1/d) * Tw * (|φ l| * v l) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (hv0 l)]
        calc |φ l| * v l * |J l| ≤ |φ l| * v l * ((1/d) * Tw) :=
              mul_le_mul_of_nonneg_left h1 (mul_nonneg (abs_nonneg _) (hv0 l))
          _ = _ := by ring
      linarith [neg_abs_le (φ l * v l * J l)]
    have := setIntegral_mono_on (hφva.const_mul ((1/d) * Tw)).neg hI2 measurableSet_Icc hb
    simp only [Pi.neg_apply] at this
    rw [integral_neg, integral_const_mul] at this
    exact this
  have hlow : ∫ l in Icc (-L) L, φ l * (l - p l) * v l ≤
      ∫ l in Icc (-L) L, (W (2*l) - W (2 * p l)) * v l := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun l _ => ?_
    · exact ((hφc.mul (continuous_id.sub hpc)).mul hvc).continuousOn.integrableOn_Icc
    · exact (((hfc.sub (hfc.comp hpc)).mul hvc)).continuousOn.integrableOn_Icc
    · have := htan (p l) l
      exact mul_le_mul_of_nonneg_right (by simp only [φ, f] at this ⊢; linarith) (hv0 l)
  have hpi := Real.pi_pos
  have hmain : (1/Real.pi) * (-((1/d) * Tw * ∫ l in Icc (-L) L, |φ l| * v l)) ≤
      ∫ l in Icc (-L) L, φ l * (l - p l) * v l := by
    rw [hsplit]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith
  have e : -((1/Real.pi) * (1/d) *
        (∫ x in Icc (-L) L, |deriv (fun y => W (2*y)) (p x)| * v x) * Tw) =
      (1/Real.pi) * (-((1/d) * Tw * ∫ l in Icc (-L) L, |φ l| * v l)) := by
    simp only [φ, f]; ring
  rw [e]
  linarith

end NlsGge.SpectralFoundations
end
