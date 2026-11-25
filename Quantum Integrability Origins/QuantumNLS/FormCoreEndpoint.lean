import Mathlib
import QuantumNLS.FormCoreFamilies

/-!
# R-1602B09D `CC:F03:core`: the endpoint cutoff

Printed estimate `E_μ(w_δ) ≤ C δ` (`CC:F03:endpoint-cutoff`) for the plateau cutoff `w_δ` at an endpoint `e` of the positive set, `ρ(x) ≤ C|x-e|^{1/2}`.  Here we prove what the
reduction needs, with the weaker hypothesis `ρ` continuous, `0 ≤ ρ ≤ B_ρ`, `ρ(e) = 0`:
`E_μ(w_δ) ≤ 16 π B_ρ sup_{|x-e|≤2δ} ρ → 0` (`formE_wend_tendsto`), by the bound `dq w ≤ (1_B(x) + 1_B(y)) · 2/(δ² + (x-y)²)` and `∫ 2/(δ²+z²) dz = 2π/δ`,
`μ(B_{2δ}(e)) ≤ 4δ sup ρ`.  (The square-root rate is not needed for density.)
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Real

noncomputable section

namespace QuantumNLS.FormCore

/-- The plateau cutoff at `e`: `1` on `|x-e| ≤ δ`, `0` on `|x-e| ≥ 2δ`, Lipschitz `1/δ`. -/
def wend (e δ x : ℝ) : ℝ := clamp (2 - |x - e| / δ)

theorem measurable_wend (e δ : ℝ) : Measurable (wend e δ) := by
  unfold wend; exact measurable_clamp.comp (by fun_prop)

theorem wend_nonneg (e δ x : ℝ) : 0 ≤ wend e δ x := clamp_nonneg _
theorem wend_le_one (e δ x : ℝ) : wend e δ x ≤ 1 := clamp_le_one _

theorem wend_lip {δ : ℝ} (hδ : 0 < δ) (e x y : ℝ) : |wend e δ x - wend e δ y| ≤ (1 / δ) * |x - y| := by
  unfold wend
  refine le_trans (abs_clamp_sub_le _ _) ?_
  have e1 : 2 - |x - e| / δ - (2 - |y - e| / δ) = (|y - e| - |x - e|) / δ := by ring
  rw [e1, abs_div, abs_of_pos hδ]
  calc |(|y - e| - |x - e|)| / δ ≤ |x - y| / δ := by
        refine div_le_div_of_nonneg_right ?_ hδ.le
        calc |(|y - e| - |x - e|)| ≤ |(y - e) - (x - e)| := abs_abs_sub_abs_le_abs_sub _ _
          _ = |x - y| := by rw [show (y - e) - (x - e) = -(x - y) by ring, abs_neg]
    _ = (1 / δ) * |x - y| := by ring

theorem wend_eq_zero {e δ x : ℝ} (hδ : 0 < δ) (hx : 2 * δ ≤ |x - e|) : wend e δ x = 0 := by
  have : 2 - |x - e| / δ ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hδ]; linarith
  simp [wend, clamp, max_eq_left this]

theorem wend_eq_one {e δ x : ℝ} (hδ : 0 < δ) (hx : |x - e| ≤ δ) : wend e δ x = 1 := by
  have : 1 ≤ 2 - |x - e| / δ := by
    have : |x - e| / δ ≤ 1 := by rw [div_le_one hδ]; exact hx
    linarith
  simp only [wend, clamp]
  rw [max_eq_right (show (0 : ℝ) ≤ 2 - |x - e| / δ by linarith)]
  exact min_eq_left this

theorem wend_tendsto {e x : ℝ} (hx : x ≠ e) :
    Tendsto (fun k : ℕ => wend e (1 / ((k : ℝ) + 1)) x) atTop (𝓝 0) := by
  have hpos : 0 < |x - e| := abs_pos.2 (sub_ne_zero.2 hx)
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / |x - e|)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop K] with k hk
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hδ : 0 < 1 / ((k : ℝ) + 1) := by positivity
  symm
  apply wend_eq_zero hδ
  have : (K : ℝ) ≤ k := by exact_mod_cast hk
  have h2 : 2 / |x - e| < (k : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hpos] at h2
  rw [mul_one_div, div_le_iff₀ hk0]
  nlinarith

theorem dq_wend_le {δ : ℝ} (hδ : 0 < δ) (e : ℝ) (p : ℝ × ℝ) :
    dq (wend e δ) p ≤ 2 / (δ ^ 2 + (p.1 - p.2) ^ 2) := by
  unfold dq
  by_cases hp : p.1 = p.2
  · simp [hp]; positivity
  · have hz : 0 < (p.1 - p.2) ^ 2 := by
      have := sub_ne_zero.2 hp
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 this))
    have hd : 0 < δ ^ 2 + (p.1 - p.2) ^ 2 := by positivity
    rw [div_le_div_iff₀ hz hd]
    set a := wend e δ p.1 - wend e δ p.2 with ha
    have h1 : a ^ 2 ≤ 1 := by
      have := wend_nonneg e δ p.1
      have := wend_nonneg e δ p.2
      have := wend_le_one e δ p.1
      have := wend_le_one e δ p.2
      nlinarith
    have h2 : a ^ 2 * δ ^ 2 ≤ (p.1 - p.2) ^ 2 := by
      have hl := wend_lip hδ e p.1 p.2
      have h3 : |a| * δ ≤ |p.1 - p.2| := by
        calc |a| * δ ≤ (1 / δ) * |p.1 - p.2| * δ := mul_le_mul_of_nonneg_right hl hδ.le
          _ = |p.1 - p.2| := by field_simp
      have h4 := pow_le_pow_left₀ (by positivity) h3 2
      rw [mul_pow, sq_abs, sq_abs] at h4
      exact h4
    nlinarith [h1, h2, sq_nonneg (p.1 - p.2)]

/-! ### The kernel `2/(δ²+z²)` -/

/-- `Kc δ z = 2/(δ² + z²) = (2/δ²)(1 + (z/δ)²)⁻¹`. -/
def Kc (δ z : ℝ) : ℝ := (2 / δ ^ 2) * (1 + (δ⁻¹ * z) ^ 2)⁻¹

theorem Kc_eq {δ : ℝ} (hδ : 0 < δ) (z : ℝ) : Kc δ z = 2 / (δ ^ 2 + z ^ 2) := by
  unfold Kc
  have hd : δ ^ 2 + z ^ 2 ≠ 0 := by positivity
  field_simp

theorem Kc_nonneg (δ z : ℝ) : 0 ≤ Kc δ z := by unfold Kc; positivity

theorem Kc_neg (δ z : ℝ) : Kc δ (-z) = Kc δ z := by unfold Kc; rw [mul_neg, neg_sq]

theorem measurable_Kc (δ : ℝ) : Measurable (Kc δ) := by unfold Kc; fun_prop

theorem integral_Kc {δ : ℝ} (hδ : 0 < δ) : ∫ z, Kc δ z = 2 * Real.pi / δ := by
  unfold Kc
  rw [integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_inv, abs_of_pos hδ]
  field_simp

theorem lintegral_Kc {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ z, ENNReal.ofReal (Kc δ z) = ENNReal.ofReal (2 * Real.pi / δ) := by
  have hint : Integrable (Kc δ) := by
    unfold Kc
    exact (integrable_inv_one_add_mul_sq (inv_ne_zero hδ.ne')).const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (Kc_nonneg δ)), integral_Kc hδ]

theorem lintegral_Kc_shift {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Kc δ (x - y)) = ENNReal.ofReal (2 * Real.pi / δ) := by
  rw [lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (Kc δ z)) x, lintegral_Kc hδ]


/-! ### The energy of the cutoff -/

theorem ofReal_mul4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    2 * (ENNReal.ofReal a * ENNReal.ofReal b * (ENNReal.ofReal c * ENNReal.ofReal d)) =
      ENNReal.ofReal (2 * (a * b * (c * d))) := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha,
    ENNReal.ofReal_mul hc]
  simp [ENNReal.ofReal_ofNat]

theorem formE_wend_le {ρ : ℝ → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {Bρ : ℝ}
    (hB : ∀ x, ρ x ≤ Bρ) {e δ η : ℝ} (hδ : 0 < δ) (hη : ∀ x ∈ Icc (e - 2 * δ) (e + 2 * δ), ρ x ≤ η) :
    formE (volume.withDensity fun x => ENNReal.ofReal (ρ x)) (wend e δ) ≤
      ENNReal.ofReal (16 * Real.pi * Bρ * η) := by
  set μ : Measure ℝ := volume.withDensity fun x => ENNReal.ofReal (ρ x) with hμ
  set Bs : Set ℝ := Icc (e - 2 * δ) (e + 2 * δ) with hBs
  have hBm : MeasurableSet Bs := measurableSet_Icc
  have hBρ : 0 ≤ Bρ := le_trans (hρ0 e) (hB e)
  have hηn : 0 ≤ η := le_trans (hρ0 e) (hη e ⟨by linarith, by linarith⟩)
  set F1 : ℝ × ℝ → ℝ≥0∞ := fun p => Bs.indicator (fun _ => (1 : ℝ≥0∞)) p.1 * ENNReal.ofReal (Kc δ (p.1 - p.2)) with hF1
  set F2 : ℝ × ℝ → ℝ≥0∞ := fun p => Bs.indicator (fun _ => (1 : ℝ≥0∞)) p.2 * ENNReal.ofReal (Kc δ (p.1 - p.2)) with hF2
  have hF1m : Measurable F1 := by
    have h1 : Measurable fun p : ℝ × ℝ => Bs.indicator (fun _ => (1 : ℝ≥0∞)) p.1 :=
      (measurable_const.indicator hBm).comp measurable_fst
    exact h1.mul (ENNReal.measurable_ofReal.comp ((measurable_Kc δ).comp (measurable_fst.sub measurable_snd)))
  have hout : ∀ x : ℝ, x ∉ Bs → wend e δ x = 0 := by
    intro x hx
    apply wend_eq_zero hδ
    simp only [hBs, mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  -- step A
  have stepA : formE μ (wend e δ) ≤ ∫⁻ p, (F1 p + F2 p) ∂(μ.prod μ) := by
    unfold formE
    refine lintegral_mono fun p => ?_
    have hK : ENNReal.ofReal (dq (wend e δ) p) ≤ ENNReal.ofReal (Kc δ (p.1 - p.2)) := by
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Kc_eq hδ]; exact dq_wend_le hδ e p
    by_cases h1 : p.1 ∈ Bs
    · have : F1 p = ENNReal.ofReal (Kc δ (p.1 - p.2)) := by simp [hF1, h1]
      rw [← this] at hK
      exact le_trans hK le_self_add
    · by_cases h2 : p.2 ∈ Bs
      · have : F2 p = ENNReal.ofReal (Kc δ (p.1 - p.2)) := by simp [hF2, h2]
        rw [← this] at hK
        exact le_trans hK le_add_self
      · have : dq (wend e δ) p = 0 := by simp [dq, hout _ h1, hout _ h2]
        rw [this]; simp
  -- step B
  have stepB : ∫⁻ p, F2 p ∂(μ.prod μ) = ∫⁻ p, F1 p ∂(μ.prod μ) := by
    have := lintegral_prod_swap (μ := μ) (ν := μ) F1
    rw [← this]
    refine lintegral_congr fun p => ?_
    simp only [hF1, hF2, Prod.fst_swap, Prod.snd_swap]
    rw [← neg_sub, Kc_neg]
  -- step C : inner bound
  have inner : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (Kc δ (x - y)) ∂μ ≤
      ENNReal.ofReal Bρ * ENNReal.ofReal (2 * Real.pi / δ) := by
    intro x
    have hm : Measurable fun y => ENNReal.ofReal (Kc δ (x - y)) :=
      ENNReal.measurable_ofReal.comp ((measurable_Kc δ).comp (measurable_const.sub measurable_id))
    rw [hμ, lintegral_withDensity_eq_lintegral_mul (f := fun x => ENNReal.ofReal (ρ x)) volume
      (show Measurable fun x => ENNReal.ofReal (ρ x) from ENNReal.measurable_ofReal.comp hρm) hm]
    calc ∫⁻ y, ((fun x => ENNReal.ofReal (ρ x)) * fun y => ENNReal.ofReal (Kc δ (x - y))) y
        ≤ ∫⁻ y, ENNReal.ofReal Bρ * ENNReal.ofReal (Kc δ (x - y)) := by
          refine lintegral_mono fun y => ?_
          show ENNReal.ofReal (ρ y) * ENNReal.ofReal (Kc δ (x - y)) ≤ _
          gcongr
          exact hB y
      _ = ENNReal.ofReal Bρ * ∫⁻ y, ENNReal.ofReal (Kc δ (x - y)) := lintegral_const_mul _ hm
      _ = _ := by rw [lintegral_Kc_shift hδ x]
  have stepC : ∫⁻ p, F1 p ∂(μ.prod μ) ≤
      (ENNReal.ofReal Bρ * ENNReal.ofReal (2 * Real.pi / δ)) * μ Bs := by
    rw [lintegral_prod _ hF1m.aemeasurable]
    calc ∫⁻ x, ∫⁻ y, F1 (x, y) ∂μ ∂μ
        ≤ ∫⁻ x, Bs.indicator (fun _ => ENNReal.ofReal Bρ * ENNReal.ofReal (2 * Real.pi / δ)) x ∂μ := by
          refine lintegral_mono fun x => ?_
          by_cases hx : x ∈ Bs
          · simp only [hF1, hx, Set.indicator_of_mem, one_mul]
            exact inner x
          · simp [hF1, hx]
      _ = _ := lintegral_indicator_const hBm _
  -- step E
  have stepE : μ Bs ≤ ENNReal.ofReal η * ENNReal.ofReal (4 * δ) := by
    rw [hμ, withDensity_apply _ hBm]
    calc ∫⁻ x in Bs, ENNReal.ofReal (ρ x) ≤ ∫⁻ _x in Bs, ENNReal.ofReal η :=
          setLIntegral_mono' hBm fun x hx => ENNReal.ofReal_le_ofReal (hη x hx)
      _ = ENNReal.ofReal η * ENNReal.ofReal (4 * δ) := by
          rw [setLIntegral_const, hBs, Real.volume_Icc]
          congr 2; ring
  calc formE μ (wend e δ) ≤ ∫⁻ p, (F1 p + F2 p) ∂(μ.prod μ) := stepA
    _ = ∫⁻ p, F1 p ∂(μ.prod μ) + ∫⁻ p, F2 p ∂(μ.prod μ) := lintegral_add_left hF1m _
    _ = 2 * ∫⁻ p, F1 p ∂(μ.prod μ) := by rw [stepB, two_mul]
    _ ≤ 2 * ((ENNReal.ofReal Bρ * ENNReal.ofReal (2 * Real.pi / δ)) * (ENNReal.ofReal η * ENNReal.ofReal (4 * δ))) := by
        gcongr
        exact le_trans stepC (by gcongr)
    _ = ENNReal.ofReal (16 * Real.pi * Bρ * η) := by
        rw [ofReal_mul4 hBρ (by positivity) hηn (by positivity)]
        congr 1
        field_simp
        ring

theorem formE_wend_tendsto {ρ : ℝ → ℝ} (hρc : Continuous ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {Bρ : ℝ}
    (hB : ∀ x, ρ x ≤ Bρ) {e : ℝ} (he : ρ e = 0) :
    Tendsto (fun k : ℕ => formE (volume.withDensity fun x => ENNReal.ofReal (ρ x))
      (wend e (1 / ((k : ℝ) + 1)))) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hBρ : 0 ≤ Bρ := le_trans (hρ0 e) (hB e)
  -- choose η with 16 π Bρ η ≤ ε
  have hεr : ε ≠ ⊤ ∨ ε = ⊤ := by tauto
  rcases eq_or_ne ε ⊤ with hεt | hεt
  · exact Eventually.of_forall fun k => by rw [hεt]; exact le_top
  have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  set η : ℝ := ε.toReal / (16 * Real.pi * (Bρ + 1)) with hηdef
  have hηpos : 0 < η := by positivity
  obtain ⟨r, hr, hρr⟩ := Metric.continuousAt_iff.1 hρc.continuousAt η hηpos
  have hηs : ∀ x, |x - e| < r → ρ x ≤ η := by
    intro x hx
    have := hρr (by rwa [Real.dist_eq])
    rw [Real.dist_eq, he, sub_zero, abs_of_nonneg (hρ0 x)] at this
    exact this.le
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / r)
  filter_upwards [eventually_ge_atTop K] with k hk
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hδ : 0 < 1 / ((k : ℝ) + 1) := by positivity
  have hkK : (K : ℝ) ≤ k := by exact_mod_cast hk
  have hδr : 2 * (1 / ((k : ℝ) + 1)) < r := by
    have h2 : 2 / r < (k : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hr] at h2
    rw [mul_one_div, div_lt_iff₀ hk0]; linarith
  refine le_trans (formE_wend_le hρc.measurable hρ0 hB hδ (η := η) (fun x hx => hηs x ?_)) ?_
  · rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
  · rw [← ENNReal.ofReal_toReal hεt]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 16 * Real.pi * Bρ * η ≤ 16 * Real.pi * (Bρ + 1) * η := by nlinarith [Real.pi_pos]
    refine le_trans this ?_
    rw [hηdef]; field_simp; exact le_rfl

end QuantumNLS.FormCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FormCore.formE_wend_tendsto
