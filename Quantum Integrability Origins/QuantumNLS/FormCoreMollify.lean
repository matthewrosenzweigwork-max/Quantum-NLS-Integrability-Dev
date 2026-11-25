import Mathlib
import QuantumNLS.FormCoreCalculus
import QuantumNLS.FormCoreEndpoint

/-!
# R-1602B09D `CC:F03:core`: mollification in the unweighted norm

The printed proof mollifies a function `v` supported in a compact subset of the positive set with a compactly supported smooth approximate identity and
uses continuity of translations in `L²`.  Here (all unweighted, Lebesgue measure):

* `Eu h = ∬ |h(x)-h(y)|²/|x-y|² dx dy`, `L2u h = ∫ h²`, `omega h t = ∫ |h(x) - h(x-t)|² dx`, and the identity `Eu h = ∫ omega h t / t² dt` (`Eu_eq`).
* `mol n f = ψ_n ⋆ f` (`ψ_n` the normalized `ContDiffBump` of radius `1/(n+1)`): smooth with compact support (`contDiff_mol`, `hasCompactSupport_mol`), `|mol f| ≤ sup |f|`,
  the contraction `∫ (mol f)² ≤ ∫ f²` (Jensen, `lintegral_mol_sq_le`), linear and translation covariant, and `mol n f → f` a.e. (Mathlib's Lebesgue-point theorem).
* `l2_mollify_tendsto`: `∫ (f - mol n f)² → 0` for bounded measurable compactly supported `f` (dominated convergence).
* `mollify_energy`: if moreover `Eu g < ∞` then `Eu (g - mol n g) → 0`: via `Eu_eq`, `(g - mol g)(x) - (g - mol g)(x-t) = f_t - mol f_t` with `f_t = g - g(· - t)`, the pointwise-in-`t` limit
  `l2_mollify_tendsto` and the domination `omega (g - mol g) t ≤ 4 omega g t` (contraction).  This replaces the translation-continuity argument of the source by the Lebesgue point theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Real Convolution

noncomputable section

namespace QuantumNLS.FormCore

/-- `∬ |h(x)-h(y)|²/|x-y|² dxdy` (Lebesgue). -/
def Eu (h : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ p, ENNReal.ofReal (dq h p) ∂(volume.prod volume)

/-- `∫ h²`. -/
def L2u (h : ℝ → ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (h x ^ 2)

/-- `ω_h(t) = ∫ |h(x) - h(x-t)|² dx`. -/
def omega (h : ℝ → ℝ) (t : ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal ((h x - h (x - t)) ^ 2)

theorem measurable_omega {h : ℝ → ℝ} (hh : Measurable h) : Measurable (omega h) := by
  unfold omega
  have : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((h p.2 - h (p.2 - p.1)) ^ 2) := by
    refine ENNReal.measurable_ofReal.comp (((hh.comp measurable_snd).sub (hh.comp
      (measurable_snd.sub measurable_fst))).pow_const 2)
  exact this.lintegral_prod_right'

theorem Eu_eq {h : ℝ → ℝ} (hh : Measurable h) :
    Eu h = ∫⁻ t, ENNReal.ofReal (1 / t ^ 2) * omega h t := by
  unfold Eu
  have hFm : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (dq h p) :=
    ENNReal.measurable_ofReal.comp (measurable_dq hh)
  rw [lintegral_prod _ hFm.aemeasurable]
  have h1 : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (dq h (x, y)) =
      ∫⁻ t, ENNReal.ofReal (1 / t ^ 2) * ENNReal.ofReal ((h x - h (x - t)) ^ 2) := by
    intro x
    rw [← lintegral_sub_left_eq_self (fun y => ENNReal.ofReal (dq h (x, y))) x]
    refine lintegral_congr fun t => ?_
    unfold dq
    simp only [sub_sub_cancel]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [h1]
  have hm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (1 / p.2 ^ 2) * ENNReal.ofReal ((h p.1 - h (p.1 - p.2)) ^ 2) := by
    refine (ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_snd.pow_const 2))).mul
      (ENNReal.measurable_ofReal.comp (((hh.comp measurable_fst).sub (hh.comp
        (measurable_fst.sub measurable_snd))).pow_const 2))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  refine lintegral_congr fun t => ?_
  unfold omega
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  

/-! ### The mollifier operator -/

/-- The bump of radius `1/(n+1)` (inner radius half of it). -/
def bump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]; nlinarith⟩

/-- The normalized bump `ψ_n`. -/
def psi (n : ℕ) : ℝ → ℝ := (bump n).normed volume

theorem psi_nonneg (n : ℕ) (x : ℝ) : 0 ≤ psi n x := (bump n).nonneg_normed x
theorem integrable_psi (n : ℕ) : Integrable (psi n) := (bump n).integrable_normed
theorem integral_psi (n : ℕ) : ∫ x, psi n x = 1 := (bump n).integral_normed
theorem continuous_psi (n : ℕ) : Continuous (psi n) := (bump n).continuous_normed
theorem hasCompactSupport_psi (n : ℕ) : HasCompactSupport (psi n) := (bump n).hasCompactSupport_normed
theorem psi_eq_zero {n : ℕ} {x : ℝ} (hx : 1 ≤ |x|) : psi n x = 0 := by
  have : x ∉ Function.support (psi n) := by
    unfold psi
    rw [ContDiffBump.support_normed_eq]
    intro h
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at h
    have : (bump n).rOut ≤ 1 := by
      show 1 / ((n : ℝ) + 1) ≤ 1
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    linarith
  simpa using this

/-- `ψ_n ⋆ f`. -/
def mol (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t, psi n t * f (x - t)

theorem mol_eq_conv (n : ℕ) (f : ℝ → ℝ) :
    mol n f = (psi n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) := by
  funext x
  simp [mol, MeasureTheory.convolution_def]

theorem integrable_psi_mul {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (x : ℝ) :
    Integrable (fun t => psi n t * f (x - t)) := by
  refine (integrable_psi n).mul_bdd (c := M) ?_ ?_
  · exact (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · exact Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using hM (x - t)

theorem abs_mol_le {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (x : ℝ) :
    |mol n f x| ≤ M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  unfold mol
  have h1 : ‖∫ t, psi n t * f (x - t)‖ ≤ ∫ t, M * psi n t := by
    refine norm_integral_le_of_norm_le ((integrable_psi n).const_mul M) (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (psi_nonneg n t)]
    calc psi n t * |f (x - t)| ≤ psi n t * M := mul_le_mul_of_nonneg_left (hM _) (psi_nonneg n t)
      _ = M * psi n t := mul_comm _ _
  rw [integral_const_mul, integral_psi, mul_one, Real.norm_eq_abs] at h1
  exact h1

theorem mol_sub {n : ℕ} {f g : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hg : Measurable g) {M' : ℝ} (hM' : ∀ x, |g x| ≤ M') (x : ℝ) :
    mol n (fun z => f z - g z) x = mol n f x - mol n g x := by
  unfold mol
  rw [← integral_sub (integrable_psi_mul hf hM x) (integrable_psi_mul hg hM' x)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only []
  ring

theorem mol_shift (n : ℕ) (f : ℝ → ℝ) (t x : ℝ) :
    mol n (fun z => f (z - t)) x = mol n f (x - t) := by
  unfold mol
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only []
  rw [sub_right_comm]

/-- Jensen: `(∫ ψ f)² ≤ ∫ ψ f²` for a probability density `ψ`. -/
theorem jensen_mol {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) (x : ℝ) :
    mol n f x ^ 2 ≤ mol n (fun z => f z ^ 2) x := by
  set m := mol n f x with hm
  have hM2 : ∀ z, |f z ^ 2| ≤ M ^ 2 := fun z => by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hM z) 2
  have i1 := integrable_psi_mul (n := n) hf hM x
  have i2 := integrable_psi_mul (n := n) (hf.pow_const 2) hM2 x
  have i0 := integrable_psi n
  have hnn : 0 ≤ ∫ t, psi n t * (f (x - t) - m) ^ 2 :=
    integral_nonneg fun t => mul_nonneg (psi_nonneg n t) (sq_nonneg _)
  have e : ∫ t, psi n t * (f (x - t) - m) ^ 2 =
      (∫ t, psi n t * f (x - t) ^ 2) - 2 * m * (∫ t, psi n t * f (x - t)) + m ^ 2 * ∫ t, psi n t := by
    have hfun : (fun t => psi n t * (f (x - t) - m) ^ 2) =
        fun t => (psi n t * f (x - t) ^ 2 - 2 * m * (psi n t * f (x - t))) + m ^ 2 * psi n t := by
      funext t; ring
    have e1 : ∫ t, ((psi n t * f (x - t) ^ 2 - 2 * m * (psi n t * f (x - t))) + m ^ 2 * psi n t) =
        (∫ t, (psi n t * f (x - t) ^ 2 - 2 * m * (psi n t * f (x - t)))) + ∫ t, m ^ 2 * psi n t :=
      integral_add (i2.sub (i1.const_mul (2 * m))) (i0.const_mul (m ^ 2))
    have e2 : ∫ t, (psi n t * f (x - t) ^ 2 - 2 * m * (psi n t * f (x - t))) =
        (∫ t, psi n t * f (x - t) ^ 2) - ∫ t, 2 * m * (psi n t * f (x - t)) :=
      integral_sub i2 (i1.const_mul (2 * m))
    rw [hfun, e1, e2, integral_const_mul, integral_const_mul]
  rw [integral_psi, mul_one] at e
  have h2 : (∫ t, psi n t * f (x - t)) = m := rfl
  rw [h2] at e
  rw [e] at hnn
  show m ^ 2 ≤ ∫ t, psi n t * f (x - t) ^ 2
  nlinarith [hnn]


/-! ### Properties of `mol` -/

theorem locInt_of_bdd {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Measure.integrableOn_of_bounded (M := M) hK.measure_lt_top.ne hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)

theorem contDiff_mol (n : ℕ) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ContDiff ℝ ∞ (mol n f) := by
  rw [mol_eq_conv]
  exact (hasCompactSupport_psi n).contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    ((bump n).contDiff_normed (μ := volume) (n := ⊤)) (locInt_of_bdd hf hM)

theorem hasCompactSupport_mol (n : ℕ) {f : ℝ → ℝ} (hcf : HasCompactSupport f) :
    HasCompactSupport (mol n f) := by
  rw [mol_eq_conv]
  exact (hasCompactSupport_psi n).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hcf

theorem mol_eq_zero_of_far {n : ℕ} {f : ℝ → ℝ} {K : Set ℝ} (hK : ∀ x, x ∉ K → f x = 0) {x : ℝ}
    (hx : x ∉ Metric.cthickening 1 K) : mol n f x = 0 := by
  unfold mol
  have : ∀ t, psi n t * f (x - t) = 0 := by
    intro t
    by_cases ht : 1 ≤ |t|
    · rw [psi_eq_zero ht, zero_mul]
    · push Not at ht
      have : x - t ∉ K := by
        intro hK'
        apply hx
        refine Metric.mem_cthickening_of_dist_le x (x - t) 1 K hK' ?_
        rw [Real.dist_eq, sub_sub_cancel]; exact ht.le
      rw [hK _ this, mul_zero]
  simp [this]

theorem lintegral_mol_sq_le {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ∫⁻ x, ENNReal.ofReal (mol n f x ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
  have hM2 : ∀ z, |f z ^ 2| ≤ M ^ 2 := fun z => by
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hM z) 2
  have step1 : ∀ x, ENNReal.ofReal (mol n f x ^ 2) ≤
      ∫⁻ t, ENNReal.ofReal (psi n t) * ENNReal.ofReal (f (x - t) ^ 2) := by
    intro x
    refine le_trans (ENNReal.ofReal_le_ofReal (jensen_mol hf hM x)) ?_
    have i2 := integrable_psi_mul (n := n) (hf.pow_const 2) hM2 x
    show ENNReal.ofReal (∫ t, psi n t * f (x - t) ^ 2) ≤ _
    refine le_of_eq ?_
    calc ENNReal.ofReal (∫ t, psi n t * f (x - t) ^ 2) = ∫⁻ t, ENNReal.ofReal (psi n t * f (x - t) ^ 2) :=
          ofReal_integral_eq_lintegral_ofReal i2 (Eventually.of_forall fun t => mul_nonneg (psi_nonneg n t) (sq_nonneg _))
      _ = _ := lintegral_congr fun t => ENNReal.ofReal_mul (psi_nonneg n t)
  have hmeas : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (psi n p.2) * ENNReal.ofReal (f (p.1 - p.2) ^ 2) :=
    (ENNReal.measurable_ofReal.comp ((continuous_psi n).measurable.comp measurable_snd)).mul
      (ENNReal.measurable_ofReal.comp ((hf.comp (measurable_fst.sub measurable_snd)).pow_const 2))
  calc ∫⁻ x, ENNReal.ofReal (mol n f x ^ 2)
      ≤ ∫⁻ x, ∫⁻ t, ENNReal.ofReal (psi n t) * ENNReal.ofReal (f (x - t) ^ 2) := lintegral_mono step1
    _ = ∫⁻ t, ∫⁻ x, ENNReal.ofReal (psi n t) * ENNReal.ofReal (f (x - t) ^ 2) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ t, ENNReal.ofReal (psi n t) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_sub_right_eq_self
          (fun z => ENNReal.ofReal (f z ^ 2)) t]
    _ = (∫⁻ t, ENNReal.ofReal (psi n t)) * ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
        exact lintegral_mul_const _ (ENNReal.measurable_ofReal.comp (continuous_psi n).measurable)
    _ = ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal (integrable_psi n)
          (Eventually.of_forall (psi_nonneg n)), integral_psi]
        simp

theorem mol_tendsto_ae {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ∀ᵐ x, Tendsto (fun n : ℕ => mol n f x) atTop (𝓝 (f x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) (g := f)
    (φ := bump) (l := atTop) (K := 2)
    (by
      show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat)
    (Eventually.of_forall fun n => by
      show 1 / ((n : ℝ) + 1) ≤ 2 * (1 / (2 * ((n : ℝ) + 1)))
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp; exact le_rfl)
    (locInt_of_bdd hf hM)
  filter_upwards [h] with x hx
  have e : (fun n : ℕ => mol n f x) = fun n : ℕ =>
      ((bump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
    funext n; rw [mol_eq_conv]; rfl
  rw [e]; exact hx


/-! ### Convergence -/

theorem l2_mollify_tendsto {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : ∀ x, x ∉ K → f x = 0) :
    Tendsto (fun n : ℕ => L2u (fun x => f x - mol n f x)) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hKc : IsCompact (Metric.cthickening 1 K) := hK.cthickening
  have hcont : ∀ n : ℕ, Measurable fun x => f x - mol n f x := fun n =>
    hf.sub (contDiff_mol n hf hM).continuous.measurable
  have := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) x => ENNReal.ofReal ((f x - mol n f x) ^ 2)) (f := fun _ => 0)
    ((Metric.cthickening 1 K).indicator (fun _ => ENNReal.ofReal (4 * M ^ 2)))
    (fun n => ENNReal.measurable_ofReal.comp ((hcont n).pow_const 2))
    (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ Metric.cthickening 1 K
      · rw [Set.indicator_of_mem hx]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hM x
        have h2 := abs_mol_le hf hM (n := n) x
        have : |f x - mol n f x| ≤ 2 * M := by
          calc |f x - mol n f x| ≤ |f x| + |mol n f x| := abs_sub _ _
            _ ≤ 2 * M := by linarith
        nlinarith [sq_abs (f x - mol n f x), abs_nonneg (f x - mol n f x)]
      · rw [Set.indicator_of_notMem hx]
        have hxK : x ∉ K := fun h => hx (Metric.self_subset_cthickening K h)
        show ENNReal.ofReal ((f x - mol n f x) ^ 2) ≤ 0
        rw [hK0 x hxK, mol_eq_zero_of_far hK0 hx]
        simp)
    (by
      rw [lintegral_indicator_const hKc.isClosed.measurableSet]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKc.measure_lt_top.ne)
    ((mol_tendsto_ae hf hM).mono fun x hx => by
      have : Tendsto (fun n : ℕ => f x - mol n f x) atTop (𝓝 (f x - f x)) := tendsto_const_nhds.sub hx
      rw [sub_self] at this
      simpa using ENNReal.tendsto_ofReal ((this.pow 2)))
  simpa [L2u] using this

theorem mollify_energy {g : ℝ → ℝ} (hg : Measurable g) {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : ∀ x, x ∉ K → g x = 0) (hU : Eu g < ⊤) :
    Tendsto (fun n : ℕ => Eu (fun x => g x - mol n g x)) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hr : ∀ n : ℕ, Measurable fun x => g x - mol n g x := fun n =>
    hg.sub (contDiff_mol n hg hM).continuous.measurable
  -- the difference function `f_t`
  set ft : ℝ → ℝ → ℝ := fun t x => g x - g (x - t) with hft
  have hftm : ∀ t, Measurable (ft t) := fun t => hg.sub (hg.comp (measurable_id.sub measurable_const))
  have hftM : ∀ t x, |ft t x| ≤ 2 * M := fun t x => by
    calc |g x - g (x - t)| ≤ |g x| + |g (x - t)| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM x, hM (x - t)]
  have hshiftM : ∀ t x, |g (x - t)| ≤ M := fun t x => hM _
  have hshiftm : ∀ t, Measurable fun z => g (z - t) := fun t => hg.comp (measurable_id.sub measurable_const)
  -- identity of the difference
  have hid : ∀ n t x, (g x - mol n g x) - (g (x - t) - mol n g (x - t)) = ft t x - mol n (ft t) x := by
    intro n t x
    have e1 : mol n (ft t) x = mol n g x - mol n (fun z => g (z - t)) x :=
      mol_sub hg hM (hshiftm t) (hshiftM t) x
    rw [e1, mol_shift]
    simp only [hft]; ring
  have homega : ∀ n t, omega (fun x => g x - mol n g x) t = L2u (fun x => ft t x - mol n (ft t) x) := by
    intro n t
    unfold omega L2u
    refine lintegral_congr fun x => ?_
    rw [hid]
  -- support of f_t
  have hftK : ∀ t, ∀ x, x ∉ (K ∪ (fun y => y + t) '' K) → ft t x = 0 := by
    intro t x hx
    have h1 : x ∉ K := fun h => hx (Or.inl h)
    have h2 : x - t ∉ K := fun h => hx (Or.inr ⟨x - t, h, by ring⟩)
    simp only [hft, hK0 x h1, hK0 _ h2, sub_zero]
  have hKt : ∀ t, IsCompact (K ∪ (fun y => y + t) '' K) := fun t =>
    hK.union (hK.image (continuous_id.add continuous_const))
  -- pointwise limits
  have hlim : ∀ t, Tendsto (fun n : ℕ => omega (fun x => g x - mol n g x) t) atTop (𝓝 0) := by
    intro t
    simp_rw [homega]
    exact l2_mollify_tendsto (hftm t) (hftM t) (hKt t) (hftK t)
  -- domination
  have hdom : ∀ n t, omega (fun x => g x - mol n g x) t ≤ 4 * omega g t := by
    intro n t
    rw [homega]
    unfold L2u
    have hc : ∫⁻ x, ENNReal.ofReal ((ft t x - mol n (ft t) x) ^ 2) ≤
        ∫⁻ x, (2 * ENNReal.ofReal (ft t x ^ 2) + 2 * ENNReal.ofReal (mol n (ft t) x ^ 2)) := by
      refine lintegral_mono fun x => ?_
      rw [← ofReal_two_mul_add _ _ (sq_nonneg _) (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (ft t x + mol n (ft t) x)])
    refine le_trans hc ?_
    have hFm : Measurable fun x => ENNReal.ofReal (ft t x ^ 2) :=
      ENNReal.measurable_ofReal.comp ((hftm t).pow_const 2)
    rw [lintegral_two_mul_add (F := fun x => ENNReal.ofReal (ft t x ^ 2))
      (G := fun x => ENNReal.ofReal (mol n (ft t) x ^ 2)) hFm]
    have h2 := lintegral_mol_sq_le (n := n) (hftm t) (hftM t)
    have hωt : ∫⁻ x, ENNReal.ofReal (ft t x ^ 2) = omega g t := rfl
    rw [hωt] at h2 ⊢
    calc 2 * omega g t + 2 * ∫⁻ x, ENNReal.ofReal (mol n (ft t) x ^ 2) ≤ 2 * omega g t + 2 * omega g t := by
          gcongr
      _ = 4 * omega g t := by ring
  have e : ∀ n : ℕ, Eu (fun x => g x - mol n g x) =
      ∫⁻ t, ENNReal.ofReal (1 / t ^ 2) * omega (fun x => g x - mol n g x) t := fun n => Eu_eq (hr n)
  refine (tendsto_congr e).2 ?_
  have hm1 : Measurable fun t : ℝ => ENNReal.ofReal (1 / t ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_const.div (measurable_id.pow_const 2))
  have hfin : ∫⁻ t, ENNReal.ofReal (1 / t ^ 2) * (4 * omega g t) ≠ ⊤ := by
    have : ∫⁻ t, ENNReal.ofReal (1 / t ^ 2) * (4 * omega g t) = 4 * Eu g := by
      calc ∫⁻ t, ENNReal.ofReal (1 / t ^ 2) * (4 * omega g t)
          = ∫⁻ t, 4 * (ENNReal.ofReal (1 / t ^ 2) * omega g t) := lintegral_congr fun t => by ring
        _ = 4 * ∫⁻ t, ENNReal.ofReal (1 / t ^ 2) * omega g t := lintegral_const_mul' 4 _ (by simp)
        _ = 4 * Eu g := by rw [Eu_eq hg]
    rw [this]; exact ENNReal.mul_ne_top (by simp) hU.ne
  have := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) t => ENNReal.ofReal (1 / t ^ 2) * omega (fun x => g x - mol n g x) t)
    (f := fun _ => 0) (fun t => ENNReal.ofReal (1 / t ^ 2) * (4 * omega g t))
    (fun n => hm1.mul (measurable_omega (hr n)))
    (fun n => Eventually.of_forall fun t => by
      show ENNReal.ofReal (1 / t ^ 2) * omega (fun x => g x - mol n g x) t ≤
        ENNReal.ofReal (1 / t ^ 2) * (4 * omega g t)
      gcongr
      exact hdom n t)
    hfin
    (Eventually.of_forall fun t => by
      simpa using ENNReal.Tendsto.const_mul (hlim t) (Or.inr ENNReal.ofReal_ne_top))
  simpa using this


end QuantumNLS.FormCore

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.FormCore.Eu_eq
#print axioms QuantumNLS.FormCore.l2_mollify_tendsto
#print axioms QuantumNLS.FormCore.mollify_energy
