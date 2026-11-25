import QuantumNLS.SobolevSpaces

/-!
# F04:lem-local (R-501CA032): local mild solutions, uniqueness, stability

Source: `source/chapters/foundations/F04.tex`: equation `F04:eq-nls`
`i∂_t u = −∂_x²u + 2κ|u|²u` (lines 14-19, `L > 0`, `κ ≥ 0`), the conventions `p_n = 2πn/L`,
`û(n) = ⟨e_n, u⟩`, `‖f‖²_{H^s} = Σ (1+p_n²)^s |f̂(n)|²` (lines 21-31), Lemma `F04:lem-products`
(R-00E786F0, accepted: `eq:tame`, `eq:lipschitz` with `C_{s,L} = max{1, 3^{s+1}c_L²}`), Lemma
`F04:lem-local` (lines 130-147) and its proof (lines 149-…).

Realization: F04's `H^s` is the realized bracket-weight space; we work on its Fourier side
`h04 L s = WSeq (f04W L s)` (SobolevSpaces; `‖a‖² = Σ (1+p_n²)^s |a_n|²`, a Hilbert space for every
real `s`, so also `H^{s−2}` for `s < 2`); for `s ≥ 0` it is isometric to the field space
`H04sp L s ⊆ L²(𝕋_L)` (`fourierHs`). The linear group `S(t)` multiplies `a_n` by `e^{−itp_n²}`;
the nonlinearity `F(u) = |u|²u` is `Fh`, the coefficient sequence of `|u|²u` on the continuous
representative (`Fourier.nlRep`), with the accepted tame and Lipschitz bounds.

Proved (checkpoint LW1):
* `Sgrp`: the linear group (isometry, group law, strong and joint continuity);
* `Fh`, `norm_Fh_le`, `norm_Fh_sub_le`, `continuous_Fh`: `eq:tame`/`eq:lipschitz` on `h^s`;
* `duhamel`, `IsMild` (`F04:eq-duhamel`, Bochner interval integral in `h^s`), `duhamel_rebase`;
* `local_existence`: for `s ≥ 1`, `κ ≥ 0`, `u₀ ∈ H^s`, a mild solution on `[−τ, τ]` with the
  printed `τ = (64(1+κ)C_{s,L}R²)⁻¹`, `R = max{1, ‖u₀‖}`, by the contraction theorem on the
  radius-`2R` ball of `C([−τ,τ]; H^s)` (Lipschitz constant `≤ 1/4`);
* `mild_unique`: uniqueness of mild solutions on any common interval;
* `stability` (`F04:eq-stability`, all `s ≥ 1`; the printed case `s = 1` uses `C_{1,L}`):
  `‖u(t) − v(t)‖ ≤ exp(4κ C_{s,L} K² |t − t₀|) ‖u(t₀) − v(t₀)‖` for mild solutions bounded by `K`,
  via the integral Grönwall inequality (`gronwall_fwd`, `gronwall_bwd`).

Not proved here (gaps): `C¹_t H^{s−2}` regularity and the equation in `H^{s−2}`; the maximal
interval and the blow-up alternative; "every `C_tH¹` distributional solution is mild" (needs a
du Bois-Reymond lemma for vector/coefficient-valued distributions, absent from the pinned Mathlib).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory QuantumNLS.Fourier QuantumNLS.Sobolev QuantumNLS.Sobolev.PosWeight

namespace QuantumNLS.LocalWellPosedness

variable {L : ℝ} [Fact (0 < L)]

/-! ## 1. The linear group `S(t)` -/

/-- `e^{−itp_n²}`. -/
def phase (L t : ℝ) (n : ℤ) : ℂ := Complex.exp (-(Complex.I * ((t * freq L n ^ 2 : ℝ) : ℂ)))

lemma norm_phase (L t : ℝ) (n : ℤ) : ‖phase L t n‖ = 1 := by
  unfold phase
  rw [show -(Complex.I * ((t * freq L n ^ 2 : ℝ) : ℂ)) = ((-(t * freq L n ^ 2) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma phase_add (L t t' : ℝ) (n : ℤ) : phase L (t + t') n = phase L t n * phase L t' n := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

lemma phase_zero (L : ℝ) (n : ℤ) : phase L 0 n = 1 := by simp [phase]

lemma continuous_phase (L : ℝ) (n : ℤ) : Continuous fun t => phase L t n := by
  unfold phase
  fun_prop

/-- The sequence `(e^{−itp_n²} a_n)_n` stays in `h^s`. -/
lemma summable_phase_mul (s t : ℝ) (a : h04 L s) :
    Summable fun n => (f04W L s).w n * ‖phase L t n * a.val n‖ ^ 2 := by
  refine a.summable.congr fun n => ?_
  rw [norm_mul, norm_phase, one_mul]

/-- **The linear group** `S(t)` on `h^s`: `(S(t)a)_n = e^{−itp_n²} a_n`. -/
def Sgrp (s t : ℝ) : h04 L s →L[ℂ] h04 L s :=
  LinearMap.mkContinuous
    { toFun := fun a => WSeq.mk _ (fun n => phase L t n * a.val n) (summable_phase_mul s t a)
      map_add' := fun a b => WSeq.ext (by funext n; simp [mul_add])
      map_smul' := fun c a => WSeq.ext (by funext n; simp; ring) }
    1 (fun a => by
      rw [one_mul]
      apply le_of_eq
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_tsum, norm_sq_eq_tsum]
      refine tsum_congr fun n => ?_
      simp only [LinearMap.coe_mk, AddHom.coe_mk, WSeq.val_mk]
      rw [norm_mul, norm_phase, one_mul])

@[simp] lemma Sgrp_val (s t : ℝ) (a : h04 L s) (n : ℤ) :
    (Sgrp s t a).val n = phase L t n * a.val n := rfl

/-- `S(t)` is an isometry. -/
lemma norm_Sgrp (s t : ℝ) (a : h04 L s) : ‖Sgrp s t a‖ = ‖a‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_tsum, norm_sq_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [Sgrp_val, norm_mul, norm_phase, one_mul]

lemma Sgrp_add (s t t' : ℝ) (a : h04 L s) : Sgrp s (t + t') a = Sgrp s t (Sgrp s t' a) :=
  WSeq.ext (by funext n; simp [phase_add, mul_assoc])

lemma Sgrp_zero (s : ℝ) (a : h04 L s) : Sgrp s 0 a = a :=
  WSeq.ext (by funext n; simp [phase_zero])

/-- **Strong continuity**: `t ↦ S(t)a` is continuous in `h^s`. -/
lemma continuous_Sgrp_apply (s : ℝ) (a : h04 L s) : Continuous fun t => Sgrp s t a := by
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun t => ‖Sgrp s t a - Sgrp s t0 a‖ ^ 2) (𝓝 t0) (𝓝 0) := by
    have e : ∀ t, ‖Sgrp s t a - Sgrp s t0 a‖ ^ 2 =
        ∑' n, (f04W L s).w n * ‖(phase L t n - phase L t0 n) * a.val n‖ ^ 2 := by
      intro t
      rw [norm_sq_eq_tsum]
      refine tsum_congr fun n => ?_
      simp [sub_mul]
    simp_rw [e]
    have h0 : (0 : ℝ) = ∑' n : ℤ, (fun _ => (0 : ℝ)) n := by simp
    rw [h0]
    refine tendsto_tsum_of_dominated_convergence (bound := fun n => 4 * ((f04W L s).w n *
      ‖a.val n‖ ^ 2)) (a.summable.mul_left 4) (fun n => ?_) (Eventually.of_forall fun t n => ?_)
    · have hc : Continuous fun t => (f04W L s).w n * ‖(phase L t n - phase L t0 n) * a.val n‖ ^ 2 :=
        continuous_const.mul ((((continuous_phase L n).sub continuous_const).mul
          continuous_const).norm.pow 2)
      have := hc.tendsto t0
      simpa using this
    · have hw := (f04W L s).pos n
      have h1 : ‖phase L t n - phase L t0 n‖ ≤ 2 := by
        calc _ ≤ ‖phase L t n‖ + ‖phase L t0 n‖ := norm_sub_le _ _
          _ = 2 := by rw [norm_phase, norm_phase]; norm_num
      rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_pow]
      have h2 : ‖phase L t n - phase L t0 n‖ ^ 2 ≤ 4 := by
        nlinarith [norm_nonneg (phase L t n - phase L t0 n)]
      have := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖a.val n‖)
      nlinarith
  have := hsq.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using this

/-- Joint continuity: `‖S(t)w − S(t₀)w₀‖ ≤ ‖w − w₀‖ + ‖S(t)w₀ − S(t₀)w₀‖`. -/
lemma continuous_Sgrp (s : ℝ) {w : ℝ → h04 L s} (hw : Continuous w) :
    Continuous fun t => Sgrp s t (w t) := by
  rw [continuous_iff_continuousAt]
  intro t0
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun t => ‖w t - w t0‖ + ‖Sgrp s t (w t0) - Sgrp s t0 (w t0)‖) (𝓝 t0)
      (𝓝 (0 + 0)) := by
    refine Tendsto.add ?_ ?_
    · exact (tendsto_iff_norm_sub_tendsto_zero.mp (hw.tendsto t0))
    · exact (tendsto_iff_norm_sub_tendsto_zero.mp ((continuous_Sgrp_apply s (w t0)).tendsto t0))
  rw [add_zero] at h1
  refine squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_) h1
  calc ‖Sgrp s t (w t) - Sgrp s t0 (w t0)‖
      = ‖Sgrp s t (w t - w t0) + (Sgrp s t (w t0) - Sgrp s t0 (w t0))‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖Sgrp s t (w t - w t0)‖ + ‖Sgrp s t (w t0) - Sgrp s t0 (w t0)‖ := norm_add_le _ _
    _ = _ := by rw [norm_Sgrp]

/-! ## 2. The nonlinearity `F(u) = |u|²u` on `h^s`, `s ≥ 1` -/

/-- The F04 constant `C_{s,L} = max{1, 3^{s+1} c_L²}`. -/
def Cs (L s : ℝ) : ℝ := max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2)

lemma one_le_Cs (L s : ℝ) : 1 ≤ Cs L s := le_max_left _ _

lemma norm_eq_sqrt (s : ℝ) (a : h04 L s) : ‖a‖ = Real.sqrt (f04NormSq L s a.val) := by
  rw [← Real.sqrt_sq (norm_nonneg a), norm_sq_eq_tsum]; rfl

/-- `F(u)` as an element of `h^s`. -/
def Fh {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) : h04 L s :=
  WSeq.mk _ (coeff L (nlRep L a.val)) (f04_tame hs (h04_mem L s a)).1

lemma norm_one_le {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) :
    Real.sqrt (f04NormSq L 1 a.val) ≤ ‖a‖ := by
  rw [norm_eq_sqrt]
  exact Real.sqrt_le_sqrt (f04NormSq_mono hs (h04_mem L s a))

/-- **`eq:tame`** on `h^s`: `‖F(u)‖_s ≤ C_{s,L} ‖u‖_1² ‖u‖_s ≤ C_{s,L} ‖u‖_s³`. -/
lemma norm_Fh_le {s : ℝ} (hs : 1 ≤ s) (a : h04 L s) : ‖Fh hs a‖ ≤ Cs L s * ‖a‖ ^ 3 := by
  have h := (f04_tame hs (h04_mem L s a)).2
  rw [norm_eq_sqrt]
  refine h.trans ?_
  rw [← norm_eq_sqrt]
  have h1 := norm_one_le hs a
  have h0 := Real.sqrt_nonneg (f04NormSq L 1 a.val)
  have hC : 0 ≤ Cs L s := le_trans zero_le_one (one_le_Cs L s)
  unfold Cs at hC ⊢
  have : Real.sqrt (f04NormSq L 1 a.val) ^ 2 ≤ ‖a‖ ^ 2 := pow_le_pow_left₀ h0 h1 2
  calc max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * Real.sqrt (f04NormSq L 1 a.val) ^ 2 * ‖a‖
      ≤ max 1 ((3 : ℝ) ^ (s + 1) * cL L ^ 2) * ‖a‖ ^ 2 * ‖a‖ := by gcongr
    _ = _ := by ring

/-- **`eq:lipschitz`** on `h^s`: `‖F(u) − F(v)‖_s ≤ C_{s,L} (‖u‖_s² + ‖v‖_s²) ‖u − v‖_s`. -/
lemma norm_Fh_sub_le {s : ℝ} (hs : 1 ≤ s) (a b : h04 L s) :
    ‖Fh hs a - Fh hs b‖ ≤ Cs L s * (‖a‖ ^ 2 + ‖b‖ ^ 2) * ‖a - b‖ := by
  have h := (f04_lipschitz hs (h04_mem L s a) (h04_mem L s b)).2
  rw [norm_eq_sqrt, norm_eq_sqrt (s := s) (a - b), norm_eq_sqrt (s := s) a,
    norm_eq_sqrt (s := s) b]
  exact h

lemma continuous_Fh {s : ℝ} (hs : 1 ≤ s) : Continuous (Fh (L := L) hs) := by
  rw [Metric.continuous_iff]
  intro b ε hε
  set K := ‖b‖ + 1
  have hC0 : 0 ≤ Cs L s := le_trans zero_le_one (one_le_Cs L s)
  have hD0 : 0 < Cs L s * 2 * K ^ 2 + 1 := by positivity
  refine ⟨min 1 (ε / (Cs L s * 2 * K ^ 2 + 1)), lt_min one_pos (div_pos hε hD0), fun a ha => ?_⟩
  rw [dist_eq_norm] at ha ⊢
  have ha1 : ‖a - b‖ < 1 := lt_of_lt_of_le ha (min_le_left _ _)
  have ha2 : ‖a - b‖ < ε / (Cs L s * 2 * K ^ 2 + 1) := lt_of_lt_of_le ha (min_le_right _ _)
  have hnA : ‖a‖ ≤ K := by
    have := norm_le_insert' a b; linarith [norm_sub_rev a b]
  have hC : 0 ≤ Cs L s := le_trans zero_le_one (one_le_Cs L s)
  have hL := norm_Fh_sub_le hs a b
  have hab : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ 2 * K ^ 2 := by
    have h1 : ‖a‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnA 2
    have h2 : ‖b‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
    linarith
  have hD : 0 < Cs L s * 2 * K ^ 2 + 1 := by positivity
  calc ‖Fh hs a - Fh hs b‖ ≤ Cs L s * (‖a‖ ^ 2 + ‖b‖ ^ 2) * ‖a - b‖ := hL
    _ ≤ (Cs L s * 2 * K ^ 2 + 1) * ‖a - b‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        nlinarith
    _ < (Cs L s * 2 * K ^ 2 + 1) * (ε / (Cs L s * 2 * K ^ 2 + 1)) :=
        mul_lt_mul_of_pos_left ha2 hD
    _ = ε := by field_simp

#print axioms continuous_Sgrp
#print axioms norm_Fh_le
#print axioms norm_Fh_sub_le
#print axioms continuous_Fh

/-! ## 3. Grönwall's inequality in integral form -/

/-- Forward integral Grönwall: `φ ≤ a + b ∫_{t₀}^r φ` on `[t₀, T]` gives `φ(r) ≤ a e^{b(r−t₀)}`. -/
lemma gronwall_fwd {φ : ℝ → ℝ} (hφ : Continuous φ) {a b t0 T : ℝ} (hb : 0 ≤ b)
    (h : ∀ r ∈ Set.Icc t0 T, φ r ≤ a + b * ∫ x in t0..r, φ x) :
    ∀ r ∈ Set.Icc t0 T, φ r ≤ a * Real.exp (b * (r - t0)) := by
  set Ψ : ℝ → ℝ := fun r => a + b * ∫ x in t0..r, φ x
  have hΨ : ∀ r, HasDerivAt Ψ (b * φ r) r := fun r =>
    ((hφ.integral_hasStrictDerivAt t0 r).hasDerivAt.const_mul b).const_add a
  set G : ℝ → ℝ := fun r => Real.exp (-(b * (r - t0))) * Ψ r
  have hG : ∀ r, HasDerivAt G (Real.exp (-(b * (r - t0))) * (b * φ r - b * Ψ r)) r := by
    intro r
    have h1 : HasDerivAt (fun r => -(b * (r - t0))) (-b) r := by
      have := ((hasDerivAt_id r).const_mul (-b)).add_const (b * t0)
      convert this using 1
      · funext x; simp only [id]; ring
      · ring
    have := (h1.exp).mul (hΨ r)
    convert this using 1; ring
  have hanti : AntitoneOn G (Set.Icc t0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc t0 T)
      (fun r _ => (hG r).continuousAt.continuousWithinAt)
      (fun r _ => (hG r).differentiableAt.differentiableWithinAt) fun r hr => ?_
    rw [(hG r).deriv, interior_Icc] at *
    have hr' : r ∈ Set.Icc t0 T := Set.Ioo_subset_Icc_self hr
    have := h r hr'
    have he := Real.exp_pos (-(b * (r - t0)))
    have : b * φ r - b * Ψ r ≤ 0 := by
      have : φ r ≤ Ψ r := this
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos he.le this
  intro r hr
  have hG0 : G t0 = a := by simp [G, Ψ]
  have hGr := hanti ⟨le_rfl, le_trans hr.1 hr.2⟩ hr hr.1
  rw [hG0] at hGr
  have hΨr : Ψ r ≤ a * Real.exp (b * (r - t0)) := by
    have he := Real.exp_pos (b * (r - t0))
    have : Real.exp (-(b * (r - t0))) * Ψ r ≤ a := hGr
    rw [Real.exp_neg] at this
    rw [inv_mul_le_iff₀ he] at this
    linarith
  exact (h r hr).trans hΨr

/-- Backward integral Grönwall: `φ ≤ a + b ∫_r^{t₀} φ` on `[T, t₀]` gives `φ(r) ≤ a e^{b(t₀−r)}`. -/
lemma gronwall_bwd {φ : ℝ → ℝ} (hφ : Continuous φ) {a b t0 T : ℝ} (hb : 0 ≤ b)
    (h : ∀ r ∈ Set.Icc T t0, φ r ≤ a + b * ∫ x in r..t0, φ x) :
    ∀ r ∈ Set.Icc T t0, φ r ≤ a * Real.exp (b * (t0 - r)) := by
  set ψ : ℝ → ℝ := fun x => φ (2 * t0 - x)
  have hψ : Continuous ψ := hφ.comp (continuous_const.sub continuous_id)
  have h' : ∀ r ∈ Set.Icc t0 (2 * t0 - T), ψ r ≤ a + b * ∫ x in t0..r, ψ x := by
    intro r hr
    have := h (2 * t0 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have e : ∫ x in t0..r, ψ x = ∫ x in (2 * t0 - r)..t0, φ x := by
      have := intervalIntegral.integral_comp_sub_left (a := t0) (b := r) φ (2 * t0)
      rw [this]; congr 1; ring
    simp only [ψ]; rw [e]; exact this
  intro r hr
  have := gronwall_fwd hψ hb h' (2 * t0 - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  simp only [ψ, show 2 * t0 - (2 * t0 - r) = r by ring] at this
  rwa [show 2 * t0 - r - t0 = t0 - r by ring] at this

/-! ## 4. Mild solutions -/

/-- The Duhamel map `S(t)u₀ − 2iκ ∫_0^t S(t−r) F(u(r)) dr` (`F04:eq-duhamel`). -/
def duhamel {s : ℝ} (hs : 1 ≤ s) (κ : ℝ) (u0 : h04 L s) (u : ℝ → h04 L s) (t : ℝ) : h04 L s :=
  Sgrp s t u0 - (2 * Complex.I * κ) • ∫ r in (0 : ℝ)..t, Sgrp s (t - r) (Fh hs (u r))

/-- A **mild solution** on an interval `I ∋ 0`: continuous `h^s`-valued and equal to its Duhamel
formula at every time of `I`. -/
structure IsMild {s : ℝ} (hs : 1 ≤ s) (κ : ℝ) (I : Set ℝ) (u0 : h04 L s) (u : ℝ → h04 L s) :
    Prop where
  zero_mem : (0 : ℝ) ∈ I
  ordConnected : I.OrdConnected
  cont : ContinuousOn u I
  duhamel_eq : ∀ t ∈ I, u t = duhamel hs κ u0 u t

lemma continuousOn_Sgrp {s : ℝ} {S : Set ℝ} {τ : ℝ → ℝ} (hτ : Continuous τ) {w : ℝ → h04 L s}
    (hw : ContinuousOn w S) : ContinuousOn (fun r => Sgrp s (τ r) (w r)) S := by
  intro r0 hr0
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun r => ‖w r - w r0‖ + ‖Sgrp s (τ r) (w r0) - Sgrp s (τ r0) (w r0)‖)
      (𝓝[S] r0) (𝓝 (0 + 0)) := by
    refine Tendsto.add ?_ ?_
    · exact tendsto_iff_norm_sub_tendsto_zero.mp (hw r0 hr0)
    · have := ((continuous_Sgrp_apply s (w r0)).comp hτ).tendsto r0
      exact tendsto_iff_norm_sub_tendsto_zero.mp (this.mono_left nhdsWithin_le_nhds)
  rw [add_zero] at h1
  refine squeeze_zero (fun _ => norm_nonneg _) (fun r => ?_) h1
  calc ‖Sgrp s (τ r) (w r) - Sgrp s (τ r0) (w r0)‖
      = ‖Sgrp s (τ r) (w r - w r0) + (Sgrp s (τ r) (w r0) - Sgrp s (τ r0) (w r0))‖ := by
        rw [map_sub]; congr 1; abel
    _ ≤ ‖Sgrp s (τ r) (w r - w r0)‖ + ‖Sgrp s (τ r) (w r0) - Sgrp s (τ r0) (w r0)‖ :=
        norm_add_le _ _
    _ = _ := by rw [norm_Sgrp]

/-- The Duhamel integrand is interval-integrable between two times of `I`. -/
lemma integrable_duhamel {s : ℝ} (hs : 1 ≤ s) {I : Set ℝ} (hI : I.OrdConnected)
    {u : ℝ → h04 L s} (hu : ContinuousOn u I) (t a b : ℝ) (ha : a ∈ I) (hb : b ∈ I) :
    IntervalIntegrable (fun r => Sgrp s (t - r) (Fh hs (u r))) volume a b := by
  refine ContinuousOn.intervalIntegrable ?_
  have hsub : Set.uIcc a b ⊆ I := hI.uIcc_subset ha hb
  exact continuousOn_Sgrp (continuous_const.sub continuous_id)
    ((continuous_Fh hs).comp_continuousOn (hu.mono hsub))

/-- **Duhamel based at any time** `t₀ ∈ I`. -/
lemma duhamel_rebase {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} {I : Set ℝ} {u0 : h04 L s} {u : ℝ → h04 L s}
    (hu : IsMild hs κ I u0 u) {t0 t : ℝ} (ht0 : t0 ∈ I) (ht : t ∈ I) :
    u t = Sgrp s (t - t0) (u t0) -
      (2 * Complex.I * κ) • ∫ r in t0..t, Sgrp s (t - r) (Fh hs (u r)) := by
  have h0 := hu.zero_mem
  have i1 := integrable_duhamel hs hu.ordConnected hu.cont t 0 t0 h0 ht0
  have i2 := integrable_duhamel hs hu.ordConnected hu.cont t t0 t ht0 ht
  have i3 := integrable_duhamel hs hu.ordConnected hu.cont t0 0 t0 h0 ht0
  rw [hu.duhamel_eq t ht, hu.duhamel_eq t0 ht0]
  unfold duhamel
  rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, map_sub, map_smul,
    ← Sgrp_add, show t - t0 + t0 = t by ring]
  have hcomm : Sgrp s (t - t0) (∫ r in (0 : ℝ)..t0, Sgrp s (t0 - r) (Fh hs (u r))) =
      ∫ r in (0 : ℝ)..t0, Sgrp s (t - r) (Fh hs (u r)) := by
    rw [← (Sgrp s (t - t0)).intervalIntegral_comp_comm i3]
    refine intervalIntegral.integral_congr fun r _ => ?_
    rw [← Sgrp_add, show t - t0 + (t0 - r) = t - r by ring]
  rw [hcomm, smul_add]
  abel

/-! ## 5. Stability and uniqueness -/

/-- `|∫_a^b f| ≤ |∫_a^b g|` for `0 ≤ f ≤ g` on `[a, b]`. -/
lemma abs_integral_le_of_le {f g : ℝ → ℝ} {a b : ℝ} (hf0 : ∀ x ∈ Set.uIcc a b, 0 ≤ f x)
    (hfg : ∀ x ∈ Set.uIcc a b, f x ≤ g x) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) :
    |∫ x in a..b, f x| ≤ |∫ x in a..b, g x| := by
  rcases le_total a b with h | h
  · have h1 := intervalIntegral.integral_mono_on h hf hg fun x hx =>
      hfg x (Set.Icc_subset_uIcc hx)
    have h2 := intervalIntegral.integral_nonneg (μ := volume) h fun x hx => hf0 x (Set.Icc_subset_uIcc hx)
    rw [abs_of_nonneg h2, abs_of_nonneg (h2.trans h1)]; exact h1
  · have h1 := intervalIntegral.integral_mono_on h hf.symm hg.symm fun x hx =>
      hfg x (Set.Icc_subset_uIcc' hx)
    have h2 := intervalIntegral.integral_nonneg (μ := volume) h fun x hx => hf0 x (Set.Icc_subset_uIcc' hx)
    rw [intervalIntegral.integral_symm (f := f) b a, intervalIntegral.integral_symm (f := g) b a, abs_neg,
      abs_neg, abs_of_nonneg h2, abs_of_nonneg (h2.trans h1)]
    exact h1

lemma norm_coef (κ : ℝ) (hκ : 0 ≤ κ) : ‖(2 * Complex.I * κ : ℂ)‖ = 2 * κ := by
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hκ]
  norm_num

/-- **`F04:eq-stability`** (for every `s ≥ 1`; the printed case is `s = 1`): for two mild
solutions with norms `≤ K` on `I` and `t₀, t ∈ I`,
`‖u(t) − v(t)‖ ≤ exp(4κ C_{s,L} K² |t − t₀|) ‖u(t₀) − v(t₀)‖`. -/
theorem stability {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} (hκ : 0 ≤ κ) {I : Set ℝ} {u0 v0 : h04 L s}
    {u v : ℝ → h04 L s} (hu : IsMild hs κ I u0 u) (hv : IsMild hs κ I v0 v) {K : ℝ}
    (hK : ∀ r ∈ I, ‖u r‖ ≤ K ∧ ‖v r‖ ≤ K) {t0 t : ℝ} (ht0 : t0 ∈ I) (ht : t ∈ I) :
    ‖u t - v t‖ ≤ Real.exp (4 * κ * Cs L s * K ^ 2 * |t - t0|) * ‖u t0 - v t0‖ := by
  set c := Cs L s
  have hc : 0 ≤ c := le_trans zero_le_one (one_le_Cs L s)
  set b := 4 * κ * c * K ^ 2
  have hb : 0 ≤ b := by positivity
  set a := ‖u t0 - v t0‖
  have hsub : Set.uIcc t0 t ⊆ I := hu.ordConnected.uIcc_subset ht0 ht
  -- continuous extension of `φ` from `[t0, t]`
  set lo := min t0 t
  set hi := max t0 t
  have hlohi : lo ≤ hi := min_le_max
  set φ0 : ℝ → ℝ := fun r => ‖u r - v r‖
  have hφ0 : ContinuousOn φ0 (Set.Icc lo hi) := by
    have := (hu.cont.mono hsub).sub (hv.cont.mono hsub)
    exact this.norm
  set φ : ℝ → ℝ := fun r => φ0 (Set.projIcc lo hi hlohi r)
  have hφ : Continuous φ := hφ0.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun r => (Set.projIcc lo hi hlohi r).2)
  have hφeq : ∀ r ∈ Set.Icc lo hi, φ r = φ0 r := fun r hr => by
    simp only [φ, Set.projIcc_of_mem hlohi hr]
  -- the key pointwise bound
  have key : ∀ r ∈ Set.uIcc t0 t, φ0 r ≤ a + b * |∫ x in t0..r, φ x| := by
    intro r hr
    have hrI := hsub hr
    have hdiff : u r - v r = Sgrp s (r - t0) (u t0 - v t0) -
        (2 * Complex.I * κ) • ∫ x in t0..r, Sgrp s (r - x) (Fh hs (u x) - Fh hs (v x)) := by
      rw [duhamel_rebase hs hu ht0 hrI, duhamel_rebase hs hv ht0 hrI, map_sub]
      have i1 := integrable_duhamel hs hu.ordConnected hu.cont r t0 r ht0 hrI
      have i2 := integrable_duhamel hs hv.ordConnected hv.cont r t0 r ht0 hrI
      have : ∫ x in t0..r, Sgrp s (r - x) (Fh hs (u x) - Fh hs (v x)) =
          (∫ x in t0..r, Sgrp s (r - x) (Fh hs (u x))) -
            ∫ x in t0..r, Sgrp s (r - x) (Fh hs (v x)) := by
        rw [← intervalIntegral.integral_sub i1 i2]
        exact intervalIntegral.integral_congr fun x _ => by simp only [map_sub]
      rw [this, smul_sub]; abel
    have hsubr : Set.uIcc t0 r ⊆ Set.uIcc t0 t := Set.uIcc_subset_uIcc_left hr
    have hpt : ∀ x ∈ Set.uIcc t0 r,
        ‖Sgrp s (r - x) (Fh hs (u x) - Fh hs (v x))‖ ≤ (2 * c * K ^ 2) * φ x := by
      intro x hx
      have hxI := hsub (hsubr hx)
      rw [norm_Sgrp]
      have hl := norm_Fh_sub_le hs (u x) (v x)
      obtain ⟨hKu, hKv⟩ := hK x hxI
      have hK0 : 0 ≤ K := (norm_nonneg _).trans hKu
      have h2 : ‖u x‖ ^ 2 + ‖v x‖ ^ 2 ≤ 2 * K ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hKu 2
        have := pow_le_pow_left₀ (norm_nonneg _) hKv 2
        linarith
      have hφx : φ x = ‖u x - v x‖ := hφeq x (hsubr hx)
      rw [hφx]
      calc ‖Fh hs (u x) - Fh hs (v x)‖ ≤ c * (‖u x‖ ^ 2 + ‖v x‖ ^ 2) * ‖u x - v x‖ := hl
        _ ≤ c * (2 * K ^ 2) * ‖u x - v x‖ := by gcongr
        _ = _ := by ring
    have hgc : ContinuousOn (fun x => ‖Sgrp s (r - x) (Fh hs (u x) - Fh hs (v x))‖)
        (Set.uIcc t0 r) := by
      have hu' := hu.cont.mono (hsubr.trans hsub)
      have hv' := hv.cont.mono (hsubr.trans hsub)
      exact (continuousOn_Sgrp (continuous_const.sub continuous_id)
        (((continuous_Fh hs).comp_continuousOn hu').sub
          ((continuous_Fh hs).comp_continuousOn hv'))).norm
    have hint := abs_integral_le_of_le (fun x hx => norm_nonneg _) hpt hgc.intervalIntegrable
      ((hφ.const_mul _).intervalIntegrable _ _)
    have hn : ‖u r - v r‖ ≤ a + 2 * κ *
        |∫ x in t0..r, ‖Sgrp s (r - x) (Fh hs (u x) - Fh hs (v x))‖| := by
      rw [hdiff]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_Sgrp, norm_smul, norm_coef κ hκ]
      have := intervalIntegral.norm_integral_le_abs_integral_norm (μ := volume) (a := t0) (b := r)
        (f := fun x => Sgrp s (r - x) (Fh hs (u x) - Fh hs (v x)))
      nlinarith
    have hlin : |∫ x in t0..r, (2 * c * K ^ 2) * φ x| = (2 * c * K ^ 2) * |∫ x in t0..r, φ x| := by
      rw [intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg (by positivity)]
    show ‖u r - v r‖ ≤ a + b * |∫ x in t0..r, φ x|
    rw [hlin] at hint
    have hb' : b = 2 * κ * (2 * c * K ^ 2) := by simp only [b]; ring
    rw [hb']
    nlinarith
  -- Grönwall in each direction
  rcases le_total t0 t with h | h
  · have hfwd : ∀ r ∈ Set.Icc t0 t, φ r ≤ a + b * ∫ x in t0..r, φ x := by
      intro r hr
      have hrI : r ∈ Set.uIcc t0 t := Set.Icc_subset_uIcc hr
      have hmem : r ∈ Set.Icc lo hi := hrI
      rw [hφeq r hmem]
      have := key r hrI
      rwa [abs_of_nonneg (intervalIntegral.integral_nonneg hr.1 fun x _ => norm_nonneg _)] at this
    have := gronwall_fwd hφ hb hfwd t ⟨h, le_rfl⟩
    rw [hφeq t (Set.right_mem_uIcc)] at this
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [mul_comm a (Real.exp (b * (t - t0)))]
  · have hbwd : ∀ r ∈ Set.Icc t t0, φ r ≤ a + b * ∫ x in r..t0, φ x := by
      intro r hr
      have hrI : r ∈ Set.uIcc t0 t := Set.Icc_subset_uIcc' hr
      have hmem : r ∈ Set.Icc lo hi := hrI
      rw [hφeq r hmem]
      have := key r hrI
      rwa [intervalIntegral.integral_symm, abs_neg,
        abs_of_nonneg (intervalIntegral.integral_nonneg hr.2 fun x _ => norm_nonneg _)] at this
    have := gronwall_bwd hφ hb hbwd t ⟨le_rfl, h⟩
    rw [hφeq t (Set.right_mem_uIcc)] at this
    rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    linarith [mul_comm a (Real.exp (b * (t0 - t)))]

/-- Restriction of a mild solution to a smaller interval containing `0`. -/
lemma IsMild.mono {s : ℝ} {hs : 1 ≤ s} {κ : ℝ} {I J : Set ℝ} {u0 : h04 L s} {u : ℝ → h04 L s}
    (hu : IsMild hs κ I u0 u) (hJ : J ⊆ I) (h0 : (0 : ℝ) ∈ J) (hJc : J.OrdConnected) :
    IsMild hs κ J u0 u :=
  ⟨h0, hJc, hu.cont.mono hJ, fun t ht => hu.duhamel_eq t (hJ ht)⟩

lemma IsMild.at_zero {s : ℝ} {hs : 1 ≤ s} {κ : ℝ} {I : Set ℝ} {u0 : h04 L s} {u : ℝ → h04 L s}
    (hu : IsMild hs κ I u0 u) : u 0 = u0 := by
  rw [hu.duhamel_eq 0 hu.zero_mem]; simp [duhamel, Sgrp_zero]

/-- **Uniqueness of mild solutions**: two mild solutions with the same initial value agree on the
common interval. -/
theorem mild_unique {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} (hκ : 0 ≤ κ) {I : Set ℝ} {u0 : h04 L s}
    {u v : ℝ → h04 L s} (hu : IsMild hs κ I u0 u) (hv : IsMild hs κ I u0 v) :
    ∀ t ∈ I, u t = v t := by
  intro t ht
  set J := Set.uIcc 0 t
  have hJ : J ⊆ I := hu.ordConnected.uIcc_subset hu.zero_mem ht
  have hu' := hu.mono hJ Set.left_mem_uIcc Set.ordConnected_uIcc
  have hv' := hv.mono hJ Set.left_mem_uIcc Set.ordConnected_uIcc
  obtain ⟨K1, hK1⟩ := isCompact_uIcc.exists_bound_of_continuousOn hu'.cont
  obtain ⟨K2, hK2⟩ := isCompact_uIcc.exists_bound_of_continuousOn hv'.cont
  have := stability hs hκ hu' hv' (K := max K1 K2)
    (fun r hr => ⟨(hK1 r hr).trans (le_max_left _ _), (hK2 r hr).trans (le_max_right _ _)⟩)
    Set.left_mem_uIcc Set.right_mem_uIcc
  rw [hu.at_zero, hv.at_zero, sub_self, norm_zero, mul_zero] at this
  exact sub_eq_zero.mp (norm_le_zero_iff.mp this)

#print axioms gronwall_fwd
#print axioms gronwall_bwd
#print axioms duhamel_rebase
#print axioms stability
#print axioms mild_unique

/-! ## 6. Local existence by contraction -/

/-- `∫_0^t S(t−r) g(r) dr = S(t) ∫_0^t S(−r) g(r) dr`. -/
lemma duhamel_integral_eq {s : ℝ} {g : ℝ → h04 L s} (hg : Continuous g) (t : ℝ) :
    ∫ r in (0 : ℝ)..t, Sgrp s (t - r) (g r) = Sgrp s t (∫ r in (0 : ℝ)..t, Sgrp s (-r) (g r)) := by
  have hi : IntervalIntegrable (fun r => Sgrp s (-r) (g r)) volume 0 t :=
    (continuousOn_Sgrp continuous_neg hg.continuousOn).intervalIntegrable
  rw [← (Sgrp s t).intervalIntegral_comp_comm hi]
  refine intervalIntegral.integral_congr fun r _ => ?_
  rw [← Sgrp_add, sub_eq_add_neg]

lemma continuous_duhamel {s : ℝ} (hs : 1 ≤ s) (κ : ℝ) (u0 : h04 L s) {u : ℝ → h04 L s}
    (hu : Continuous u) : Continuous (duhamel hs κ u0 u) := by
  have hg : Continuous fun r => Fh hs (u r) := (continuous_Fh hs).comp hu
  have hw : Continuous fun t => ∫ r in (0 : ℝ)..t, Sgrp s (-r) (Fh hs (u r)) :=
    intervalIntegral.continuous_primitive (fun a b =>
      (continuousOn_Sgrp continuous_neg hg.continuousOn).intervalIntegrable) 0
  unfold duhamel
  simp_rw [duhamel_integral_eq hg]
  exact (continuous_Sgrp_apply s u0).sub ((continuous_Sgrp s hw).const_smul (2 * Complex.I * κ))

lemma duhamel_sub {s : ℝ} (hs : 1 ≤ s) (κ : ℝ) (u0 : h04 L s) {u w : ℝ → h04 L s}
    (hu : Continuous u) (hw : Continuous w) (t : ℝ) :
    duhamel hs κ u0 u t - duhamel hs κ u0 w t =
      -((2 * Complex.I * κ) • ∫ r in (0 : ℝ)..t, Sgrp s (t - r) (Fh hs (u r) - Fh hs (w r))) := by
  have hiu : IntervalIntegrable (fun r => Sgrp s (t - r) (Fh hs (u r))) volume 0 t :=
    (continuousOn_Sgrp (continuous_const.sub continuous_id)
      ((continuous_Fh hs).comp hu).continuousOn).intervalIntegrable
  have hiw : IntervalIntegrable (fun r => Sgrp s (t - r) (Fh hs (w r))) volume 0 t :=
    (continuousOn_Sgrp (continuous_const.sub continuous_id)
      ((continuous_Fh hs).comp hw).continuousOn).intervalIntegrable
  have hsplit : ∫ r in (0 : ℝ)..t, Sgrp s (t - r) (Fh hs (u r) - Fh hs (w r)) =
      (∫ r in (0 : ℝ)..t, Sgrp s (t - r) (Fh hs (u r))) -
        ∫ r in (0 : ℝ)..t, Sgrp s (t - r) (Fh hs (w r)) := by
    rw [← intervalIntegral.integral_sub hiu hiw]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [map_sub]
  unfold duhamel
  rw [hsplit, smul_sub]
  abel

/-- The printed existence time `τ = (64(1+κ) C_{s,L} R²)⁻¹`, `R = max{1, ‖u₀‖}`. -/
def tau (L s κ : ℝ) {L' : ℝ} [Fact (0 < L')] (u0 : h04 L' s) : ℝ :=
  (64 * (1 + κ) * Cs L s * (max 1 ‖u0‖) ^ 2)⁻¹

/-- **Local existence**: for `s ≥ 1`, `κ ≥ 0` and `u₀ ∈ H^s`, a mild solution exists on
`[−τ, τ]` with the printed `τ > 0`. -/
theorem local_existence {s : ℝ} (hs : 1 ≤ s) {κ : ℝ} (hκ : 0 ≤ κ) (u0 : h04 L s) :
    0 < tau L s κ u0 ∧ ∃ u : ℝ → h04 L s, IsMild hs κ (Set.Icc (-tau L s κ u0) (tau L s κ u0)) u0 u ∧
      ∀ t, ‖u t‖ ≤ 2 * max 1 ‖u0‖ := by
  set R := max 1 ‖u0‖ with hRdef
  set C := Cs L s
  have hC : 1 ≤ C := one_le_Cs L s
  have hR : 1 ≤ R := le_max_left _ _
  set τ := tau L s κ u0 with hτdef
  have hτ : 0 < τ := by
    rw [hτdef, tau]; positivity
  have hτR : 16 * κ * τ * C * R ^ 2 ≤ 1 / 4 := by
    rw [hτdef, tau, ← hRdef]
    have hD : 0 < 64 * (1 + κ) * C * R ^ 2 := by positivity
    rw [show 16 * κ * (64 * (1 + κ) * C * R ^ 2)⁻¹ * C * R ^ 2 =
      16 * κ * C * R ^ 2 / (64 * (1 + κ) * C * R ^ 2) by field_simp]
    rw [div_le_iff₀ hD]
    have : 0 ≤ C * R ^ 2 := by positivity
    nlinarith
  set J := Set.Icc (-τ) τ
  have hJ : -τ ≤ τ := by linarith
  -- the space `C(J, h^s)`
  let ext : C(J, h04 L s) → ℝ → h04 L s := fun v t => v (Set.projIcc (-τ) τ hJ t)
  have ext_cont : ∀ v, Continuous (ext v) := fun v => v.continuous.comp continuous_projIcc
  have ext_bound : ∀ v : C(J, h04 L s), ∀ t, ‖ext v t‖ ≤ ‖v‖ := fun v t => v.norm_coe_le_norm _
  have ext_sub : ∀ v w : C(J, h04 L s), ∀ t, ‖ext v t - ext w t‖ ≤ ‖v - w‖ := fun v w t => by
    have := (v - w).norm_coe_le_norm (Set.projIcc (-τ) τ hJ t)
    simpa using this
  let Φ : C(J, h04 L s) → C(J, h04 L s) := fun v =>
    ⟨fun t => duhamel hs κ u0 (ext v) t,
      (continuous_duhamel hs κ u0 (ext_cont v)).comp continuous_subtype_val⟩
  have hcoef := norm_coef κ hκ
  -- integral estimate
  have int_bound : ∀ (g : ℝ → h04 L s) (M : ℝ), (∀ r, ‖g r‖ ≤ M) → ∀ t ∈ J,
      ‖∫ r in (0 : ℝ)..t, Sgrp s (t - r) (g r)‖ ≤ M * τ := by
    intro g M hM t ht
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := M) fun r _ => ?_).trans ?_
    · rw [norm_Sgrp]; exact hM r
    · have : |t - 0| ≤ τ := by rw [sub_zero, abs_le]; exact ⟨ht.1, ht.2⟩
      exact mul_le_mul_of_nonneg_left this hM0
  -- maps the ball into itself
  have hmaps : ∀ v : C(J, h04 L s), ‖v‖ ≤ 2 * R → ‖Φ v‖ ≤ 2 * R := by
    intro v hv
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
    show ‖duhamel hs κ u0 (ext v) t‖ ≤ 2 * R
    unfold duhamel
    have hF : ∀ r, ‖Fh hs (ext v r)‖ ≤ C * (2 * R) ^ 3 := fun r =>
      (norm_Fh_le hs _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) ((ext_bound v r).trans hv) 3) (by positivity))
    have hI := int_bound (fun r => Fh hs (ext v r)) _ hF t t.2
    calc ‖Sgrp s t u0 - (2 * Complex.I * κ) • ∫ r in (0 : ℝ)..t, Sgrp s (t - r) (Fh hs (ext v r))‖
        ≤ ‖Sgrp s t u0‖ + ‖(2 * Complex.I * κ) • ∫ r in (0 : ℝ)..t,
            Sgrp s (t - r) (Fh hs (ext v r))‖ := norm_sub_le _ _
      _ ≤ R + 2 * κ * (C * (2 * R) ^ 3 * τ) := by
          rw [norm_Sgrp, norm_smul, hcoef]
          exact add_le_add (le_max_right _ _) (mul_le_mul_of_nonneg_left hI (by positivity))
      _ ≤ 2 * R := by nlinarith
  -- Lipschitz with constant 1/4 on the ball
  have hlip : ∀ v w : C(J, h04 L s), ‖v‖ ≤ 2 * R → ‖w‖ ≤ 2 * R →
      ‖Φ v - Φ w‖ ≤ (1 / 4) * ‖v - w‖ := by
    intro v w hv hw
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun t => ?_
    show ‖duhamel hs κ u0 (ext v) t - duhamel hs κ u0 (ext w) t‖ ≤ (1 / 4) * ‖v - w‖
    have hF : ∀ r, ‖Fh hs (ext v r) - Fh hs (ext w r)‖ ≤ C * (8 * R ^ 2) * ‖v - w‖ := by
      intro r
      refine (norm_Fh_sub_le hs _ _).trans ?_
      have h1 := pow_le_pow_left₀ (norm_nonneg _) ((ext_bound v r).trans hv) 2
      have h2 := pow_le_pow_left₀ (norm_nonneg _) ((ext_bound w r).trans hw) 2
      have h3 := ext_sub v w r
      apply mul_le_mul _ h3 (norm_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    rw [duhamel_sub hs κ u0 (ext_cont v) (ext_cont w), norm_neg, norm_smul, hcoef]
    have hI := int_bound (fun r => Fh hs (ext v r) - Fh hs (ext w r)) _ hF t t.2
    have hvw := norm_nonneg (v - w)
    calc 2 * κ * ‖∫ r in (0 : ℝ)..t, Sgrp s (t - r) (Fh hs (ext v r) - Fh hs (ext w r))‖
        ≤ 2 * κ * (C * (8 * R ^ 2) * ‖v - w‖ * τ) := mul_le_mul_of_nonneg_left hI (by positivity)
      _ = (16 * κ * τ * C * R ^ 2) * ‖v - w‖ := by ring
      _ ≤ (1 / 4) * ‖v - w‖ := mul_le_mul_of_nonneg_right hτR hvw
  -- the contraction on the closed ball
  let B := Metric.closedBall (0 : C(J, h04 L s)) (2 * R)
  have : CompleteSpace B := (Metric.isClosed_closedBall).completeSpace_coe
  have : Nonempty B := ⟨⟨0, Metric.mem_closedBall_self (by positivity)⟩⟩
  have hB : ∀ v : B, ‖(v : C(J, h04 L s))‖ ≤ 2 * R := fun v => by
    have := v.2; rw [Metric.mem_closedBall, dist_zero_right] at this; exact this
  let Φ' : B → B := fun v => ⟨Φ v, by
    rw [Metric.mem_closedBall, dist_zero_right]; exact hmaps v (hB v)⟩
  have hcontr : ContractingWith (1 / 4 : NNReal) Φ' := by
    refine ⟨by rw [div_lt_one (by norm_num)]; norm_num, LipschitzWith.of_dist_le_mul fun v w => ?_⟩
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    have := hlip v w (hB v) (hB w)
    simpa using this
  set vstar := ContractingWith.fixedPoint Φ' hcontr
  have hfix : Φ' vstar = vstar := ContractingWith.fixedPoint_isFixedPt (f := Φ') hcontr
  set u := ext (vstar : C(J, h04 L s))
  refine ⟨hτ, u, ⟨⟨by linarith, le_of_lt hτ⟩, Set.ordConnected_Icc, (ext_cont _).continuousOn,
    fun t ht => ?_⟩, fun t => (ext_bound _ t).trans (hB vstar)⟩
  have h1 : u t = (vstar : C(J, h04 L s)) ⟨t, ht⟩ := by
    simp only [u, ext, Set.projIcc_of_mem hJ ht]
  rw [h1]
  have h2 : (Φ' vstar : C(J, h04 L s)) ⟨t, ht⟩ = (vstar : C(J, h04 L s)) ⟨t, ht⟩ :=
    congrArg (fun v : B => (v : C(J, h04 L s)) ⟨t, ht⟩) hfix
  rw [← h2]
  rfl

#print axioms duhamel_integral_eq
#print axioms continuous_duhamel
#print axioms duhamel_sub
#print axioms local_existence
#print axioms norm_phase
#print axioms Sgrp_add
#print axioms Sgrp_zero
#print axioms norm_Sgrp
#print axioms continuous_Sgrp_apply
#print axioms continuousOn_Sgrp
#print axioms integrable_duhamel
#print axioms abs_integral_le_of_le
#print axioms IsMild.at_zero

end QuantumNLS.LocalWellPosedness
