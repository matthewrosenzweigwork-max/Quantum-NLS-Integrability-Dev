import NlsGge.GK38.Lib.ParamProductsZeros

/-!
# L4c part 2a: square-root-type factors (the shape of P1's canonical root), pointwise lemmas

P1's canonical root is `∏_m stdRoot(τ_m, γ_m², z)/π_m`,
`stdRoot τ g2 z = (τ - z) √(1 - (g2/4)/(τ - z)²)`; its factors are *not* `entProd` factors.
Simple explicit case: `τ_m = mπ` (fixed), `γ_m² = g_m²` with `g ∈ ℓ²` the parameter,
```
rootFac m (z, g) = ((mπ - z)/π_m) · √(1 - (g_m²/4)/(mπ - z)²),
```
on the open set `rootDom = {(z, g) | ‖g‖ < 2 |Im z|}` (there `|g_m²/(4(mπ - z)²)| < 1`, so the
radicand has positive real part).  This file proves the ingredients the generic lemma needs:

* `norm_sqrt_one_sub_sub_one_le`: `‖√(1-ε) - 1‖ ≤ ‖ε‖` (from `Re √ ≥ 0`);
* `analyticAt_rootFac`: each factor is analytic on `rootDom`;
* `rootPair_le_maj`: the paired deviation is bounded by `pairMaj` (total-mass type) uniformly on
  `|Im z| ≥ δ`, `‖z‖ ≤ R`.

The probes themselves are in `ParamProductsRootProbe`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter Metric

namespace NlsGge.GK38.Lib

noncomputable section

/-! ### The factors -/

/-- `stdRoot (mπ) (g_m²) z / π_m` (the plan's `stdRoot`, with the constant `τ_m = mπ`). -/
def rootFac (m : ℤ) (p : ℂ × L2Seq) : ℂ :=
  (((m : ℂ) * (Real.pi : ℂ) - p.1) / (piN m : ℂ)) *
    Complex.sqrt (1 - (p.2 m ^ 2 / 4) / ((m : ℂ) * (Real.pi : ℂ) - p.1) ^ 2)

/-- `ε_m = g_m²/(4(mπ - z)²)`. -/
def rootEps (m : ℤ) (p : ℂ × L2Seq) : ℂ :=
  (p.2 m ^ 2 / 4) / ((m : ℂ) * (Real.pi : ℂ) - p.1) ^ 2

/-- The domain of the probe. -/
def rootDom : Set (ℂ × L2Seq) := {p | ‖p.2‖ < 2 * |p.1.im|}

theorem isOpen_rootDom : IsOpen rootDom :=
  isOpen_lt (continuous_snd.norm)
    (continuous_const.mul (continuous_abs.comp (Complex.continuous_im.comp continuous_fst)))

theorem rootFac_eq (m : ℤ) (p : ℂ × L2Seq) :
    rootFac m p = ((((m : ℂ) * (Real.pi : ℂ) - p.1) / (piN m : ℂ)) *
      Complex.sqrt (1 - rootEps m p)) := rfl

/-! ### The square root -/

theorem sqrt_sq (a : ℂ) : Complex.sqrt a ^ 2 = a := by
  unfold Complex.sqrt
  exact Complex.cpow_ofNat_inv_pow a 2

theorem re_sqrt_nonneg (a : ℂ) : 0 ≤ (Complex.sqrt a).re := by
  unfold Complex.sqrt
  rw [Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

/-- `‖√(1 - ε) - 1‖ ≤ ‖ε‖`: from `s² - 1 = -ε` and `‖s + 1‖ ≥ 1` (`Re s ≥ 0`). -/
theorem norm_sqrt_one_sub_sub_one_le (ε : ℂ) : ‖Complex.sqrt (1 - ε) - 1‖ ≤ ‖ε‖ := by
  set s := Complex.sqrt (1 - ε) with hs
  have h1 : (s - 1) * (s + 1) = -ε := by
    have := sqrt_sq (1 - ε)
    rw [← hs] at this
    linear_combination this
  have h2 : 1 ≤ ‖s + 1‖ := by
    have hre : 1 ≤ (s + 1).re := by
      have := re_sqrt_nonneg (1 - ε)
      rw [← hs] at this
      simp only [Complex.add_re, Complex.one_re]
      linarith
    exact hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have h3 : ‖s - 1‖ * ‖s + 1‖ = ‖ε‖ := by
    rw [← norm_mul, h1, norm_neg]
  nlinarith [norm_nonneg (s - 1)]

theorem norm_sqrt_one_sub_le (ε : ℂ) : ‖Complex.sqrt (1 - ε)‖ ≤ 1 + ‖ε‖ := by
  have := norm_sqrt_one_sub_sub_one_le ε
  calc ‖Complex.sqrt (1 - ε)‖ = ‖(Complex.sqrt (1 - ε) - 1) + 1‖ := by simp
    _ ≤ ‖Complex.sqrt (1 - ε) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 + ‖ε‖ := by simp; linarith

/-! ### The radicand on the domain -/

theorem im_pos_of_mem {p : ℂ × L2Seq} (hp : p ∈ rootDom) : 0 < |p.1.im| := by
  have h : ‖p.2‖ < 2 * |p.1.im| := hp
  have := norm_nonneg p.2
  linarith

theorem abs_im_le_norm_lin (m : ℤ) (z : ℂ) : |z.im| ≤ ‖(m : ℂ) * (Real.pi : ℂ) - z‖ := by
  have : ((m : ℂ) * (Real.pi : ℂ) - z).im = -z.im := by simp
  rw [← abs_neg, ← this]
  exact Complex.abs_im_le_norm _

theorem lin_ne_zero {p : ℂ × L2Seq} (hp : p ∈ rootDom) (m : ℤ) :
    (m : ℂ) * (Real.pi : ℂ) - p.1 ≠ 0 := by
  intro h
  have := abs_im_le_norm_lin m p.1
  rw [h, norm_zero] at this
  exact (im_pos_of_mem hp).not_ge this

theorem norm_rootEps_le {p : ℂ × L2Seq} {δ : ℝ} (hδ : 0 < δ) (hδp : δ ≤ |p.1.im|) (m : ℤ) :
    ‖rootEps m p‖ ≤ ‖p.2 m‖ ^ 2 / (4 * δ ^ 2) := by
  unfold rootEps
  have hl := (hδp.trans (abs_im_le_norm_lin m p.1))
  rw [norm_div, norm_pow, norm_div, norm_pow]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4]
  have hpos : 0 < ‖(m : ℂ) * (Real.pi : ℂ) - p.1‖ ^ 2 := by
    have : 0 < ‖(m : ℂ) * (Real.pi : ℂ) - p.1‖ := hδ.trans_le hl
    positivity
  calc ‖p.2 m‖ ^ 2 / 4 / ‖(m : ℂ) * (Real.pi : ℂ) - p.1‖ ^ 2
      = ‖p.2 m‖ ^ 2 / (4 * ‖(m : ℂ) * (Real.pi : ℂ) - p.1‖ ^ 2) := by
        field_simp
    _ ≤ ‖p.2 m‖ ^ 2 / (4 * δ ^ 2) := by
        gcongr

theorem norm_rootEps_lt_one {p : ℂ × L2Seq} (hp : p ∈ rootDom) (m : ℤ) : ‖rootEps m p‖ < 1 := by
  have hpos := im_pos_of_mem hp
  have h := norm_rootEps_le hpos le_rfl (p := p) m
  refine h.trans_lt ?_
  have hg : ‖p.2 m‖ < 2 * |p.1.im| := (norm_coord_le p.2 m).trans_lt hp
  rw [div_lt_one (by positivity)]
  have h0 := norm_nonneg (p.2 m)
  nlinarith [sq_abs p.1.im]

theorem slit_of_mem {p : ℂ × L2Seq} (hp : p ∈ rootDom) (m : ℤ) : 1 - rootEps m p ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h := norm_rootEps_lt_one hp m
  have : (rootEps m p).re ≤ ‖rootEps m p‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem analyticAt_rootFac {p : ℂ × L2Seq} (hp : p ∈ rootDom) (m : ℤ) :
    AnalyticAt ℂ (rootFac m) p := by
  have h3 : AnalyticAt ℂ (fun p : ℂ × L2Seq => p.2 m) p :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).analyticAt _ |>.comp analyticAt_snd
  have hA : AnalyticAt ℂ (fun p : ℂ × L2Seq => (m : ℂ) * (Real.pi : ℂ) - p.1) p :=
    analyticAt_const.sub analyticAt_fst
  have hE : AnalyticAt ℂ (fun p : ℂ × L2Seq => rootEps m p) p := by
    unfold rootEps
    exact ((h3.pow 2).div analyticAt_const (by norm_num)).div (hA.pow 2)
      (pow_ne_zero 2 (lin_ne_zero hp m))
  have hS : AnalyticAt ℂ (fun p : ℂ × L2Seq => Complex.sqrt (1 - rootEps m p)) p := by
    unfold Complex.sqrt
    exact (analyticAt_const.sub hE).cpow analyticAt_const (slit_of_mem hp m)
  have e : rootFac m = fun p : ℂ × L2Seq =>
      (1 / (piN m : ℂ)) * (((m : ℂ) * (Real.pi : ℂ) - p.1) * Complex.sqrt (1 - rootEps m p)) := by
    funext q
    rw [rootFac_eq]
    field_simp
  rw [e]
  exact analyticAt_const.mul (hA.mul hS)

/-! ### The paired deviation is of total-mass type -/

theorem rootFac_pair (p : ℂ × L2Seq) (k : ℕ) :
    rootFac ((k : ℤ) + 1) p * rootFac (-((k : ℤ) + 1)) p
      = (1 - p.1 ^ 2 / (((k : ℂ) + 1) * (Real.pi : ℂ)) ^ 2) *
        (Complex.sqrt (1 - rootEps ((k : ℤ) + 1) p) * Complex.sqrt (1 - rootEps (-((k : ℤ) + 1)) p)) := by
  have h1 : ((k : ℤ) + 1) ≠ 0 := by omega
  have h2 : (-((k : ℤ) + 1)) ≠ 0 := by omega
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [rootFac_eq, rootFac_eq, piN_of_ne h1, piN_of_ne h2]
  push_cast
  field_simp
  ring

/-- **Pair bound.**  On `rootDom`, with `|Im z| ≥ δ > 0`, `‖z‖ ≤ R`, `‖g_n‖² ≤ d_n`:
`‖pairDev‖ ≤ pairMaj (d/(2δ² c₁)) (2R)`, i.e. total-mass type. -/
theorem rootPair_le_maj {p : ℂ × L2Seq} (hp : p ∈ rootDom) {δ R : ℝ} (hδ : 0 < δ)
    (hδp : δ ≤ |p.1.im|) (hR : ‖p.1‖ ≤ R) {d : ℤ → ℝ} (hd : ∀ n, ‖p.2 n‖ ^ 2 ≤ d n) (k : ℕ) :
    ‖pairDev (fun n => rootFac n p) k‖
      ≤ pairMaj (fun n => (1 / (2 * δ ^ 2 * majC1)) * d n) (2 * R) k := by
  set a₁ : ℤ := (k : ℤ) + 1 with ha₁
  set a₂ : ℤ := -((k : ℤ) + 1) with ha₂
  set s₁ := Complex.sqrt (1 - rootEps a₁ p) with hs₁
  set s₂ := Complex.sqrt (1 - rootEps a₂ p) with hs₂
  set w : ℂ := p.1 ^ 2 / (((k : ℂ) + 1) * (Real.pi : ℂ)) ^ 2 with hw
  have hpd : pairDev (fun n => rootFac n p) k = (s₁ * s₂ - 1) - w * (s₁ * s₂) := by
    unfold pairDev
    rw [rootFac_pair]
    ring
  have hpi := Real.pi_pos
  have hc1 : 0 < majC1 := by unfold majC1; positivity
  have he₁ := norm_rootEps_le hδ hδp a₁
  have he₂ := norm_rootEps_le hδ hδp a₂
  have hl₁ := norm_rootEps_lt_one hp a₁
  have hl₂ := norm_rootEps_lt_one hp a₂
  have hd₁ : ‖p.2 a₁‖ ^ 2 ≤ d a₁ := hd a₁
  have hd₂ : ‖p.2 a₂‖ ^ 2 ≤ d a₂ := hd a₂
  have hδ2 : 0 < 4 * δ ^ 2 := by positivity
  have hE₁ : ‖rootEps a₁ p‖ ≤ d a₁ / (4 * δ ^ 2) :=
    he₁.trans (div_le_div_of_nonneg_right hd₁ hδ2.le)
  have hE₂ : ‖rootEps a₂ p‖ ≤ d a₂ / (4 * δ ^ 2) :=
    he₂.trans (div_le_div_of_nonneg_right hd₂ hδ2.le)
  have hm₁ : ‖s₁ - 1‖ ≤ ‖rootEps a₁ p‖ := norm_sqrt_one_sub_sub_one_le _
  have hm₂ : ‖s₂ - 1‖ ≤ ‖rootEps a₂ p‖ := norm_sqrt_one_sub_sub_one_le _
  have hn₁ : ‖s₁‖ ≤ 2 := (norm_sqrt_one_sub_le _).trans (by linarith)
  have hn₂ : ‖s₂‖ ≤ 2 := (norm_sqrt_one_sub_le _).trans (by linarith)
  -- `s₁ s₂ - 1`
  have hA : ‖s₁ * s₂ - 1‖ ≤ 2 * (‖rootEps a₁ p‖ + ‖rootEps a₂ p‖) := by
    have e : s₁ * s₂ - 1 = (s₁ - 1) * (s₂ - 1) + (s₁ - 1) + (s₂ - 1) := by ring
    rw [e]
    refine (norm_add₃_le).trans ?_
    rw [norm_mul]
    have h0 := norm_nonneg (s₁ - 1)
    have h0' := norm_nonneg (s₂ - 1)
    nlinarith [norm_nonneg (rootEps a₁ p), norm_nonneg (rootEps a₂ p)]
  have hB : ‖s₁ * s₂‖ ≤ 4 := by
    rw [norm_mul]
    nlinarith [norm_nonneg s₁, norm_nonneg s₂]
  have hK : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hwn : ‖w‖ ≤ R ^ 2 / (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) := by
    rw [hw, norm_div, norm_pow, norm_pow, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hpi.le]
    have hk' : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      have : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hk', mul_pow]
    have hR0 : 0 ≤ ‖p.1‖ := norm_nonneg _
    gcongr
  have hmain : ‖pairDev (fun n => rootFac n p) k‖
      ≤ 2 * (‖rootEps a₁ p‖ + ‖rootEps a₂ p‖)
        + 4 * (R ^ 2 / (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2)) := by
    rw [hpd]
    refine (norm_sub_le _ _).trans (add_le_add hA ?_)
    rw [norm_mul]
    calc ‖w‖ * ‖s₁ * s₂‖ ≤ (R ^ 2 / (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2)) * 4 :=
          mul_le_mul hwn hB (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine hmain.trans ?_
  -- compare with `pairMaj`
  unfold pairMaj
  have hdd : majC1 * ((1 / (2 * δ ^ 2 * majC1)) * d a₁ + (1 / (2 * δ ^ 2 * majC1)) * d a₂)
      = (d a₁ + d a₂) / (2 * δ ^ 2) := by
    field_simp
  have hmaj : majC1 * ((fun n => (1 / (2 * δ ^ 2 * majC1)) * d n) ((k : ℤ) + 1)
      + (fun n => (1 / (2 * δ ^ 2 * majC1)) * d n) (-((k : ℤ) + 1)))
      = (d a₁ + d a₂) / (2 * δ ^ 2) := hdd
  rw [hmaj]
  have h2e : 2 * (‖rootEps a₁ p‖ + ‖rootEps a₂ p‖) ≤ (d a₁ + d a₂) / (2 * δ ^ 2) := by
    have : 2 * (d a₁ / (4 * δ ^ 2) + d a₂ / (4 * δ ^ 2)) = (d a₁ + d a₂) / (2 * δ ^ 2) := by
      field_simp; ring
    rw [← this]
    linarith
  have hc2 : 4 * (R ^ 2 / (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2))
      ≤ majC2 (2 * R) * (1 / ((k : ℝ) + 1) ^ 2) := by
    unfold majC2
    have hK2 : 0 < ((k : ℝ) + 1) ^ 2 := by positivity
    have e : (1 / Real.pi + 2 * (2 * R) ^ 2 / Real.pi ^ 2) * (1 / ((k : ℝ) + 1) ^ 2)
        = 1 / (Real.pi * ((k : ℝ) + 1) ^ 2) + 8 * (R ^ 2 / (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2)) := by
      field_simp
      ring
    rw [e]
    have h1 : 0 ≤ 1 / (Real.pi * ((k : ℝ) + 1) ^ 2) := by positivity
    have h2 : 0 ≤ R ^ 2 / (((k : ℝ) + 1) ^ 2 * Real.pi ^ 2) := by positivity
    linarith
  linarith

end

end NlsGge.GK38.Lib
