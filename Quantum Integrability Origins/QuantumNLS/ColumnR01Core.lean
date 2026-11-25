import Mathlib
import QuantumNLS.PhysicalAuxiliaryDensity

/-!
# ColumnR01Core: the deterministic column argument of `cor:column` (R-AA5864B7)

Source: `source-text/chapters/core/projective_reconstruction.tex:281-324` (sha256
`bc1188a07b52d3a19c337ef5ba61fb006d940f5d079d0defe2730801e679a60d`), proof lines 304-324:

"The operator norm is bounded by the trace norm, so `|p_N(t)-r^2| ≤ ε_N` and
`‖Γ_N(t)e_b-P(t)e_b‖ ≤ ε_N`. Since `r>0`, the diagonal is uniformly positive for large `N`. Also
`P(t)e_b=w(t)\overline{w_b(t)}`. Therefore
`‖Γ_N(t)e_b/√p_N(t) - P(t)e_b/r‖ ≤ ε_N/√p_N(t) + |p_N(t)-r^2|/(√p_N(t)(√p_N(t)+r))`.
The right-hand side tends to zero uniformly. For nonzero vectors `x,y`,
`‖x/‖x‖ - y/‖y‖‖ ≤ 2‖x-y‖/‖y‖`, as follows by inserting `x/‖y‖` and using `|‖x‖-‖y‖| ≤ ‖x-y‖`.
Here `x=Γ_N(t)e_b`, `y=P(t)e_b` has norm `r`, and `‖x-y‖ ≤ ε_N < r` for large `N`."

This module proves exactly that argument for an ARBITRARY parameter set `T`, an arbitrary family of positive
operators `Γ_N(t)` on `h = ℓ²(ℤ)` and unit vectors `w(t)` with `|w_b(t)| = r > 0` for every `t`
(`column_uniform`).  It contains no physical object and no hypothesis about the source's model.
* `norm_normalize_sub_le`: the printed normalization inequality, proved by inserting `x/‖y‖`.
* `column_estimates`: one operator, one `t`: `|p - r²| ≤ ε` (from `‖·‖ ≤ ‖·‖₁` and the entry bound), the
  diagonal is real and `≥ r²/2` whenever `ε ≤ r²/2`; the printed bound
  `ε/√p + |p - r²|/(√p(√p + r))` is estimated by `2ε(1+1/r)/r`; the exactly normalized column is defined
  (nonzero) and within `2ε/r`.
* `column_uniform`: the uniform statement with `ε_N = sup_t ‖Γ_N(t) - |w(t)⟩⟨w(t)|‖₁` (`supError`, in `ℝ≥0∞`).

The sourced objects are the accepted DEF-029 ones: `AuxiliaryDensity.column`, `normalizedColumn`,
`rankOneOperator`, and `PhysicalAuxiliaryDensity.sourceColumn` (`c_N^{(b)} = Γe_b/√Γ_{bb}`).
-/

set_option autoImplicit false

open scoped InnerProductSpace ComplexConjugate ComplexOrder ENNReal
open Filter Topology

noncomputable section

namespace QuantumNLS.ColumnR01Core

open QuantumNLS.OccupationUnitary (OneParticle oneBasis)
open QuantumNLS.AuxiliaryDensity
open QuantumNLS.PhysicalAuxiliaryDensity (sourceColumn column_rankOne column_apply_anchor
  column_anchor_nonneg)
open QuantumNLS.TraceClass (traceNorm)

/-- The limiting column `w \overline{w_b}/|w_b|` of `eq:column-limit`. -/
def target (w : OneParticle) (b : ℤ) : OneParticle := (conj (w b) / ((‖w b‖ : ℝ) : ℂ)) • w

theorem norm_oneBasis (a : ℤ) : ‖oneBasis a‖ = 1 := by
  rw [QuantumNLS.OccupationUnitary.oneBasis_apply, lp.norm_single (by norm_num)]
  simp

theorem norm_smul_ofReal (a : ℝ) (v : OneParticle) : ‖((a : ℝ) : ℂ) • v‖ = |a| * ‖v‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- The printed normalization inequality: for nonzero `x, y`,
`‖x/‖x‖ - y/‖y‖‖ ≤ 2‖x-y‖/‖y‖`, by inserting `x/‖y‖` and `|‖x‖-‖y‖| ≤ ‖x-y‖`. -/
theorem norm_normalize_sub_le {x y : OneParticle} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖(((‖x‖ : ℝ) : ℂ))⁻¹ • x - (((‖y‖ : ℝ) : ℂ))⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖y‖ := by
  have ha : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hb : 0 < ‖y‖ := norm_pos_iff.2 hy
  have e : (((‖x‖ : ℝ) : ℂ))⁻¹ • x - (((‖y‖ : ℝ) : ℂ))⁻¹ • y =
      (((‖x‖⁻¹ - ‖y‖⁻¹ : ℝ)) : ℂ) • x + (((‖y‖⁻¹ : ℝ)) : ℂ) • (x - y) := by
    simp only [smul_sub, sub_smul, Complex.ofReal_sub, Complex.ofReal_inv]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul_ofReal, norm_smul_ofReal, abs_of_pos (inv_pos.2 hb)]
  have h1 : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖x‖ = |‖y‖ - ‖x‖| / ‖y‖ := by
    rw [inv_sub_inv ha.ne' hb.ne', abs_div, abs_of_pos (mul_pos ha hb), div_mul_eq_mul_div,
      mul_comm ‖x‖ ‖y‖, mul_div_mul_right _ _ ha.ne']
  rw [h1]
  have h2 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
    rw [norm_sub_rev]
    exact abs_norm_sub_norm_le y x
  rw [inv_mul_eq_div]
  calc |‖y‖ - ‖x‖| / ‖y‖ + ‖x - y‖ / ‖y‖ ≤ ‖x - y‖ / ‖y‖ + ‖x - y‖ / ‖y‖ := by gcongr
    _ = 2 * ‖x - y‖ / ‖y‖ := by ring

/-- **One operator.**  If `Γ ≥ 0`, `‖w‖ = 1`, `|w_b| = r > 0` and `‖Γ - |w⟩⟨w|‖ ≤ ε ≤ r²/2`, then the diagonal
`p = Γ_{bb}` is real with `p ≥ r²/2`, the column `c = Γe_b/√p` is within `2ε(1+1/r)/r` of
`w\overline{w_b}/|w_b|` (the printed bound `ε/√p + |p-r²|/(√p(√p+r))`), and the exactly normalized
column is defined and within `2ε/r`. -/
theorem column_estimates (Γ : OneParticle →L[ℂ] OneParticle) (hΓ : Γ.IsPositive)
    (w : OneParticle) (hw : ‖w‖ = 1) (b : ℤ) {r ε : ℝ} (hr : 0 < r) (hwb : ‖w b‖ = r)
    (hε : ‖Γ - rankOneOperator w‖ ≤ ε) (hεr : ε ≤ r ^ 2 / 2) :
    (((r ^ 2 / 2 : ℝ)) : ℂ) ≤ ⟪oneBasis b, Γ (oneBasis b)⟫_ℂ ∧
    ‖sourceColumn Γ b - target w b‖ ≤ 2 * ε * (1 + 1 / r) / r ∧
    column Γ b ≠ 0 ∧
    ‖normalizedColumn Γ b - target w b‖ ≤ 2 * ε / r := by
  have hyw : column (rankOneOperator w) b = conj (w b) • w := column_rankOne w b
  have hxy : ‖column Γ b - column (rankOneOperator w) b‖ ≤ ε := by
    have : column Γ b - column (rankOneOperator w) b = (Γ - rankOneOperator w) (oneBasis b) := by
      rfl
    rw [this]
    calc _ ≤ ‖Γ - rankOneOperator w‖ * ‖oneBasis b‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Γ - rankOneOperator w‖ := by rw [norm_oneBasis, mul_one]
      _ ≤ ε := hε
  have hny : ‖column (rankOneOperator w) b‖ = r := by
    rw [hyw, norm_smul, Complex.norm_conj, hwb, hw, mul_one]
  -- the diagonal entry `p = Γ_{bb}` is real and nonnegative (positivity)
  have hxb0 : 0 ≤ column Γ b b := column_anchor_nonneg hΓ b
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.1 hxb0
  have hxb : column Γ b b = (((column Γ b b).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [← him]
  have hyb : column (rankOneOperator w) b b = (((r ^ 2 : ℝ)) : ℂ) := by
    rw [hyw, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, Complex.conj_mul', hwb]
    push_cast
    ring
  -- `|p - r²| ≤ ε`
  have hpr : |(column Γ b b).re - r ^ 2| ≤ ε := by
    have h1 : ‖column Γ b b - column (rankOneOperator w) b b‖ ≤ ε := by
      refine le_trans ?_ hxy
      have := lp.norm_apply_le_norm (p := (2 : ℝ≥0∞)) (by norm_num)
        (column Γ b - column (rankOneOperator w) b) b
      simpa using this
    rw [hyb] at h1
    rw [hxb, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
    simpa using h1
  set p := (column Γ b b).re with hp
  have hp2 : r ^ 2 / 2 ≤ p := by
    have := (abs_le.1 hpr).1
    linarith
  have hppos : 0 < p := lt_of_lt_of_le (by positivity) hp2
  -- part 1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← column_apply_anchor, hxb]
    exact Complex.real_le_real.2 hp2
  · -- the unnormalized column `c = Γe_b/√p`
    set s := Real.sqrt p with hs
    have hs0 : 0 < s := Real.sqrt_pos.2 hppos
    have hs2 : s ^ 2 = p := Real.sq_sqrt hppos.le
    have hsr : r / 2 ≤ s := by
      have h := Real.sqrt_le_sqrt (show (r / 2) ^ 2 ≤ p by nlinarith)
      rwa [Real.sqrt_sq (by positivity)] at h
    have hrs : |r - s| ≤ ε / r := by
      have h1 : |r - s| * (r + s) ≤ ε := by
        rw [← abs_of_pos (show 0 < r + s by positivity), ← abs_mul,
          show (r - s) * (r + s) = -(p - r ^ 2) by nlinarith [hs2], abs_neg]
        exact hpr
      rw [le_div_iff₀ hr]
      have : |r - s| * r ≤ |r - s| * (r + s) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      linarith
    have ht : target w b = (((r : ℝ) : ℂ))⁻¹ • column (rankOneOperator w) b := by
      rw [target, hyw, smul_smul, hwb, div_eq_inv_mul]
    have hsc : sourceColumn Γ b = (((s : ℝ) : ℂ))⁻¹ • column Γ b := rfl
    have e : (((s : ℝ) : ℂ))⁻¹ • column Γ b - (((r : ℝ) : ℂ))⁻¹ • column (rankOneOperator w) b =
        (((s⁻¹ : ℝ)) : ℂ) • (column Γ b - column (rankOneOperator w) b) +
          (((s⁻¹ - r⁻¹ : ℝ)) : ℂ) • column (rankOneOperator w) b := by
      simp only [smul_sub, sub_smul, Complex.ofReal_sub, Complex.ofReal_inv]
      abel
    rw [hsc, ht, e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul_ofReal, norm_smul_ofReal, abs_of_pos (inv_pos.2 hs0), hny]
    have h3 : |s⁻¹ - r⁻¹| * r = s⁻¹ * |r - s| := by
      rw [inv_sub_inv hs0.ne' hr.ne', abs_div, abs_of_pos (mul_pos hs0 hr)]
      field_simp
    rw [h3]
    have hsinv : s⁻¹ ≤ 2 / r := by
      have := inv_anti₀ (by positivity : 0 < r / 2) hsr
      rwa [inv_div] at this
    calc s⁻¹ * ‖column Γ b - column (rankOneOperator w) b‖ + s⁻¹ * |r - s|
        = s⁻¹ * (‖column Γ b - column (rankOneOperator w) b‖ + |r - s|) := by ring
      _ ≤ (2 / r) * (ε + ε / r) :=
          mul_le_mul hsinv (add_le_add hxy hrs) (by positivity) (by positivity)
      _ = 2 * ε * (1 + 1 / r) / r := by ring
  · intro h0
    have : column Γ b b = 0 := by rw [h0]; rfl
    rw [hxb] at this
    exact hppos.ne' (Complex.ofReal_eq_zero.1 this)
  · have hx0 : column Γ b ≠ 0 := by
      intro h0
      have : column Γ b b = 0 := by rw [h0]; rfl
      rw [hxb] at this
      exact hppos.ne' (Complex.ofReal_eq_zero.1 this)
    have hy0 : column (rankOneOperator w) b ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hny
      exact hr.ne' hny.symm
    have ht : target w b =
        (((‖column (rankOneOperator w) b‖ : ℝ) : ℂ))⁻¹ • column (rankOneOperator w) b := by
      rw [hny, target, hyw, smul_smul, hwb, div_eq_inv_mul]
    rw [ht]
    refine (norm_normalize_sub_le hx0 hy0).trans ?_
    rw [hny]
    gcongr

/-- `ε_N = sup_{t} ‖Γ_N(t) - |w(t)⟩⟨w(t)|‖₁` (in `ℝ≥0∞`). -/
def supError {T : Type*} (Γ : ℕ → T → OneParticle →L[ℂ] OneParticle) (w : T → OneParticle)
    (N : ℕ) : ℝ≥0∞ :=
  ⨆ t, traceNorm (Γ N t - rankOneOperator (w t))

/-- The operator norm is bounded by the trace norm, hence by `ε_N`. -/
theorem opNorm_le_supError {T : Type*} (Γ : ℕ → T → OneParticle →L[ℂ] OneParticle)
    (w : T → OneParticle) (N : ℕ) (hfin : supError Γ w N ≠ ⊤) (t : T) :
    ‖Γ N t - rankOneOperator (w t)‖ ≤ (supError Γ w N).toReal := by
  have h1 : ENNReal.ofReal ‖Γ N t - rankOneOperator (w t)‖ ≤ supError Γ w N :=
    (QuantumNLS.TraceClass.norm_le_traceNorm _).trans
      (le_iSup (fun t => traceNorm (Γ N t - rankOneOperator (w t))) t)
  exact (ENNReal.ofReal_le_iff_le_toReal hfin).1 h1

/-- A uniform real bound tending to zero gives convergence of the `ℝ≥0∞` supremum. -/
theorem tendsto_iSup_ofReal {T : Type*} (f : ℕ → T → ℝ) (g : ℕ → ℝ)
    (hg : Tendsto g atTop (𝓝 0)) (hfg : ∀ᶠ N in atTop, ∀ t, f N t ≤ g N) :
    Tendsto (fun N => ⨆ t, ENNReal.ofReal (f N t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => ENNReal.ofReal (g N)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal hg
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
    (Filter.Eventually.of_forall fun N => zero_le) ?_
  exact hfg.mono fun N hN => iSup_le fun t => ENNReal.ofReal_le_ofReal (hN t)

theorem tendsto_supError_toReal {T : Type*} (Γ : ℕ → T → OneParticle →L[ℂ] OneParticle)
    (w : T → OneParticle) (hlim : Tendsto (supError Γ w) atTop (𝓝 0)) :
    Tendsto (fun N => (supError Γ w N).toReal) atTop (𝓝 0) := by
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  simpa [Function.comp_def] using this

/-- **Column recovery, uniform in an arbitrary parameter set** (the argument of `cor:column`).
For positive `Γ_N(t)`, unit `w(t)` with `|w_b(t)| = r > 0` for every `t`, and
`ε_N = sup_t ‖Γ_N(t) - |w(t)⟩⟨w(t)|‖₁ → 0`:
(1) eventually `p_N(t) = Γ_N(t)_{bb}` is real with `p_N(t) ≥ r²/2 > 0` for every `t`;
(2) `sup_t ‖c_N^{(b)}(t) - w(t)\overline{w_b(t)}/|w_b(t)|‖ → 0`;
(3) eventually every column `Γ_N(t)e_b` is nonzero and the exactly normalized column is within `2ε_N/r`;
(4) `sup_t ‖ĉ_N^{(b)}(t) - w(t)\overline{w_b(t)}/|w_b(t)|‖ → 0`. -/
theorem column_uniform {T : Type*} (Γ : ℕ → T → OneParticle →L[ℂ] OneParticle)
    (w : T → OneParticle) (b : ℤ) {r : ℝ} (hpos : ∀ N t, (Γ N t).IsPositive)
    (hw : ∀ t, ‖w t‖ = 1) (hr : 0 < r) (hwb : ∀ t, ‖w t b‖ = r)
    (hlim : Tendsto (supError Γ w) atTop (𝓝 0)) :
    (∀ᶠ N in atTop, ∀ t, (((r ^ 2 / 2 : ℝ)) : ℂ) ≤ ⟪oneBasis b, Γ N t (oneBasis b)⟫_ℂ ∧
        0 < ⟪oneBasis b, Γ N t (oneBasis b)⟫_ℂ) ∧
    Tendsto (fun N => ⨆ t, ENNReal.ofReal ‖sourceColumn (Γ N t) b - target (w t) b‖) atTop
      (𝓝 0) ∧
    (∀ᶠ N in atTop, ∀ t, column (Γ N t) b ≠ 0 ∧
        ‖normalizedColumn (Γ N t) b - target (w t) b‖ ≤ 2 * (supError Γ w N).toReal / r) ∧
    Tendsto (fun N => ⨆ t, ENNReal.ofReal ‖normalizedColumn (Γ N t) b - target (w t) b‖) atTop
      (𝓝 0) := by
  have hev : ∀ᶠ N in atTop, supError Γ w N < ENNReal.ofReal (r ^ 2 / 2) :=
    hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity)))
  have key : ∀ᶠ N in atTop, ∀ t,
      (((r ^ 2 / 2 : ℝ)) : ℂ) ≤ ⟪oneBasis b, Γ N t (oneBasis b)⟫_ℂ ∧
      ‖sourceColumn (Γ N t) b - target (w t) b‖ ≤
        2 * (supError Γ w N).toReal * (1 + 1 / r) / r ∧
      column (Γ N t) b ≠ 0 ∧
      ‖normalizedColumn (Γ N t) b - target (w t) b‖ ≤ 2 * (supError Γ w N).toReal / r := by
    refine hev.mono fun N hN t => ?_
    have hfin : supError Γ w N ≠ ⊤ := ne_top_of_lt hN
    have hεr : (supError Γ w N).toReal ≤ r ^ 2 / 2 :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hN.le
    exact column_estimates (Γ N t) (hpos N t) (w t) (hw t) b hr (hwb t)
      (opNorm_le_supError Γ w N hfin t) hεr
  have hε0 := tendsto_supError_toReal Γ w hlim
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine key.mono fun N hN t => ⟨(hN t).1, lt_of_lt_of_le ?_ (hN t).1⟩
    exact Complex.zero_lt_real.2 (by positivity)
  · refine tendsto_iSup_ofReal _ (fun N => 2 * (supError Γ w N).toReal * (1 + 1 / r) / r) ?_
      (key.mono fun N hN t => (hN t).2.1)
    have := ((hε0.const_mul 2).mul_const (1 + 1 / r)).div_const r
    simpa using this
  · exact key.mono fun N hN t => ⟨(hN t).2.2.1, (hN t).2.2.2⟩
  · refine tendsto_iSup_ofReal _ (fun N => 2 * (supError Γ w N).toReal / r) ?_
      (key.mono fun N hN t => (hN t).2.2.2)
    have := (hε0.const_mul 2).div_const r
    simpa using this

/-- Pointwise consequence of the uniform trace limit: for each parameter, operator-norm convergence. -/
theorem tendsto_opNorm_of_supError {T : Type*} (Γ : ℕ → T → OneParticle →L[ℂ] OneParticle)
    (w : T → OneParticle) (hlim : Tendsto (supError Γ w) atTop (𝓝 0)) (t : T) :
    Tendsto (fun N => ‖Γ N t - rankOneOperator (w t)‖) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N => ENNReal.ofReal ‖Γ N t - rankOneOperator (w t)‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun N => (QuantumNLS.TraceClass.norm_le_traceNorm _).trans
        (le_iSup (fun t => traceNorm (Γ N t - rankOneOperator (w t))) t))
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simpa [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _)] using h2

/-- Diagonal entries converge: `Γ_N(t)_{nn} → |w_n(t)|²`. -/
theorem tendsto_diag_of_opNorm (Γ : ℕ → OneParticle →L[ℂ] OneParticle) (w : OneParticle) (n : ℤ)
    (h : Tendsto (fun N => ‖Γ N - rankOneOperator w‖) atTop (𝓝 0)) :
    Tendsto (fun N => ⟪oneBasis n, Γ N (oneBasis n)⟫_ℂ) atTop (𝓝 (((‖w n‖ ^ 2 : ℝ)) : ℂ)) := by
  have hlimv : ⟪oneBasis n, rankOneOperator w (oneBasis n)⟫_ℂ = (((‖w n‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← column_apply_anchor, column_rankOne, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      Complex.conj_mul']
    push_cast
    ring
  rw [← hlimv, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) h
  have e : Γ N (oneBasis n) - rankOneOperator w (oneBasis n) =
      (Γ N - rankOneOperator w) (oneBasis n) := rfl
  rw [← inner_sub_right, e]
  calc _ ≤ ‖oneBasis n‖ * ‖(Γ N - rankOneOperator w) (oneBasis n)‖ := norm_inner_le_norm _ _
    _ ≤ ‖oneBasis n‖ * (‖Γ N - rankOneOperator w‖ * ‖oneBasis n‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖Γ N - rankOneOperator w‖ := by rw [norm_oneBasis]; ring

end QuantumNLS.ColumnR01Core

#print axioms QuantumNLS.ColumnR01Core.norm_normalize_sub_le
#print axioms QuantumNLS.ColumnR01Core.column_estimates
#print axioms QuantumNLS.ColumnR01Core.column_uniform
#print axioms QuantumNLS.ColumnR01Core.tendsto_opNorm_of_supError
#print axioms QuantumNLS.ColumnR01Core.tendsto_diag_of_opNorm

set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.ColumnR01Core." ||
        n.toString.startsWith "_private.QuantumNLS.ColumnR01Core." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"ColumnR01Core aggregate audit PASS: {own} own constants; {seen.size} transitive constants; standard axioms only; no held identifiers."
