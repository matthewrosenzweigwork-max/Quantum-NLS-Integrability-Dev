import NlsGge.Schur.ActualSchurRealTypeSymmetry38V1
import NlsGge.Schur.ActualSchurQnCauchy38V1
import NlsGge.Schur.ActualSchurGapComparisonRealization38V1

/-!
# Real-type center, real `q_n` and the real-H¹ derivative bound (NEW-F03.05/.06)

Source: `paper/v2.tex` lines 1124-1129 ("It is real for real-type potentials")
and 1150-1153 (Cauchy estimate on the line `(u + ζ w, ū + ζ w̄)`).

* For `(u₁,u₂) = (u, ū)` the actual center `σ_n` is real (real contraction on
  `[nπ - 1/2, nπ + 1/2]`, using reality of `α_n` from the real-type symmetry, then
  uniqueness of the complex fixed point).
* The real-H¹ map `u ↦ q_n(u, ū) - u_n` is real-differentiable on the open
  radius-`R` ball (threshold imposed at radius `4R`) and its real derivative
  has operator norm at most `C R^3/n^2` (F:eq:qCauchy, second inequality).
-/

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace NNReal
open NlsGge.Analysis NlsGge.Pilot

namespace NlsGge.Schur

/-- The actual moving center is real on the real-type subspace. -/
theorem actualSchurCenter38_real_realType
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hw : ‖w‖ ≤ R) :
    (actualSchurCenter38 R n (w, actualH1Conj38 w)).im = 0 := by
  let p : ActualSchurEffectiveH1PairV3_30 := (w, actualH1Conj38 w)
  have hp₁ : ‖p.1‖ ≤ R := hw
  have hp₂ : ‖p.2‖ ≤ R := by
    change ‖actualH1Conj38 w‖ ≤ R
    rw [actualH1Conj38_norm]
    exact hw
  obtain ⟨hmaps, hlip⟩ :=
    actualSchurCenterMap38_mapsTo_and_lipschitz R hR n hthr p hp₁ hp₂
  let c : ℝ := Real.pi * n
  let s : Set ℝ := Set.Icc (c - 1 / 2) (c + 1 / 2)
  have hcR : (spectralCenter n) = ((c : ℝ) : ℂ) := by
    simp [spectralCenter, c]
    ring
  have hball : ∀ x ∈ s, ((x : ℂ)) ∈ Metric.closedBall (spectralCenter n) (1 / 2) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm, hcR, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := hx
    constructor <;> linarith
  let T : ℝ → ℝ := fun x => c + (actualSchurAlpha38 n p x).re
  have hsf : Set.MapsTo T s s := by
    intro x hx
    have h := hmaps x (hball x hx)
    rw [add_sub_cancel_left] at h
    have hre := le_trans (Complex.abs_re_le_norm _) h
    rw [abs_le] at hre
    obtain ⟨h1, h2⟩ := hre
    constructor <;> simp only [T] <;> linarith
  have hsc : IsComplete s := isClosed_Icc.isComplete
  have hK : (1 / 4 : ℝ≥0) < 1 := by
    rw [show (1 / 4 : ℝ≥0) = (4 : ℝ≥0)⁻¹ by simp]
    exact inv_lt_one_of_one_lt₀ (by norm_num)
  have hcontr : ContractingWith (1 / 4 : ℝ≥0) (hsf.restrict T s s) := by
    refine ⟨hK, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    change dist (T x) (T y) ≤ ((1 / 4 : ℝ≥0) : ℝ) * dist (x : ℝ) (y : ℝ)
    rw [Real.dist_eq, Real.dist_eq]
    have h := hlip x (hball x x.2) y (hball y y.2)
    have hn' : ‖((x : ℝ) : ℂ) - ((y : ℝ) : ℂ)‖ = |(x : ℝ) - y| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [hn'] at h
    have he : T x - T y = (actualSchurAlpha38 n p x - actualSchurAlpha38 n p y).re := by
      simp only [T, Complex.sub_re]
      ring
    rw [he]
    refine le_trans (Complex.abs_re_le_norm _) ?_
    simpa using h
  have hcs : c ∈ s := ⟨by linarith, by linarith⟩
  obtain ⟨x0, hx0s, hx0fix, -, -⟩ :=
    hcontr.exists_fixedPoint' hsc hsf hcs (edist_ne_top _ _)
  have hdisk : ((x0 : ℂ)) ∈ spectralDisk n :=
    closedBall_half_subset_spectralDisk38 n (hball x0 hx0s)
  have him := actualSchurAlpha38_im_eq_zero_realType38 R hR n hthr x0 hdisk w hw
  have hfixC : ((x0 : ℂ)) = spectralCenter n + actualSchurAlpha38 n p x0 := by
    apply Complex.ext
    · simp only [Complex.ofReal_re, Complex.add_re, hcR]
      have := hx0fix.eq
      simp only [T] at this
      linarith
    · simp only [Complex.ofReal_im, Complex.add_im, hcR]
      change (0 : ℝ) = 0 + (actualSchurAlpha38 n (w, actualH1Conj38 w) (x0 : ℂ)).im
      rw [him]
      ring
  have heq := actualSchurCenter38_eq_of_fixed R hR n hthr p hp₁ hp₂ x0
    (hball x0 hx0s) hfixC
  change (actualSchurCenter38 R n p).im = 0
  rw [heq, Complex.ofReal_im]

end NlsGge.Schur

namespace NlsGge.Schur

theorem actualH1Conj38_add_real_smul
    (u w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (t : ℝ) :
    actualH1Conj38 (u + (t : ℂ) • w) = actualH1Conj38 u + (t : ℂ) • actualH1Conj38 w := by
  apply Subtype.ext
  funext k
  change star ((u : ℤ → ℂ) (-k) + (t : ℂ) * (w : ℤ → ℂ) (-k)) =
    star ((u : ℤ → ℂ) (-k)) + (t : ℂ) * star ((w : ℤ → ℂ) (-k))
  rw [star_add, star_mul', Complex.star_def, Complex.conj_ofReal]

/-- F:eq:qCauchy, second inequality, directional form on the real-type
subspace: for `‖u‖_{H¹} ≤ R` and every real H¹ direction `w` with `‖w‖ ≤ 1`, the
real directional derivative of `t ↦ q_n(u + t w, conj(u + t w)) - (u + t w)_n`
at `t = 0` exists and has size at most `C (4R)^4/n^2 / R`, uniformly in `w`.
The threshold is imposed at radius `4R` as in the source. -/
theorem actualSchurQnRealType_directional_bound38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * (4 * R) ^ 3 ≤ |(n : ℝ)|)
    (u w : WeightedHilbert (sobolevModeWeight (1 : ℝ)))
    (hu : ‖u‖ ≤ R) (hw : ‖w‖ ≤ 1) :
    ∃ L : ℂ, HasDerivAt (fun t : ℝ =>
        actualSchurQn38 (4 * R) n (u + (t : ℂ) • w, actualH1Conj38 (u + (t : ℂ) • w)) -
          (u + (t : ℂ) • w : WeightedHilbert (sobolevModeWeight (1 : ℝ))) n) L 0 ∧
      ‖L‖ ≤ actualSchurBremConstant38 * (4 * R) ^ 4 / |(n : ℝ)| ^ 2 / R := by
  have h4R : 1 ≤ 4 * R := by linarith
  let p : ActualSchurEffectiveH1PairV3_30 := (u, actualH1Conj38 u)
  let v : ActualSchurEffectiveH1PairV3_30 := (w, actualH1Conj38 w)
  have hp₁ : ‖p.1‖ ≤ R := hu
  have hp₂ : ‖p.2‖ ≤ R := by
    change ‖actualH1Conj38 u‖ ≤ R
    rw [actualH1Conj38_norm]; exact hu
  have hv₁ : ‖v.1‖ ≤ 1 := hw
  have hv₂ : ‖v.2‖ ≤ 1 := by
    change ‖actualH1Conj38 w‖ ≤ 1
    rw [actualH1Conj38_norm]; exact hw
  let G : ℂ → ℂ := fun ζ => actualSchurQn38 (4 * R) n (p + ζ • v) - (p + ζ • v).1 n
  have hbound := actualSchurQn38_line_deriv_bound R hR n hthr p v hp₁ hp₂ hv₁ hv₂
  have hGd : DifferentiableAt ℂ G 0 := by
    have hq := actualSchurQn38_differentiableAt (4 * R) h4R n hthr (p + (0 : ℂ) • v)
      (by simp only [zero_smul, add_zero]; linarith)
      (by simp only [zero_smul, add_zero]; linarith)
    have hline : DifferentiableAt ℂ (fun ξ : ℂ => p + ξ • v) 0 :=
      (differentiableAt_id.smul_const v).const_add p
    have hcoord : ∀ ζ : ℂ, (p + ζ • v).1 n = p.1 n + ζ * v.1 n := fun ζ => rfl
    have hsecond : DifferentiableAt ℂ (fun ξ : ℂ => (p + ξ • v).1 n) 0 := by
      simp only [hcoord]
      exact (differentiableAt_id.mul_const _).const_add _
    exact (hq.comp (0 : ℂ) hline).sub hsecond
  refine ⟨deriv G 0, ?_, hbound⟩
  have h := hGd.hasDerivAt.comp_ofReal (z := (0 : ℝ))
  convert h using 1
  funext t
  change _ = actualSchurQn38 (4 * R) n (p + (t : ℂ) • v) - (p + (t : ℂ) • v).1 n
  rw [actualH1Conj38_add_real_smul]
  rfl

/-- F:eq:qaction, first inequality, on the real-type subspace: with the real
moving center `σ_n(u)` and the auxiliary coordinate `q_n(u) = b_n(σ_n(u); u, ū)`,
any real zeros `λ⁺` of `F - |b_n|` and `λ⁻` of `F + |b_n|` in
`[nπ - 1/2, nπ + 1/2]` satisfy `λ⁺ - λ⁻ ≥ 2|q_n(u)|/(1 + 2 d_n)`. -/
theorem actualSchurQnRealType_gap_lower38
    (R : ℝ) (hR : 1 ≤ R) (n : ℤ)
    (hthr : actualSchurCenterThresholdConstant38 * R ^ 3 ≤ |(n : ℝ)|)
    (u : WeightedHilbert (sobolevModeWeight (1 : ℝ))) (hu : ‖u‖ ≤ R)
    (lm lp : ℝ)
    (hlmI : lm ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlpI : lp ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2))
    (hlp : lp - Real.pi * n - (actualSchurAlpha38 n (u, actualH1Conj38 u) lp).re -
      ‖actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (false, resonantIndex n) ((lp : ℂ), (u, actualH1Conj38 u))‖ = 0)
    (hlm : lm - Real.pi * n - (actualSchurAlpha38 n (u, actualH1Conj38 u) lm).re +
      ‖actualSchurCoefficientAfterDext31 n
        (true, resonantIndex n) (false, resonantIndex n) ((lm : ℂ), (u, actualH1Conj38 u))‖ = 0) :
    2 * ‖actualSchurQn38 R n (u, actualH1Conj38 u)‖ /
        (1 + 2 * actualSchurGapParameter38 R n) ≤ lp - lm := by
  let p : ActualSchurEffectiveH1PairV3_30 := (u, actualH1Conj38 u)
  have hp₁ : ‖p.1‖ ≤ R := hu
  have hp₂ : ‖p.2‖ ≤ R := by
    change ‖actualH1Conj38 u‖ ≤ R
    rw [actualH1Conj38_norm]; exact hu
  obtain ⟨hσball, hσfix⟩ := actualSchurCenter38_spec R hR n hthr p hp₁ hp₂
  have him := actualSchurCenter38_real_realType R hR n hthr u hu
  set σ := actualSchurCenter38 R n p with hσdef
  have hσreal : ((σ.re : ℝ) : ℂ) = σ := by
    apply Complex.ext <;> simp [him]
  have hσI : σ.re ∈ Set.Icc (Real.pi * n - 1 / 2) (Real.pi * n + 1 / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hσball
    have h := le_trans (Complex.abs_re_le_norm _) hσball
    rw [Complex.sub_re, abs_le] at h
    have hc : (spectralCenter n).re = Real.pi * n := by
      simp [spectralCenter, Complex.mul_re]
      ring
    rw [hc] at h
    obtain ⟨h1, h2⟩ := h
    constructor <;> linarith
  have hfix' : ((σ.re : ℝ) : ℂ) = spectralCenter n + actualSchurAlpha38 n p (σ.re : ℂ) := by
    rw [hσreal]; exact hσfix
  have h := actualSchurGapComparison38V1 R hR n hthr p hp₁ hp₂ σ.re lm lp hσI hlmI hlpI
    hfix' hlp hlm
  have hq : actualSchurQn38 R n p =
      actualSchurCoefficientAfterDext31 n (true, resonantIndex n) (false, resonantIndex n)
        (((σ.re : ℝ) : ℂ), p) := by
    rw [hσreal]; rfl
  change 2 * ‖actualSchurQn38 R n p‖ / _ ≤ _
  rw [hq]
  exact h.2.2

end NlsGge.Schur
