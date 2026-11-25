import Mathlib

/-!
# R-2AF76530 `lem:E-kernel`: the symmetrized interaction kernel error

Source: `source/chapters/quantitative/static_finite_gap.tex`, `\label{lem:E-kernel}` (lines 71-86),
`\ReportID{R-2AF76530}`, with its printed proof (lines 88-108). No graph prerequisites.

Objects, formalized literally:
* `KN κ N f t u = (N/κ)(f t − f u) arctan(κ/(N(t−u)))`, with diagonal value `0` (`KN`).
* `Kf f t u = ∫_0^1 f'(u + s(t−u)) ds` (`Kf`), with `f' = deriv f`.
* `f ∈ C_c²(ℝ)` is `Good f`: `ContDiff ℝ 2 f` and `HasCompactSupport f`.
* `λ = N⁻¹ Σ_j δ_{q_j}` is `empirical N q`; `μ = ρ(t) dt` is `densityMeasure ρ`, a probability
  measure with `0 ≤ ρ ≤ Mρ` (boundedness of `ρ` is the only property of `ρ` the source uses).
* `w = W_1(λ, μ)`: `W1 λ μ` is the infimum of `∫ |x−y| dπ` over couplings `π` (`IsCoupling`).
* `‖g‖_∞` is `supAbs g = ⨆ x, |g x|`.

Main statement (`E_kernel_bound`): for `0 ≤ w ≤ 1` with `W1 λ μ = ofReal w`,
  `|∬KN dλ⊗² − ∬Kf dμ⊗²| ≤ (8Mρ + 4 + κ²/3) ‖f'‖_∞ (√w + N^{−2/3}) + 2 ‖f''‖_∞ w`.
The constant `8Mρ + 4 + κ²/3` depends only on `Mρ` and `κ` (`E_kernel_bound_exists`: existential form).

Proof route (the printed one, made explicit):
* strip: a tent cutoff `tent δ` with `1_{|s|≤δ} ≤ tent δ ≤ 1_{|s|≤2δ}`, `1/δ`-Lipschitz, is
  integrated against `λ⊗λ`; the two-coordinate coupling lemma `two_coupling_bound` moves it to
  `μ⊗μ` at cost `2(1/δ)∫|x−y|dπ`, and `μ⊗μ{|t−u| ≤ 2δ} ≤ 4Mρδ`;
* off the strip `|K_N − K^f| ≤ ‖f'‖ κ²/(3N²(t−u)²)`, from `|arctan y − y| ≤ |y|³/3`,
  `y = κ/(N(t−u))`;
* `K^f` is `‖f''‖`-Lipschitz in each variable, so replacing `λ⊗λ` by `μ⊗μ` costs
  `2‖f''‖∫|x−y|dπ`;
* the coupling is chosen with cost `c ≤ w + ε`, `δ = √c + N^{−2/3}`, and `ε → 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace QuantumNLS.EKernelBound

/-! ## Definitions -/

/-- `K_N^f(t,u) = (N/κ)(f(t) − f(u)) arctan(κ/(N(t−u)))`, with diagonal value `0`. -/
def KN (κ N : ℝ) (f : ℝ → ℝ) (t u : ℝ) : ℝ :=
  if t = u then 0 else (N / κ) * (f t - f u) * Real.arctan (κ / (N * (t - u)))

/-- `K^f(t,u) = ∫_0^1 f'(u + s(t − u)) ds`, with `f' = deriv f`. -/
def Kf (f : ℝ → ℝ) (t u : ℝ) : ℝ :=
  ∫ s in (0:ℝ)..1, deriv f (u + s * (t - u))

/-- Sup norm `‖g‖_∞ = sup_x |g x|`. -/
def supAbs (g : ℝ → ℝ) : ℝ :=
  ⨆ x, |g x|

/-- Empirical measure `λ = N⁻¹ Σ_j δ_{q_j}`. -/
def empirical (N : ℕ) (q : Fin N → ℝ) : Measure ℝ :=
  (N : ℝ≥0∞)⁻¹ • ∑ j, Measure.dirac (q j)

/-- The measure `μ = ρ(t) dt`. -/
def densityMeasure (ρ : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (ρ t))

/-- `cp` is a coupling of `lam` and `mu`: a probability measure on `ℝ × ℝ` with these marginals. -/
abbrev IsCoupling (cp : Measure (ℝ × ℝ)) (lam mu : Measure ℝ) : Prop :=
  IsProbabilityMeasure cp ∧ cp.map Prod.fst = lam ∧ cp.map Prod.snd = mu

/-- Wasserstein distance of order one: `W_1(lam, mu) = inf over couplings of ∫|x − y| dcp`. -/
def W1 (lam mu : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (cp : Measure (ℝ × ℝ)) (_ : IsCoupling cp lam mu), ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂cp

/-- `f ∈ C_c²(ℝ)`. -/
abbrev Good (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 f ∧ HasCompactSupport f

/-- Tent cutoff: `1` on `|s| ≤ δ`, `0` on `|s| ≥ 2δ`, and `1/δ`-Lipschitz. -/
def tent (δ s : ℝ) : ℝ :=
  max (min 1 (2 - |s| / δ)) 0

/-- The right-hand side `C ‖f'‖_∞ (√c + a) + 2 ‖f''‖_∞ c`, with `a = N^{−2/3}`. -/
def Fbound (C M2 a c : ℝ) : ℝ :=
  C * (Real.sqrt c + a) + 2 * M2 * c

/-! ## 1. Elementary bounds for arctan -/

lemma hasDerivAt_arctan_aux (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.arctan x - x + x ^ 3 / 3) (1 / (1 + x ^ 2) - 1 + x ^ 2) x := by
  have h := ((Real.hasDerivAt_arctan x).sub (hasDerivAt_id' x)).add
    ((hasDerivAt_pow 3 x).div_const 3)
  refine h.congr_deriv ?_
  norm_num

/-- `y − y³/3 ≤ arctan y` for `y ≥ 0`. -/
lemma arctan_lower {y : ℝ} (hy : 0 ≤ y) : y - y ^ 3 / 3 ≤ Real.arctan y := by
  have hmono : MonotoneOn (fun x : ℝ => Real.arctan x - x + x ^ 3 / 3) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x _
      exact (hasDerivAt_arctan_aux x).continuousAt.continuousWithinAt
    · intro x _
      exact (hasDerivAt_arctan_aux x).differentiableAt.differentiableWithinAt
    · intro x _
      rw [(hasDerivAt_arctan_aux x).deriv]
      have hpos : (0:ℝ) < 1 + x ^ 2 := by positivity
      have e : 1 / (1 + x ^ 2) - 1 + x ^ 2 = x ^ 4 / (1 + x ^ 2) := by
        field_simp
        ring
      rw [e]
      positivity
  have h := hmono (Set.mem_Ici.mpr (le_refl (0:ℝ))) (Set.mem_Ici.mpr hy) hy
  norm_num at h
  linarith

/-- `|arctan y − y| ≤ |y|³/3` for all `y`. -/
lemma abs_arctan_sub_self_le (y : ℝ) : |Real.arctan y - y| ≤ |y| ^ 3 / 3 := by
  rcases le_total 0 y with hy | hy
  · have h1 := arctan_lower hy
    have h2 := Real.arctan_le_self hy
    have h3 : 0 ≤ y ^ 3 := pow_nonneg hy 3
    rw [abs_of_nonneg hy, abs_le]
    constructor <;> linarith
  · have hy' : 0 ≤ -y := neg_nonneg.mpr hy
    have h1 := arctan_lower hy'
    have h2 := Real.arctan_le_self hy'
    rw [Real.arctan_neg] at h1 h2
    have h3 : 0 ≤ (-y) ^ 3 := pow_nonneg hy' 3
    rw [abs_of_nonpos hy, abs_le]
    constructor <;> linarith

/-- For `y ≠ 0`: `|arctan y / y| ≤ 1` and `|arctan y / y − 1| ≤ y²/3`. -/
lemma arctan_div_bounds {y : ℝ} (hy : y ≠ 0) :
    |Real.arctan y / y| ≤ 1 ∧ |Real.arctan y / y - 1| ≤ y ^ 2 / 3 := by
  have hpos : 0 < |y| := abs_pos.mpr hy
  refine ⟨?_, ?_⟩
  · rw [abs_div, div_le_one hpos]
    exact Real.abs_arctan_le_abs
  · have e : Real.arctan y / y - 1 = (Real.arctan y - y) / y := by
      rw [sub_div, div_self hy]
    rw [e, abs_div, div_le_iff₀ hpos]
    calc |Real.arctan y - y| ≤ |y| ^ 3 / 3 := abs_arctan_sub_self_le y
      _ = y ^ 2 / 3 * |y| := by rw [← sq_abs y]; ring

/-! ## 2. Regularity of `f ∈ C_c²` -/

lemma good_contDiff_deriv {f : ℝ → ℝ} (hf : Good f) : ContDiff ℝ 1 (deriv f) :=
  (show ContDiff ℝ (1 + 1) f from hf.1).deriv'

lemma good_deriv_cont {f : ℝ → ℝ} (hf : Good f) : Continuous (deriv f) :=
  (good_contDiff_deriv hf).continuous

lemma good_deriv_diff {f : ℝ → ℝ} (hf : Good f) : Differentiable ℝ (deriv f) :=
  (good_contDiff_deriv hf).differentiable (by norm_num)

lemma good_deriv2_cont {f : ℝ → ℝ} (hf : Good f) : Continuous (deriv (deriv f)) :=
  (good_contDiff_deriv hf).continuous_deriv le_rfl

lemma good_deriv_cs {f : ℝ → ℝ} (hf : Good f) : HasCompactSupport (deriv f) :=
  hf.2.deriv

lemma good_deriv2_cs {f : ℝ → ℝ} (hf : Good f) : HasCompactSupport (deriv (deriv f)) :=
  hf.2.deriv.deriv

lemma good_hasDerivAt {f : ℝ → ℝ} (hf : Good f) (x : ℝ) : HasDerivAt f (deriv f x) x :=
  ((hf.1.differentiable (by norm_num)) x).hasDerivAt

/-! ## 3. Sup norms and the Lipschitz bound for `f'` -/

lemma abs_le_supAbs {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (x : ℝ) :
    |g x| ≤ supAbs g := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  have hbdd : BddAbove (Set.range fun y => |g y|) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨y, rfl⟩
    have h := hC y
    rw [Real.norm_eq_abs] at h
    exact h
  unfold supAbs
  exact le_ciSup hbdd x

lemma supAbs_nonneg {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    0 ≤ supAbs g :=
  (abs_nonneg _).trans (abs_le_supAbs hg hgc 0)

lemma supAbs_deriv_nonneg {f : ℝ → ℝ} (hf : Good f) : 0 ≤ supAbs (deriv f) :=
  supAbs_nonneg (good_deriv_cont hf) (good_deriv_cs hf)

lemma supAbs_deriv2_nonneg {f : ℝ → ℝ} (hf : Good f) : 0 ≤ supAbs (deriv (deriv f)) :=
  supAbs_nonneg (good_deriv2_cont hf) (good_deriv2_cs hf)

lemma abs_deriv_le_supAbs {f : ℝ → ℝ} (hf : Good f) (x : ℝ) :
    |deriv f x| ≤ supAbs (deriv f) :=
  abs_le_supAbs (good_deriv_cont hf) (good_deriv_cs hf) x

lemma abs_deriv2_le_supAbs {f : ℝ → ℝ} (hf : Good f) (x : ℝ) :
    |deriv (deriv f) x| ≤ supAbs (deriv (deriv f)) :=
  abs_le_supAbs (good_deriv2_cont hf) (good_deriv2_cs hf) x

/-- `f'` is `‖f''‖_∞`-Lipschitz. -/
lemma deriv_lip {f : ℝ → ℝ} (hf : Good f) (a b : ℝ) :
    |deriv f a - deriv f b| ≤ supAbs (deriv (deriv f)) * |a - b| := by
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := deriv f) (C := supAbs (deriv (deriv f)))
    (fun x _ => good_deriv_diff hf x)
    (fun x _ => by rw [Real.norm_eq_abs]; exact abs_deriv2_le_supAbs hf x)
    (Set.mem_univ a) (Set.mem_univ b)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  rw [abs_sub_comm (deriv f a), abs_sub_comm a]
  exact h

/-! ## 4. The kernel `K^f` -/

/-- Fundamental theorem of calculus: `(t − u) K^f(t,u) = f(t) − f(u)`. -/
lemma Kf_mul_sub {f : ℝ → ℝ} (hf : Good f) (t u : ℝ) :
    (t - u) * Kf f t u = f t - f u := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => f (u + s * (t - u)))
      ((t - u) * deriv f (u + s * (t - u))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => u + s * (t - u)) (t - u) s := by
      simpa using ((hasDerivAt_id' s).mul_const (t - u)).const_add u
    have h2 := HasDerivAt.comp (x := s) (good_hasDerivAt hf (u + s * (t - u))) h1
    exact h2.congr_deriv (mul_comm _ _)
  have hcont : Continuous (fun s : ℝ => (t - u) * deriv f (u + s * (t - u))) :=
    continuous_const.mul ((good_deriv_cont hf).comp (by fun_prop))
  have hFTC : ∫ s in (0:ℝ)..1, (t - u) * deriv f (u + s * (t - u)) = f t - f u := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => f (u + s * (t - u)))
      (f' := fun s : ℝ => (t - u) * deriv f (u + s * (t - u)))
      (fun s _ => hd s) (hcont.intervalIntegrable 0 1)
    simpa using h
  unfold Kf
  rw [← intervalIntegral.integral_const_mul]
  exact hFTC

/-- `|K^f| ≤ ‖f'‖_∞`. -/
lemma Kf_abs_le {f : ℝ → ℝ} (hf : Good f) (t u : ℝ) : |Kf f t u| ≤ supAbs (deriv f) := by
  have hpt : ∀ s ∈ Set.uIoc (0:ℝ) 1, ‖deriv f (u + s * (t - u))‖ ≤ supAbs (deriv f) := by
    intro s _
    rw [Real.norm_eq_abs]
    exact abs_deriv_le_supAbs hf _
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (C := supAbs (deriv f)) (f := fun s : ℝ => deriv f (u + s * (t - u))) hpt
  rw [Real.norm_eq_abs] at h
  unfold Kf
  simpa using h

/-- `K^f` is `‖f''‖_∞`-Lipschitz in each variable (and jointly in the sum of the distances). -/
lemma Kf_lip {f : ℝ → ℝ} (hf : Good f) (t u t' u' : ℝ) :
    |Kf f t u - Kf f t' u'| ≤ supAbs (deriv (deriv f)) * (|t - t'| + |u - u'|) := by
  have hM2 : 0 ≤ supAbs (deriv (deriv f)) := supAbs_deriv2_nonneg hf
  have hI1 : IntervalIntegrable (fun s : ℝ => deriv f (u + s * (t - u))) volume 0 1 :=
    ((good_deriv_cont hf).comp (by fun_prop)).intervalIntegrable 0 1
  have hI2 : IntervalIntegrable (fun s : ℝ => deriv f (u' + s * (t' - u'))) volume 0 1 :=
    ((good_deriv_cont hf).comp (by fun_prop)).intervalIntegrable 0 1
  have hsub : Kf f t u - Kf f t' u' =
      ∫ s in (0:ℝ)..1, (deriv f (u + s * (t - u)) - deriv f (u' + s * (t' - u'))) := by
    unfold Kf
    rw [intervalIntegral.integral_sub hI1 hI2]
  have hpt : ∀ s ∈ Set.uIoc (0:ℝ) 1,
      ‖deriv f (u + s * (t - u)) - deriv f (u' + s * (t' - u'))‖ ≤
        supAbs (deriv (deriv f)) * (|t - t'| + |u - u'|) := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    obtain ⟨hs0, hs1⟩ := hs
    rw [Real.norm_eq_abs]
    have hA : |(u + s * (t - u)) - (u' + s * (t' - u'))| ≤ |t - t'| + |u - u'| := by
      have e : (u + s * (t - u)) - (u' + s * (t' - u'))
          = (u - u') * (1 - s) + (t - t') * s := by ring
      rw [e]
      have h1 : |(u - u') * (1 - s)| = |u - u'| * (1 - s) := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s)]
      have h2 : |(t - t') * s| = |t - t'| * s := by
        rw [abs_mul, abs_of_nonneg hs0.le]
      calc |(u - u') * (1 - s) + (t - t') * s|
          ≤ |(u - u') * (1 - s)| + |(t - t') * s| := abs_add_le _ _
        _ = |u - u'| * (1 - s) + |t - t'| * s := by rw [h1, h2]
        _ ≤ |u - u'| + |t - t'| := by
            nlinarith [mul_nonneg (abs_nonneg (u - u')) hs0.le,
              mul_nonneg (abs_nonneg (t - t')) (by linarith : (0:ℝ) ≤ 1 - s)]
        _ = |t - t'| + |u - u'| := by ring
    calc |deriv f (u + s * (t - u)) - deriv f (u' + s * (t' - u'))|
        ≤ supAbs (deriv (deriv f)) * |(u + s * (t - u)) - (u' + s * (t' - u'))| :=
          deriv_lip hf _ _
      _ ≤ supAbs (deriv (deriv f)) * (|t - t'| + |u - u'|) :=
          mul_le_mul_of_nonneg_left hA hM2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
    (C := supAbs (deriv (deriv f)) * (|t - t'| + |u - u'|))
    (f := fun s : ℝ => deriv f (u + s * (t - u)) - deriv f (u' + s * (t' - u'))) hpt
  rw [hsub]
  simpa [Real.norm_eq_abs] using h

/-- A function on `ℝ × ℝ` that is Lipschitz for the sum of the coordinate distances is continuous. -/
lemma continuous_of_lip2 {F : ℝ × ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ p q : ℝ × ℝ, |F p - F q| ≤ C * dist p q) : Continuous F := by
  apply LipschitzWith.continuous (K := Real.toNNReal C)
  apply LipschitzWith.of_dist_le_mul
  intro p q
  rw [Real.dist_eq, Real.coe_toNNReal C hC]
  exact h p q

lemma abs_fst_sub_le_dist (p q : ℝ × ℝ) : |p.1 - q.1| ≤ dist p q := by
  rw [Prod.dist_eq, ← Real.dist_eq]
  exact le_max_left _ _

lemma abs_snd_sub_le_dist (p q : ℝ × ℝ) : |p.2 - q.2| ≤ dist p q := by
  rw [Prod.dist_eq, ← Real.dist_eq]
  exact le_max_right _ _

lemma Kf_continuous {f : ℝ → ℝ} (hf : Good f) :
    Continuous (fun p : ℝ × ℝ => Kf f p.1 p.2) := by
  have hM2 : 0 ≤ supAbs (deriv (deriv f)) := supAbs_deriv2_nonneg hf
  apply continuous_of_lip2 (C := 2 * supAbs (deriv (deriv f))) (by linarith)
  intro p q
  calc |Kf f p.1 p.2 - Kf f q.1 q.2|
      ≤ supAbs (deriv (deriv f)) * (|p.1 - q.1| + |p.2 - q.2|) := Kf_lip hf _ _ _ _
    _ ≤ supAbs (deriv (deriv f)) * (dist p q + dist p q) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (abs_fst_sub_le_dist p q) (abs_snd_sub_le_dist p q)) hM2
    _ = 2 * supAbs (deriv (deriv f)) * dist p q := by ring

/-- Lipschitz in the first variable with constant `‖f''‖_∞`. -/
lemma Kf_L1 {f : ℝ → ℝ} (hf : Good f) (x y x' : ℝ) :
    |Kf f x x' - Kf f y x'| ≤ supAbs (deriv (deriv f)) * |x - y| := by
  have h := Kf_lip hf x x' y x'
  rw [sub_self, abs_zero, add_zero] at h
  exact h

/-- Lipschitz in the second variable with constant `‖f''‖_∞`. -/
lemma Kf_L2 {f : ℝ → ℝ} (hf : Good f) (y x' y' : ℝ) :
    |Kf f y x' - Kf f y y'| ≤ supAbs (deriv (deriv f)) * |x' - y'| := by
  have h := Kf_lip hf y x' y y'
  rw [sub_self, abs_zero, zero_add] at h
  exact h

/-! ## 5. The kernel `K_N^f` -/

lemma KN_eq_formula (κ N : ℝ) (f : ℝ → ℝ) (t u : ℝ) :
    KN κ N f t u = (N / κ) * (f t - f u) * Real.arctan (κ / (N * (t - u))) := by
  unfold KN
  by_cases h : t = u
  · subst h
    simp
  · simp [h]

/-- For `t ≠ u`: `K_N^f(t,u) = K^f(t,u) · arctan(y)/y` with `y = κ/(N(t−u))`. -/
lemma KN_eq_Kf_mul {f : ℝ → ℝ} (hf : Good f) {κ N : ℝ} (hκ : κ ≠ 0) (hN : N ≠ 0) {t u : ℝ}
    (htu : t ≠ u) :
    KN κ N f t u = Kf f t u * (Real.arctan (κ / (N * (t - u))) / (κ / (N * (t - u)))) := by
  have hx : t - u ≠ 0 := sub_ne_zero.mpr htu
  have hKf := Kf_mul_sub hf t u
  rw [KN_eq_formula, ← hKf]
  generalize Real.arctan (κ / (N * (t - u))) = A
  field_simp

lemma KN_measurable {f : ℝ → ℝ} (hf : Good f) (κ N : ℝ) :
    Measurable (fun p : ℝ × ℝ => KN κ N f p.1 p.2) := by
  have hfc : Continuous f := hf.1.continuous
  have e : (fun p : ℝ × ℝ => KN κ N f p.1 p.2)
      = fun p : ℝ × ℝ => (N / κ) * (f p.1 - f p.2) * Real.arctan (κ / (N * (p.1 - p.2))) :=
    funext fun p => KN_eq_formula κ N f p.1 p.2
  rw [e]
  apply Measurable.mul
  · exact measurable_const.mul
      ((hfc.measurable.comp measurable_fst).sub (hfc.measurable.comp measurable_snd))
  · exact Real.continuous_arctan.measurable.comp
      (measurable_const.div (measurable_const.mul (measurable_fst.sub measurable_snd)))

/-- `|K_N^f| ≤ ‖f'‖_∞`. -/
lemma abs_KN_le {f : ℝ → ℝ} (hf : Good f) {κ N : ℝ} (hκ : κ ≠ 0) (hN : N ≠ 0) (t u : ℝ) :
    |KN κ N f t u| ≤ supAbs (deriv f) := by
  by_cases htu : t = u
  · subst htu
    unfold KN
    simpa using supAbs_deriv_nonneg hf
  · rw [KN_eq_Kf_mul hf hκ hN htu, abs_mul]
    have h1 := (arctan_div_bounds
      (y := κ / (N * (t - u))) (div_ne_zero hκ (mul_ne_zero hN (sub_ne_zero.mpr htu)))).1
    calc |Kf f t u| * |Real.arctan (κ / (N * (t - u))) / (κ / (N * (t - u)))|
        ≤ supAbs (deriv f) * 1 :=
          mul_le_mul (Kf_abs_le hf t u) h1 (abs_nonneg _) (supAbs_deriv_nonneg hf)
      _ = supAbs (deriv f) := mul_one _

/-- Algebra of the cube-root bound: `(κ/(Nx))²/3 = κ²/(3N²x²)`. -/
lemma sq_div_three {κ N x : ℝ} :
    (κ / (N * x)) ^ 2 / 3 = κ ^ 2 / (3 * N ^ 2 * x ^ 2) := by
  rw [div_pow, mul_pow, div_div]
  ring

/-- Off the diagonal: `|K_N^f − K^f| ≤ ‖f'‖_∞ κ²/(3N²(t−u)²)`. -/
lemma abs_KN_sub_Kf_le {f : ℝ → ℝ} (hf : Good f) {κ N : ℝ} (hκ : κ ≠ 0) (hN : N ≠ 0)
    {t u : ℝ} (htu : t ≠ u) :
    |KN κ N f t u - Kf f t u| ≤ supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * (t - u) ^ 2)) := by
  have hx : t - u ≠ 0 := sub_ne_zero.mpr htu
  have hy : κ / (N * (t - u)) ≠ 0 := div_ne_zero hκ (mul_ne_zero hN hx)
  have hb := arctan_div_bounds hy
  have hy2 : (κ / (N * (t - u))) ^ 2 / 3 = κ ^ 2 / (3 * N ^ 2 * (t - u) ^ 2) :=
    sq_div_three
  rw [KN_eq_Kf_mul hf hκ hN htu]
  calc |Kf f t u * (Real.arctan (κ / (N * (t - u))) / (κ / (N * (t - u)))) - Kf f t u|
      = |Kf f t u| * |Real.arctan (κ / (N * (t - u))) / (κ / (N * (t - u))) - 1| := by
        rw [← abs_mul]
        congr 1
        ring
    _ ≤ supAbs (deriv f) * ((κ / (N * (t - u))) ^ 2 / 3) :=
        mul_le_mul (Kf_abs_le hf t u) hb.2 (abs_nonneg _) (supAbs_deriv_nonneg hf)
    _ = supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * (t - u) ^ 2)) := by rw [hy2]

/-! ## 6. The tent cutoff -/

lemma tent_nonneg (δ s : ℝ) : 0 ≤ tent δ s := le_max_right _ _

lemma tent_le_one (δ s : ℝ) : tent δ s ≤ 1 :=
  max_le (min_le_left _ _) zero_le_one

lemma abs_tent_le_one (δ s : ℝ) : |tent δ s| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [tent_nonneg δ s], tent_le_one δ s⟩

lemma tent_eq_one {δ s : ℝ} (hδ : 0 < δ) (h : |s| ≤ δ) : tent δ s = 1 := by
  have h1 : |s| / δ ≤ 1 := (div_le_one hδ).mpr h
  have h2 : (1:ℝ) ≤ 2 - |s| / δ := by linarith
  unfold tent
  rw [min_eq_left h2]
  exact max_eq_left zero_le_one

lemma tent_eq_zero {δ s : ℝ} (hδ : 0 < δ) (h : 2 * δ ≤ |s|) : tent δ s = 0 := by
  have h1 : 2 ≤ |s| / δ := (le_div_iff₀ hδ).mpr (by linarith)
  have h2 : min 1 (2 - |s| / δ) ≤ 0 := le_trans (min_le_right _ _) (by linarith)
  unfold tent
  exact max_eq_right h2

/-- `1/δ`-Lipschitz. -/
lemma tent_lip {δ : ℝ} (hδ : 0 < δ) (s s' : ℝ) :
    |tent δ s - tent δ s'| ≤ |s - s'| / δ := by
  have h1 : |min 1 (2 - |s| / δ) - min 1 (2 - |s'| / δ)|
      ≤ |(2 - |s| / δ) - (2 - |s'| / δ)| := by
    have h := abs_min_sub_min_le_max (1:ℝ) (2 - |s| / δ) 1 (2 - |s'| / δ)
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)] at h
    exact h
  have h2 : |(2 - |s| / δ) - (2 - |s'| / δ)| ≤ |s - s'| / δ := by
    rw [show (2 - |s| / δ) - (2 - |s'| / δ) = (|s'| - |s|) / δ by ring, abs_div,
      abs_of_pos hδ]
    refine div_le_div_of_nonneg_right ?_ hδ.le
    calc |(|s'| - |s|)| ≤ |s' - s| := abs_abs_sub_abs_le_abs_sub s' s
      _ = |s - s'| := abs_sub_comm s' s
  unfold tent
  calc |max (min 1 (2 - |s| / δ)) 0 - max (min 1 (2 - |s'| / δ)) 0|
      ≤ |min 1 (2 - |s| / δ) - min 1 (2 - |s'| / δ)| := abs_max_sub_max_le_abs _ _ _
    _ ≤ |(2 - |s| / δ) - (2 - |s'| / δ)| := h1
    _ ≤ |s - s'| / δ := h2

lemma continuous_tent_pair {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun p : ℝ × ℝ => tent δ (p.1 - p.2)) := by
  apply continuous_of_lip2 (C := 2 / δ) (div_nonneg (by norm_num) hδ.le)
  intro p q
  have hd : |(p.1 - p.2) - (q.1 - q.2)| ≤ dist p q + dist p q := by
    have e : (p.1 - p.2) - (q.1 - q.2) = (p.1 - q.1) - (p.2 - q.2) := by ring
    rw [e]
    have h1 := abs_fst_sub_le_dist p q
    have h2 := abs_snd_sub_le_dist p q
    rw [abs_le]
    constructor <;> linarith [le_abs_self (p.1 - q.1), neg_abs_le (p.1 - q.1),
      le_abs_self (p.2 - q.2), neg_abs_le (p.2 - q.2)]
  calc |tent δ (p.1 - p.2) - tent δ (q.1 - q.2)|
      ≤ |(p.1 - p.2) - (q.1 - q.2)| / δ := tent_lip hδ _ _
    _ ≤ (dist p q + dist p q) / δ := div_le_div_of_nonneg_right hd hδ.le
    _ = 2 / δ * dist p q := by ring

lemma tent_L1 {δ : ℝ} (hδ : 0 < δ) (x y x' : ℝ) :
    |tent δ (x - x') - tent δ (y - x')| ≤ 1 / δ * |x - y| := by
  have h := tent_lip hδ (x - x') (y - x')
  have e : (x - x') - (y - x') = x - y := by ring
  rw [e] at h
  exact le_trans h (le_of_eq (by ring))

lemma tent_L2 {δ : ℝ} (hδ : 0 < δ) (y x' y' : ℝ) :
    |tent δ (y - x') - tent δ (y - y')| ≤ 1 / δ * |x' - y'| := by
  have h := tent_lip hδ (y - x') (y - y')
  have e : (y - x') - (y - y') = y' - x' := by ring
  rw [e, abs_sub_comm y' x'] at h
  exact le_trans h (le_of_eq (by ring))

/-- Pointwise kernel error with the tent cutoff: on the strip `|t−u| ≤ δ` the error is at most
`2‖f'‖_∞`; off it, at most `‖f'‖_∞ κ²/(3N²δ²)`. -/
lemma abs_KN_sub_Kf_le_tent {f : ℝ → ℝ} (hf : Good f) {κ N : ℝ} (hκ : κ ≠ 0) (hN : N ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (t u : ℝ) :
    |KN κ N f t u - Kf f t u| ≤
      2 * supAbs (deriv f) * tent δ (t - u) + supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2)) := by
  have hM1 : 0 ≤ supAbs (deriv f) := supAbs_deriv_nonneg hf
  have hpos : 0 ≤ 2 * supAbs (deriv f) * tent δ (t - u) :=
    mul_nonneg (mul_nonneg (by norm_num) hM1) (tent_nonneg δ (t - u))
  have hK : 0 ≤ supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2)) :=
    mul_nonneg hM1 (div_nonneg (sq_nonneg κ) (by positivity))
  by_cases hin : |t - u| ≤ δ
  · rw [tent_eq_one hδ hin]
    have h1 : |KN κ N f t u - Kf f t u| ≤ |KN κ N f t u| + |Kf f t u| := by
      have := abs_add_le (KN κ N f t u) (-Kf f t u)
      rw [← sub_eq_add_neg, abs_neg] at this
      exact this
    have h2 := abs_KN_le hf hκ hN t u
    have h3 := Kf_abs_le hf t u
    linarith
  · have htu : t ≠ u := by
      intro h
      apply hin
      rw [h, sub_self, abs_zero]
      exact hδ.le
    have hlt : δ < |t - u| := not_le.mp hin
    have hsq : δ ^ 2 ≤ (t - u) ^ 2 := by
      nlinarith [sq_abs (t - u), abs_nonneg (t - u)]
    have hN2 : 0 < N ^ 2 := lt_of_le_of_ne (sq_nonneg N) (Ne.symm (pow_ne_zero 2 hN))
    have hc : 0 < 3 * N ^ 2 * δ ^ 2 := mul_pos (mul_pos (by norm_num) hN2) (pow_pos hδ 2)
    have hle : 3 * N ^ 2 * δ ^ 2 ≤ 3 * N ^ 2 * (t - u) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have hA := abs_KN_sub_Kf_le hf hκ hN htu
    have hB : supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * (t - u) ^ 2))
        ≤ supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (sq_nonneg κ) hc hle) hM1
    linarith

/-! ## 7. Measures: the empirical measure, the density and couplings -/

lemma empirical_isProbabilityMeasure {N : ℕ} (hN : 1 ≤ N) (q : Fin N → ℝ) :
    IsProbabilityMeasure (empirical N q) := by
  constructor
  unfold empirical
  rw [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, smul_eq_mul]
  have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  exact ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top N)

/-- `μ⊗μ{|t−u| ≤ 2δ} ≤ 4Mρδ` for `μ = ρ dt` with `ρ ≤ Mρ`. -/
lemma density_prod_mass_le {ρ : ℝ → ℝ} {Mρ : ℝ} (hρ_nonneg : ∀ t, 0 ≤ ρ t)
    (hρ_bdd : ∀ t, ρ t ≤ Mρ) [IsProbabilityMeasure (densityMeasure ρ)] (δ : ℝ) :
    (densityMeasure ρ).prod (densityMeasure ρ) {p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ}
      ≤ ENNReal.ofReal (4 * Mρ * δ) := by
  have hMρ0 : 0 ≤ Mρ := (hρ_nonneg 0).trans (hρ_bdd 0)
  have hS : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hsec : ∀ x : ℝ, densityMeasure ρ (Prod.mk x ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ})
      ≤ ENNReal.ofReal (4 * Mρ * δ) := by
    intro x
    calc densityMeasure ρ (Prod.mk x ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ})
        ≤ densityMeasure ρ (Set.Icc (x - 2 * δ) (x + 2 * δ)) := by
          apply measure_mono
          intro y hy
          have hy' : |x - y| ≤ 2 * δ := hy
          obtain ⟨h1, h2⟩ := abs_le.mp hy'
          exact ⟨by linarith, by linarith⟩
      _ ≤ ENNReal.ofReal (4 * Mρ * δ) := by
          unfold densityMeasure
          rw [withDensity_apply _ measurableSet_Icc]
          calc ∫⁻ y in Set.Icc (x - 2 * δ) (x + 2 * δ), ENNReal.ofReal (ρ y)
              ≤ ∫⁻ y in Set.Icc (x - 2 * δ) (x + 2 * δ), ENNReal.ofReal Mρ :=
                setLIntegral_mono measurable_const fun y _ => ENNReal.ofReal_le_ofReal (hρ_bdd y)
            _ = ENNReal.ofReal (4 * Mρ * δ) := by
                rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul hMρ0]
                congr 1
                ring
  rw [Measure.prod_apply hS]
  calc ∫⁻ x, densityMeasure ρ (Prod.mk x ⁻¹' {p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ})
        ∂(densityMeasure ρ)
      ≤ ∫⁻ _x, ENNReal.ofReal (4 * Mρ * δ) ∂(densityMeasure ρ) := lintegral_mono hsec
    _ = ENNReal.ofReal (4 * Mρ * δ) := by rw [lintegral_const, measure_univ, mul_one]

/-- `∫ tent(t−u) dμ⊗μ ≤ 4Mρδ` for `μ = ρ dt` with `ρ ≤ Mρ`. -/
lemma density_tent_bound {ρ : ℝ → ℝ} {Mρ : ℝ} (hρ_nonneg : ∀ t, 0 ≤ ρ t)
    (hρ_bdd : ∀ t, ρ t ≤ Mρ) [IsProbabilityMeasure (densityMeasure ρ)] {δ : ℝ} (hδ : 0 < δ) :
    ∫ p, tent δ (p.1 - p.2) ∂((densityMeasure ρ).prod (densityMeasure ρ)) ≤ 4 * Mρ * δ := by
  have hMρ0 : 0 ≤ Mρ := (hρ_nonneg 0).trans (hρ_bdd 0)
  have hS : MeasurableSet {p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  have hpt : ∀ p : ℝ × ℝ, tent δ (p.1 - p.2)
      ≤ ({p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ}).indicator (1 : ℝ × ℝ → ℝ) p := by
    intro p
    by_cases hp : |p.1 - p.2| ≤ 2 * δ
    · rw [Set.indicator_of_mem (show p ∈ {p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ} from hp)]
      exact tent_le_one _ _
    · rw [Set.indicator_of_notMem (show p ∉ {p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ} from hp)]
      exact (tent_eq_zero hδ (le_of_lt (not_le.mp hp))).le
  have hGint : Integrable (fun p : ℝ × ℝ => tent δ (p.1 - p.2))
      ((densityMeasure ρ).prod (densityMeasure ρ)) :=
    Integrable.of_bound (continuous_tent_pair hδ).aestronglyMeasurable 1
      (ae_of_all _ fun p => abs_tent_le_one δ (p.1 - p.2))
  have hIind : Integrable ({p : ℝ × ℝ | |p.1 - p.2| ≤ 2 * δ}.indicator (1 : ℝ × ℝ → ℝ))
      ((densityMeasure ρ).prod (densityMeasure ρ)) :=
    (integrable_const (1 : ℝ)).indicator hS
  have hle := integral_mono hGint hIind (fun p => hpt p)
  rw [integral_indicator_one hS] at hle
  refine hle.trans ?_
  unfold Measure.real
  apply ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg (by norm_num) hMρ0) hδ.le)
  exact density_prod_mass_le hρ_nonneg hρ_bdd δ

lemma integral_abs_fst {cp : Measure (ℝ × ℝ)} [IsProbabilityMeasure cp] :
    ∫ z : (ℝ × ℝ) × (ℝ × ℝ), |z.1.1 - z.1.2| ∂(cp.prod cp) = ∫ p, |p.1 - p.2| ∂cp := by
  have h := integral_fun_fst (μ := cp) (ν := cp) (fun p : ℝ × ℝ => |p.1 - p.2|)
  simpa using h

lemma integral_abs_snd {cp : Measure (ℝ × ℝ)} [IsProbabilityMeasure cp] :
    ∫ z : (ℝ × ℝ) × (ℝ × ℝ), |z.2.1 - z.2.2| ∂(cp.prod cp) = ∫ p, |p.1 - p.2| ∂cp := by
  have h := integral_fun_snd (μ := cp) (ν := cp) (fun p : ℝ × ℝ => |p.1 - p.2|)
  simpa using h

/-- Two-coordinate coupling bound: for a coupling `cp` of `(lam, mu)` and `G` bounded, continuous
and Lipschitz in each variable with constant `L`,
`|∬G dlam⊗² − ∬G dmu⊗²| ≤ 2 L ∫|x − y| dcp`. -/
lemma two_coupling_bound {lam mu : Measure ℝ} [IsProbabilityMeasure lam]
    [IsProbabilityMeasure mu] {cp : Measure (ℝ × ℝ)} (hcp : IsCoupling cp lam mu)
    (hint : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) cp)
    {G : ℝ × ℝ → ℝ} (hG : Continuous G) {B L : ℝ} (hB : ∀ p, |G p| ≤ B)
    (hL1 : ∀ x y x' : ℝ, |G (x, x') - G (y, x')| ≤ L * |x - y|)
    (hL2 : ∀ y x' y' : ℝ, |G (y, x') - G (y, y')| ≤ L * |x' - y'|) :
    |(∫ p, G p ∂(lam.prod lam)) - ∫ p, G p ∂(mu.prod mu)|
      ≤ 2 * L * ∫ p, |p.1 - p.2| ∂cp := by
  obtain ⟨hcpP, hfst, hsnd⟩ := hcp
  have hmap1 : lam.prod lam = (cp.prod cp).map (Prod.map Prod.fst Prod.fst) := by
    rw [← hfst, Measure.map_prod_map cp cp measurable_fst measurable_fst]
  have hmap2 : mu.prod mu = (cp.prod cp).map (Prod.map Prod.snd Prod.snd) := by
    rw [← hsnd, Measure.map_prod_map cp cp measurable_snd measurable_snd]
  have e1 : ∫ p, G p ∂(lam.prod lam) = ∫ z, G (z.1.1, z.2.1) ∂(cp.prod cp) := by
    rw [hmap1]
    exact integral_map (measurable_fst.prodMap measurable_fst).aemeasurable
      hG.aestronglyMeasurable
  have e2 : ∫ p, G p ∂(mu.prod mu) = ∫ z, G (z.1.2, z.2.2) ∂(cp.prod cp) := by
    rw [hmap2]
    exact integral_map (measurable_snd.prodMap measurable_snd).aemeasurable
      hG.aestronglyMeasurable
  have hI1 : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => |z.1.1 - z.1.2|) (cp.prod cp) :=
    hint.comp_fst cp
  have hI2 : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => |z.2.1 - z.2.2|) (cp.prod cp) :=
    hint.comp_snd cp
  have hc1 : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => G (z.1.1, z.2.1)) :=
    hG.comp (by fun_prop)
  have hc2 : Continuous (fun z : (ℝ × ℝ) × (ℝ × ℝ) => G (z.1.2, z.2.2)) :=
    hG.comp (by fun_prop)
  have hGint1 : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => G (z.1.1, z.2.1)) (cp.prod cp) :=
    Integrable.of_bound hc1.aestronglyMeasurable B
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hB _)
  have hGint2 : Integrable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => G (z.1.2, z.2.2)) (cp.prod cp) :=
    Integrable.of_bound hc2.aestronglyMeasurable B
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hB _)
  have hD : ∀ z : (ℝ × ℝ) × (ℝ × ℝ),
      |G (z.1.1, z.2.1) - G (z.1.2, z.2.2)|
        ≤ L * |z.1.1 - z.1.2| + L * |z.2.1 - z.2.2| := by
    intro z
    calc |G (z.1.1, z.2.1) - G (z.1.2, z.2.2)|
        ≤ |G (z.1.1, z.2.1) - G (z.1.2, z.2.1)| + |G (z.1.2, z.2.1) - G (z.1.2, z.2.2)| :=
          abs_sub_le _ _ _
      _ ≤ L * |z.1.1 - z.1.2| + L * |z.2.1 - z.2.2| := add_le_add (hL1 _ _ _) (hL2 _ _ _)
  have hgint : Integrable
      (fun z : (ℝ × ℝ) × (ℝ × ℝ) => L * |z.1.1 - z.1.2| + L * |z.2.1 - z.2.2|) (cp.prod cp) :=
    (hI1.const_mul L).add (hI2.const_mul L)
  have hgval : ∫ z : (ℝ × ℝ) × (ℝ × ℝ), (L * |z.1.1 - z.1.2| + L * |z.2.1 - z.2.2|)
      ∂(cp.prod cp) = 2 * L * ∫ p, |p.1 - p.2| ∂cp := by
    rw [integral_add (hI1.const_mul L) (hI2.const_mul L), integral_const_mul,
      integral_const_mul, integral_abs_fst, integral_abs_snd]
    ring
  rw [e1, e2, ← integral_sub hGint1 hGint2]
  have hbound := norm_integral_le_of_norm_le (f := fun z : (ℝ × ℝ) × (ℝ × ℝ) =>
      G (z.1.1, z.2.1) - G (z.1.2, z.2.2)) hgint
    (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hD z)
  rw [Real.norm_eq_abs] at hbound
  exact hbound.trans (le_of_eq hgval)

/-! ## 8. The one-coupling estimate, the cube-root identity, and the final assembly -/

/-- The estimate for one coupling and one scale `δ`. -/
lemma step1 {f : ℝ → ℝ} (hf : Good f) {κ N : ℝ} (hκ : κ ≠ 0) (hN : N ≠ 0)
    {lam mu : Measure ℝ} [IsProbabilityMeasure lam] [IsProbabilityMeasure mu]
    {cp : Measure (ℝ × ℝ)} (hcp : IsCoupling cp lam mu)
    (hint : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) cp)
    {Mρ : ℝ} (hmu2 : ∀ δ : ℝ, 0 < δ → ∫ p, tent δ (p.1 - p.2) ∂(mu.prod mu) ≤ 4 * Mρ * δ)
    {δ : ℝ} (hδ : 0 < δ) :
    |(∫ p, KN κ N f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(mu.prod mu)|
      ≤ 2 * supAbs (deriv f) * (4 * Mρ * δ + 2 * (1 / δ) * ∫ p, |p.1 - p.2| ∂cp)
        + supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2))
        + 2 * supAbs (deriv (deriv f)) * ∫ p, |p.1 - p.2| ∂cp := by
  have hM1 : 0 ≤ supAbs (deriv f) := supAbs_deriv_nonneg hf
  have hM2 : 0 ≤ supAbs (deriv (deriv f)) := supAbs_deriv2_nonneg hf
  have hKNm := KN_measurable hf κ N
  have hKfc : Continuous (fun p : ℝ × ℝ => Kf f p.1 p.2) := Kf_continuous hf
  have hKNint : Integrable (fun p : ℝ × ℝ => KN κ N f p.1 p.2) (lam.prod lam) :=
    Integrable.of_bound hKNm.aestronglyMeasurable (supAbs (deriv f))
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact abs_KN_le hf hκ hN p.1 p.2)
  have hKfint : Integrable (fun p : ℝ × ℝ => Kf f p.1 p.2) (lam.prod lam) :=
    Integrable.of_bound hKfc.aestronglyMeasurable (supAbs (deriv f))
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact Kf_abs_le hf p.1 p.2)
  have htent_cont : Continuous (fun p : ℝ × ℝ => tent δ (p.1 - p.2)) := continuous_tent_pair hδ
  have htent_int : Integrable (fun p : ℝ × ℝ => tent δ (p.1 - p.2)) (lam.prod lam) :=
    Integrable.of_bound htent_cont.aestronglyMeasurable 1
      (ae_of_all _ fun p => abs_tent_le_one δ (p.1 - p.2))
  -- Term A: the difference of the kernels against λ⊗λ, on and off the strip.
  have hHval : ∫ p : ℝ × ℝ,
      (2 * supAbs (deriv f) * tent δ (p.1 - p.2) + supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2)))
        ∂(lam.prod lam)
      = 2 * supAbs (deriv f) * ∫ p, tent δ (p.1 - p.2) ∂(lam.prod lam)
        + supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2)) := by
    rw [integral_add (htent_int.const_mul (2 * supAbs (deriv f)))
        (integrable_const (supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2)))),
      integral_const_mul]
    simp
  have hH_int : Integrable (fun p : ℝ × ℝ =>
      2 * supAbs (deriv f) * tent δ (p.1 - p.2) + supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2)))
      (lam.prod lam) :=
    (htent_int.const_mul (2 * supAbs (deriv f))).add
      (integrable_const (supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2))))
  have hA : |(∫ p, KN κ N f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(lam.prod lam)|
      ≤ 2 * supAbs (deriv f) * (∫ p, tent δ (p.1 - p.2) ∂(lam.prod lam))
        + supAbs (deriv f) * (κ ^ 2 / (3 * N ^ 2 * δ ^ 2)) := by
    rw [← integral_sub hKNint hKfint, ← Real.norm_eq_abs]
    have h := norm_integral_le_of_norm_le (f := fun p : ℝ × ℝ =>
        KN κ N f p.1 p.2 - Kf f p.1 p.2) hH_int
      (ae_of_all _ fun p => by
        rw [Real.norm_eq_abs]; exact abs_KN_sub_Kf_le_tent hf hκ hN hδ p.1 p.2)
    rw [hHval] at h
    exact h
  -- Term T: the tent integral moves from λ⊗λ to μ⊗μ at cost 2 (1/δ) c.
  have hT : ∫ p, tent δ (p.1 - p.2) ∂(lam.prod lam)
      ≤ ∫ p, tent δ (p.1 - p.2) ∂(mu.prod mu) + 2 * (1 / δ) * ∫ p, |p.1 - p.2| ∂cp := by
    have h := two_coupling_bound hcp hint htent_cont (B := 1) (L := 1 / δ)
      (fun p => abs_tent_le_one δ (p.1 - p.2))
      (fun x y x' => tent_L1 hδ x y x') (fun y x' y' => tent_L2 hδ y x' y')
    have h' := (abs_le.mp h).2
    linarith
  -- Term B: the replacement of λ⊗λ by μ⊗μ for K^f.
  have hB2 : |(∫ p, Kf f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(mu.prod mu)|
      ≤ 2 * supAbs (deriv (deriv f)) * ∫ p, |p.1 - p.2| ∂cp :=
    two_coupling_bound hcp hint hKfc (B := supAbs (deriv f)) (L := supAbs (deriv (deriv f)))
      (fun p => Kf_abs_le hf p.1 p.2) (fun x y x' => Kf_L1 hf x y x')
      (fun y x' y' => Kf_L2 hf y x' y')
  have hT' : ∫ p, tent δ (p.1 - p.2) ∂(lam.prod lam)
      ≤ 4 * Mρ * δ + 2 * (1 / δ) * ∫ p, |p.1 - p.2| ∂cp := by
    linarith [hT, hmu2 δ hδ]
  have hmul := mul_le_mul_of_nonneg_left hT' (by linarith : (0:ℝ) ≤ 2 * supAbs (deriv f))
  have hsplit : |(∫ p, KN κ N f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(mu.prod mu)|
      ≤ |(∫ p, KN κ N f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(lam.prod lam)|
        + |(∫ p, Kf f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(mu.prod mu)| := by
    have e : (∫ p, KN κ N f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(mu.prod mu)
        = ((∫ p, KN κ N f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(lam.prod lam))
          + ((∫ p, Kf f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(mu.prod mu)) := by ring
    rw [e]
    exact abs_add_le _ _
  linarith [hsplit, hA, hB2, hmul]

/-- `a = N^{−2/3}` satisfies `a³N² = 1`. -/
lemma cube_identity {N : ℝ} (hN : 1 ≤ N) : ((N : ℝ) ^ (-(2 / 3 : ℝ))) ^ 3 * N ^ 2 = 1 := by
  have hN0 : 0 < N := by linarith
  have h3 : ((N : ℝ) ^ (-(2 / 3 : ℝ))) ^ (3 : ℕ) = (N : ℝ) ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  rw [h3, Real.rpow_neg hN0.le, Real.rpow_two]
  exact inv_mul_cancel₀ (pow_ne_zero 2 hN0.ne')

lemma Fbound_mono {C M2 a c c' : ℝ} (hC : 0 ≤ C) (hM2 : 0 ≤ M2) (hcc : c ≤ c') :
    Fbound C M2 a c ≤ Fbound C M2 a c' := by
  unfold Fbound
  have hs : Real.sqrt c ≤ Real.sqrt c' := Real.sqrt_le_sqrt hcc
  nlinarith [mul_le_mul_of_nonneg_left hs hC, mul_le_mul_of_nonneg_left hcc hM2]

/-- The estimate for a coupling `cp` of `(λ, μ)`, at the scale `δ = √c + N^{−2/3}`, where
`c = ∫|x − y| dcp`. The right-hand side is `Fbound`. -/
lemma coupling_bound {f : ℝ → ℝ} (hf : Good f) {κ N : ℝ} (hκ : κ ≠ 0) (hN : 1 ≤ N)
    {lam mu : Measure ℝ} [IsProbabilityMeasure lam] [IsProbabilityMeasure mu]
    {cp : Measure (ℝ × ℝ)} (hcp : IsCoupling cp lam mu)
    (hint : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) cp)
    {Mρ : ℝ}
    (hmu2 : ∀ δ : ℝ, 0 < δ → ∫ p, tent δ (p.1 - p.2) ∂(mu.prod mu) ≤ 4 * Mρ * δ) :
    |(∫ p, KN κ N f p.1 p.2 ∂(lam.prod lam)) - ∫ p, Kf f p.1 p.2 ∂(mu.prod mu)|
      ≤ Fbound ((8 * Mρ + 4 + κ ^ 2 / 3) * supAbs (deriv f)) (supAbs (deriv (deriv f)))
          ((N : ℝ) ^ (-(2 / 3 : ℝ))) (∫ p, |p.1 - p.2| ∂cp) := by
  have hN0 : 0 < N := by linarith
  have hN0' : N ≠ 0 := hN0.ne'
  have hc0 : 0 ≤ ∫ p, |p.1 - p.2| ∂cp := integral_nonneg fun p => abs_nonneg _
  have ha0 : 0 < (N : ℝ) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hδpos : 0 < Real.sqrt (∫ p, |p.1 - p.2| ∂cp) + (N : ℝ) ^ (-(2 / 3 : ℝ)) := by
    have := Real.sqrt_nonneg (∫ p, |p.1 - p.2| ∂cp)
    linarith
  have hstep := step1 hf hκ hN0' hcp hint hmu2 hδpos
  have hcube := cube_identity hN
  unfold Fbound
  set c := ∫ p, |p.1 - p.2| ∂cp with hc_def
  set a := (N : ℝ) ^ (-(2 / 3 : ℝ)) with ha_def
  set s := Real.sqrt c with hs_def
  set M1 := supAbs (deriv f) with hM1_def
  set M2 := supAbs (deriv (deriv f)) with hM2_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg c
  have hsc : s * s = c := Real.mul_self_sqrt hc0
  have hM1 : 0 ≤ M1 := supAbs_deriv_nonneg hf
  have hc_s : c * (1 / (s + a)) ≤ s := by
    rw [mul_one_div, div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hs0 ha0.le]
  have hA1 : 1 ≤ a * N ^ 2 * (s + a) ^ 2 := by
    have h1 : a ^ 2 ≤ (s + a) ^ 2 := by nlinarith [mul_nonneg hs0 ha0.le, sq_nonneg s]
    have h2 : a * N ^ 2 * a ^ 2 = 1 := by linear_combination hcube
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg ha0.le (sq_nonneg N))]
  have hk : κ ^ 2 / (3 * N ^ 2 * (s + a) ^ 2) ≤ κ ^ 2 * a / 3 := by
    rw [div_le_iff₀ (mul_pos (mul_pos (by norm_num) (pow_pos hN0 2)) (pow_pos (by linarith) 2))]
    nlinarith [mul_nonneg (sq_nonneg κ) (sub_nonneg.mpr hA1)]
  have hterm1 : 2 * M1 * (4 * Mρ * (s + a) + 2 * (1 / (s + a)) * c)
      ≤ 8 * M1 * Mρ * (s + a) + 4 * M1 * s := by
    have e : 2 * M1 * (4 * Mρ * (s + a) + 2 * (1 / (s + a)) * c)
        = 8 * M1 * Mρ * (s + a) + 4 * M1 * (c * (1 / (s + a))) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hc_s (by linarith : (0:ℝ) ≤ 4 * M1)
    linarith
  have hterm2 : M1 * (κ ^ 2 / (3 * N ^ 2 * (s + a) ^ 2)) ≤ M1 * (κ ^ 2 * a / 3) :=
    mul_le_mul_of_nonneg_left hk hM1
  have hfin : 8 * M1 * Mρ * (s + a) + 4 * M1 * s + M1 * (κ ^ 2 * a / 3)
      ≤ (8 * Mρ + 4 + κ ^ 2 / 3) * M1 * (s + a) := by
    nlinarith [mul_nonneg hM1 ha0.le, mul_nonneg hM1 (mul_nonneg (sq_nonneg κ) hs0)]
  linarith [hstep, hterm1, hterm2, hfin]

/-- A continuous function bounded by its value at `w + ε`, for all small `ε > 0`, is bounded at `w`. -/
lemma limit_step {F : ℝ → ℝ} (hcont : Continuous F) {w X : ℝ}
    (key : ∀ ε : ℝ, 0 < ε → X ≤ F (w + ε)) : X ≤ F w := by
  have hc : Continuous (fun ε : ℝ => F (w + ε)) := hcont.comp (continuous_const.add continuous_id)
  have htend : Tendsto (fun ε : ℝ => F (w + ε)) (𝓝[>] 0) (𝓝 (F w)) := by
    have h : Tendsto (fun ε : ℝ => F (w + ε)) (𝓝[>] (0:ℝ)) (𝓝 (F (w + 0))) :=
      (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa using h
  have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), X ≤ F (w + ε) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact key ε hε
  exact ge_of_tendsto htend hev

/-- **Main statement of `lem:E-kernel` (R-2AF76530).** With `λ = N⁻¹ Σ_j δ_{q_j}`, `μ = ρ(t) dt` a
probability measure with `0 ≤ ρ ≤ Mρ`, `f ∈ C_c²(ℝ)`, and `w = W_1(λ, μ) ∈ [0,1]`,
`|∬K_N^f dλ⊗² − ∬K^f dμ⊗²| ≤ (8Mρ+4+κ²/3) ‖f'‖_∞ (√w + N^{−2/3}) + 2‖f''‖_∞ w`. -/
theorem E_kernel_bound (κ Mρ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (q : Fin N → ℝ)
    (ρ : ℝ → ℝ) (hρ_meas : Measurable ρ) (hρ_nonneg : ∀ t, 0 ≤ ρ t)
    (hρ_bdd : ∀ t, ρ t ≤ Mρ) (hμ : IsProbabilityMeasure (densityMeasure ρ))
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hW : W1 (empirical N q) (densityMeasure ρ) = ENNReal.ofReal w) :
    |(∫ p, KN κ (N : ℝ) f p.1 p.2 ∂((empirical N q).prod (empirical N q)))
        - ∫ p, Kf f p.1 p.2 ∂((densityMeasure ρ).prod (densityMeasure ρ))|
      ≤ (8 * Mρ + 4 + κ ^ 2 / 3) * supAbs (deriv f) * (Real.sqrt w + (N : ℝ) ^ (-(2 / 3 : ℝ)))
        + 2 * supAbs (deriv (deriv f)) * w := by
  have hG : Good f := ⟨hf, hfc⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have : IsProbabilityMeasure (empirical N q) := empirical_isProbabilityMeasure hN q
  have := hμ
  have hMρ0 : 0 ≤ Mρ := (hρ_nonneg 0).trans (hρ_bdd 0)
  have hκne : κ ≠ 0 := hκ.ne'
  have hmu2 : ∀ δ : ℝ, 0 < δ →
      ∫ p, tent δ (p.1 - p.2) ∂((densityMeasure ρ).prod (densityMeasure ρ)) ≤ 4 * Mρ * δ :=
    fun δ hδ => density_tent_bound hρ_nonneg hρ_bdd hδ
  have hM1 : 0 ≤ supAbs (deriv f) := supAbs_deriv_nonneg hG
  have hM2 : 0 ≤ supAbs (deriv (deriv f)) := supAbs_deriv2_nonneg hG
  have hC0 : 0 ≤ (8 * Mρ + 4 + κ ^ 2 / 3) * supAbs (deriv f) :=
    mul_nonneg (by nlinarith [sq_nonneg κ]) hM1
  have key : ∀ ε : ℝ, 0 < ε →
      |(∫ p, KN κ (N : ℝ) f p.1 p.2 ∂((empirical N q).prod (empirical N q)))
        - ∫ p, Kf f p.1 p.2 ∂((densityMeasure ρ).prod (densityMeasure ρ))|
      ≤ Fbound ((8 * Mρ + 4 + κ ^ 2 / 3) * supAbs (deriv f)) (supAbs (deriv (deriv f)))
          ((N : ℝ) ^ (-(2 / 3 : ℝ))) (w + ε) := by
    intro ε hε
    have hlt : W1 (empirical N q) (densityMeasure ρ) < ENNReal.ofReal (w + ε) := by
      rw [hW]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    unfold W1 at hlt
    obtain ⟨cp, hcp1⟩ := iInf_lt_iff.mp hlt
    obtain ⟨hcpc, hlt2⟩ := iInf_lt_iff.mp hcp1
    have hcpP : IsProbabilityMeasure cp := hcpc.1
    have := hcpP
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => |p.1 - p.2|) cp :=
      (continuous_abs.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable
    have hfin : ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂cp < ⊤ := hlt2.trans ENNReal.ofReal_lt_top
    have hint : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) cp :=
      ⟨hmeas, (hasFiniteIntegral_iff_ofReal
        (ae_of_all _ fun p : ℝ × ℝ => abs_nonneg (p.1 - p.2))).mpr hfin⟩
    have hc_eq : ∫ p, |p.1 - p.2| ∂cp = (∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂cp).toReal :=
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun p => abs_nonneg _) hmeas
    have hc_le : ∫ p, |p.1 - p.2| ∂cp ≤ w + ε := by
      rw [hc_eq]
      exact ENNReal.toReal_le_of_le_ofReal (by linarith) hlt2.le
    have hb := coupling_bound hG hκne hN1 hcpc hint hmu2
    exact hb.trans (Fbound_mono hC0 hM2 hc_le)
  have hcont : Continuous (fun x : ℝ => Fbound ((8 * Mρ + 4 + κ ^ 2 / 3) * supAbs (deriv f))
      (supAbs (deriv (deriv f))) ((N : ℝ) ^ (-(2 / 3 : ℝ))) x) := by
    unfold Fbound
    fun_prop
  exact limit_step hcont key

/-- Existential form: the constant depends only on `Mρ` and `κ`. -/
theorem E_kernel_bound_exists (κ Mρ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, ∀ (N : ℕ), 1 ≤ N → ∀ (q : Fin N → ℝ) (ρ : ℝ → ℝ), Measurable ρ →
      (∀ t, 0 ≤ ρ t) → (∀ t, ρ t ≤ Mρ) → IsProbabilityMeasure (densityMeasure ρ) →
      ∀ (f : ℝ → ℝ), ContDiff ℝ 2 f → HasCompactSupport f →
      ∀ w : ℝ, 0 ≤ w → w ≤ 1 → W1 (empirical N q) (densityMeasure ρ) = ENNReal.ofReal w →
      |(∫ p, KN κ (N : ℝ) f p.1 p.2 ∂((empirical N q).prod (empirical N q)))
          - ∫ p, Kf f p.1 p.2 ∂((densityMeasure ρ).prod (densityMeasure ρ))|
        ≤ C * supAbs (deriv f) * (Real.sqrt w + (N : ℝ) ^ (-(2 / 3 : ℝ)))
          + 2 * supAbs (deriv (deriv f)) * w := by
  refine ⟨8 * Mρ + 4 + κ ^ 2 / 3, ?_⟩
  intro N hN q ρ hρm hρ0 hρb hμ f hf hfc w hw0 hw1 hW
  exact E_kernel_bound κ Mρ hκ N hN q ρ hρm hρ0 hρb hμ f hf hfc w hw0 hw1 hW

/-! ## 9. Axiom audit (`#print axioms`) -/

#print axioms QuantumNLS.EKernelBound.E_kernel_bound
#print axioms QuantumNLS.EKernelBound.E_kernel_bound_exists
#print axioms QuantumNLS.EKernelBound.coupling_bound
#print axioms QuantumNLS.EKernelBound.step1
#print axioms QuantumNLS.EKernelBound.two_coupling_bound
#print axioms QuantumNLS.EKernelBound.density_tent_bound
#print axioms QuantumNLS.EKernelBound.KN_eq_Kf_mul
#print axioms QuantumNLS.EKernelBound.abs_KN_sub_Kf_le
#print axioms QuantumNLS.EKernelBound.abs_KN_sub_Kf_le_tent
#print axioms QuantumNLS.EKernelBound.Kf_mul_sub
#print axioms QuantumNLS.EKernelBound.Kf_lip
#print axioms QuantumNLS.EKernelBound.arctan_lower
#print axioms QuantumNLS.EKernelBound.arctan_div_bounds
#print axioms QuantumNLS.EKernelBound.tent_lip
#print axioms QuantumNLS.EKernelBound.empirical_isProbabilityMeasure
#print axioms QuantumNLS.EKernelBound.cube_identity
#print axioms QuantumNLS.EKernelBound.limit_step

end QuantumNLS.EKernelBound
