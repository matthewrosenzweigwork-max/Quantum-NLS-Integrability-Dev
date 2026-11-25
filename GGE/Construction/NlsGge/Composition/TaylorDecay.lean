import NlsGge.Composition.FourierDecay
import NlsGge.Composition.SeriesBounds
import NlsGge.Composition.LocalBounds
import NlsGge.Composition.TrigCurve

/-!
# Exponential decay of the Fourier coefficients of the Taylor coefficients along a trigonometric
curve

Source: `paper/v2.tex` lines 1464-1473 (`B_k(θ) = D^k F(p(θ)) / k!`, Fourier norms bounded by a
strip constant independent of `k`).  Documented departure: instead of a complex strip we use the
real power-series route (composition of the Cauchy-bounded series of `D^k f` with the entire series
of the trigonometric curve) followed by the integration-by-parts decay lemma
`fourierCoeff_norm_le_of_iteratedDeriv_infty`.

* `taylorCoeff_fourier_decay`
* `taylorCoeff_continuous`
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.Composition

open FormalMultilinearSeries

section Generic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A power series of `f` on a ball yields a power series of every iterated derivative. -/
lemma hasFPowerSeriesAt_iteratedFDeriv {f : E → F} {p : FormalMultilinearSeries ℝ E F} {y : E}
    {r : ENNReal} (h : HasFPowerSeriesOnBall f p y r) (k : ℕ) :
    HasFPowerSeriesAt (iteratedFDeriv ℝ k f) (p.iteratedFDerivSeries k) y := by
  have hs : IsOpen (Metric.eball y r) := Metric.isOpen_eball
  have hy : y ∈ Metric.eball y r := Metric.mem_eball_self h.r_pos
  have h1 : HasFPowerSeriesWithinOnBall f p (Metric.eball y r) y r :=
    h.hasFPowerSeriesWithinOnBall
  have hanal : AnalyticOn ℝ f (Metric.eball y r) := fun z hz =>
    (h.analyticAt_of_mem hz).analyticWithinAt
  have h2 := h1.iteratedFDerivWithin hanal k hs.uniqueDiffOn hy
  have h3 : HasFPowerSeriesWithinOnBall (iteratedFDeriv ℝ k f) (p.iteratedFDerivSeries k)
      (Metric.eball y r) y r := by
    refine h2.congr' (fun z hz => ?_)
    rw [Set.insert_eq_of_mem hy] at hz
    exact (iteratedFDerivWithin_of_isOpen k hs hz.1).symm
  exact (hasFPowerSeriesWithinAt_iff_of_nhds _ _ (hs.mem_nhds hy)).1 ⟨r, h3⟩

omit [CompleteSpace F] in
/-- Cauchy-type bound for the normalised coefficients of the series of `D^k f / k!`. -/
lemma norm_smul_iteratedFDerivSeries_le {p : FormalMultilinearSeries ℝ E F} {M ρ : ℝ}
    (hp : ∀ n, ‖p n‖ ≤ M * ρ⁻¹ ^ n) (k j : ℕ) :
    ‖(((k.factorial : ℝ)⁻¹) • p.iteratedFDerivSeries k) j‖
      ≤ (M * (2 / ρ) ^ k) * (ρ / 2)⁻¹ ^ j := by
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hj : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have h1 := norm_iteratedFDerivSeries_le p k j
  have hchoose : (((j + k).factorial : ℝ) / (j.factorial : ℝ)) * (k.factorial : ℝ)⁻¹
      = ((j + k).choose k : ℝ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial j k
    have h' : (((j + k).choose k : ℕ) : ℝ) * (j.factorial : ℝ) * (k.factorial : ℝ)
        = ((j + k).factorial : ℝ) := by exact_mod_cast this
    rw [← h']
    field_simp
  have hch : ((j + k).choose k : ℝ) ≤ 2 ^ (j + k) := by
    exact_mod_cast Nat.choose_le_two_pow (j + k) k
  have hpjk := hp (j + k)
  show ‖(k.factorial : ℝ)⁻¹ • p.iteratedFDerivSeries k j‖ ≤ _
  have hsm := @NormedSpace.norm_smul_le ℝ _ _ _
    (inferInstance : NormedSpace ℝ (E [×j]→L[ℝ] E [×k]→L[ℝ] F))
    ((k.factorial : ℝ)⁻¹) (p.iteratedFDerivSeries k j)
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hk)] at hsm
  refine hsm.trans ?_
  calc (k.factorial : ℝ)⁻¹ * ‖p.iteratedFDerivSeries k j‖
      ≤ (k.factorial : ℝ)⁻¹ * ((((j + k).factorial : ℝ) / (j.factorial : ℝ)) * ‖p (j + k)‖) := by
        gcongr
    _ = ((j + k).choose k : ℝ) * ‖p (j + k)‖ := by
        rw [← hchoose]; ring
    _ ≤ 2 ^ (j + k) * (M * ρ⁻¹ ^ (j + k)) :=
        mul_le_mul hch hpjk (norm_nonneg _) (by positivity)
    _ = (M * (2 / ρ) ^ k) * (ρ / 2)⁻¹ ^ j := by
        rw [inv_div, div_eq_mul_inv 2 ρ, mul_pow, mul_pow, pow_add, pow_add, inv_pow]
        ring

end Generic

section Main

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]

/-- The constant bounding the coefficients of the trigonometric curve (`σ = 1`). -/
def trigConst (S : Finset ℤ) (v : ℤ → X) : ℝ :=
  (∑ n ∈ S, ‖v n‖) * Real.exp (2 * Real.pi * ∑ n ∈ S, |(n : ℝ)|)

omit [NormedSpace ℂ X] [CompleteSpace X] in
lemma trigConst_nonneg (S : Finset ℤ) (v : ℤ → X) : 0 ≤ trigConst S v :=
  mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Real.exp_pos _).le

/-- Local series of `t ↦ D^k f (γ t) / k!` at `t₀`, with `k`-dependence only through
`M (2/ρ)^k`. -/
lemma taylor_series_at {f : X → Y} {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M)
    {S : Finset ℤ} {v : ℤ → X} {t₀ : ℝ} {p : FormalMultilinearSeries ℝ X Y}
    (hp : HasFPowerSeriesOnBall f p (trigCurve S v t₀) (ENNReal.ofReal ρ))
    (hb : ∀ n, ‖p n‖ ≤ M * ρ⁻¹ ^ n) (k : ℕ) :
    ∃ Q : FormalMultilinearSeries ℝ ℝ (X [×k]→L[ℝ] Y),
      HasFPowerSeriesAt
        (fun t : ℝ => ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k f (trigCurve S v t)) Q t₀ ∧
      ∀ m, ‖Q m‖ ≤ (M * (2 / ρ) ^ k) * (2 * max 1 (trigConst S v / (ρ / 2))) ^ m := by
  set N : ℝ := ∑ n ∈ S, |(n : ℝ)| with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hNS : ∀ n ∈ S, |(n : ℝ)| ≤ N := fun n hn =>
    Finset.single_le_sum (f := fun n : ℤ => |(n : ℝ)|) (fun _ _ => abs_nonneg _) hn
  obtain ⟨P, hP, hPb⟩ := trigCurve_hasFPowerSeries S v t₀ N hN0 hNS
  have hq := (hasFPowerSeriesAt_iteratedFDeriv hp k).const_smul (c := ((k.factorial : ℝ)⁻¹))
  have hcomp := hq.comp hP.hasFPowerSeriesAt
  refine ⟨_, hcomp, fun m => ?_⟩
  have hbd := norm_comp_le (((k.factorial : ℝ)⁻¹) • (p.iteratedFDerivSeries k)) P
    (M := M * (2 / ρ) ^ k) (R := ρ / 2) (L := trigConst S v) (σ := 1)
    (mul_nonneg hM (pow_nonneg (by positivity) _)) (by positivity) (trigConst_nonneg S v)
    one_pos (fun j => norm_smul_iteratedFDerivSeries_le hb k j) ?_ m
  · simpa using hbd
  · intro m _
    calc ‖P m‖ ≤ (∑ n ∈ S, ‖v n‖) * (2 * Real.pi * N) ^ m / m.factorial := hPb m
      _ = (∑ n ∈ S, ‖v n‖) * ((2 * Real.pi * N) ^ m / m.factorial) := by rw [mul_div_assoc]
      _ ≤ (∑ n ∈ S, ‖v n‖) * Real.exp (2 * Real.pi * N) :=
          mul_le_mul_of_nonneg_left (Real.pow_div_factorial_le_exp _ (by positivity) m)
            (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ = trigConst S v * 1⁻¹ ^ m := by simp [trigConst, hN]

theorem taylorCoeff_fourier_decay {f : X → Y} {K : Set X} {δ ρ M : ℝ} (_hδ : 0 < δ) (hρ : 0 < ρ)
    (hM : 0 ≤ M)
    (hdata : ∀ y ∈ Metric.thickening δ K, ∃ p : FormalMultilinearSeries ℝ X Y,
        HasFPowerSeriesOnBall f p y (ENNReal.ofReal ρ) ∧ ∀ n, ‖p n‖ ≤ M * ρ⁻¹ ^ n)
    (S : Finset ℤ) (v : ℤ → X)
    (hγ : ∀ θ : AddCircle (1:ℝ), (∑ n ∈ S, fourier n θ • v n) ∈ Metric.thickening δ K) :
    ∃ s : ℝ, 0 < s ∧ ∀ (k : ℕ) (n : ℤ),
      ‖fourierCoeff (fun θ : AddCircle (1:ℝ) =>
          ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f (∑ m ∈ S, fourier m θ • v m))) n‖
        ≤ 2 * M * (2 / ρ) ^ k * Real.exp (-(Real.pi * s) * |(n:ℝ)|) := by
  set s₀ : ℝ := (2 * max 1 (trigConst S v / (ρ / 2)))⁻¹ with hs₀
  have hmax : 0 < max 1 (trigConst S v / (ρ / 2)) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hs₀pos : 0 < s₀ := by positivity
  refine ⟨s₀, hs₀pos, fun k n => ?_⟩
  -- the curve, as a function on `ℝ`
  set U : ℝ → (X [×k]→L[ℝ] Y) :=
    fun t => ((k.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ k f (trigCurve S v t) with hU
  have hloc : ∀ t : ℝ, ∃ Q : FormalMultilinearSeries ℝ ℝ (X [×k]→L[ℝ] Y),
      HasFPowerSeriesAt U Q t ∧
      ∀ m, ‖Q m‖ ≤ (M * (2 / ρ) ^ k) * s₀⁻¹ ^ m := by
    intro t
    obtain ⟨p, hp, hb⟩ := hdata _ (hγ (t : AddCircle (1:ℝ)))
    obtain ⟨Q, hQ, hQb⟩ := taylor_series_at hρ hM (t₀ := t) hp hb k
    exact ⟨Q, hQ, by simpa [hs₀] using hQb⟩
  have hsmooth : ∀ m : ℕ, ContDiff ℝ m U := fun m =>
    contDiff_iff_contDiffAt.2 fun t =>
      (hloc t).choose_spec.1.analyticAt.contDiffAt
  have hK : ∀ (m : ℕ) (x : ℝ),
      ‖iteratedDeriv m U x‖ ≤ (M * (2 / ρ) ^ k) * m.factorial / s₀ ^ m := by
    intro m x
    obtain ⟨Q, hQ, hQb⟩ := hloc x
    obtain ⟨r, hr⟩ := hQ
    have h1 := norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall hr m
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at h1
    refine h1.trans ?_
    calc (m.factorial : ℝ) * ‖Q m‖
        ≤ (m.factorial : ℝ) * ((M * (2 / ρ) ^ k) * s₀⁻¹ ^ m) := by gcongr; exact hQb m
      _ = (M * (2 / ρ) ^ k) * m.factorial / s₀ ^ m := by
          rw [inv_pow]; field_simp
  have key := fourierCoeff_norm_le_of_iteratedDeriv_infty
    (E := X [×k]→L[ℝ] Y)
    (fun θ : AddCircle (1:ℝ) =>
      ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f (∑ m ∈ S, fourier m θ • v m)))
    hsmooth hs₀pos hK n
  calc _ ≤ 2 * (M * (2 / ρ) ^ k) * Real.exp (-(Real.pi * s₀) * |(n:ℝ)|) := key
    _ = _ := by ring

omit [CompleteSpace X] in
theorem taylorCoeff_continuous {f : X → Y} {K : Set X} {δ ρ M : ℝ}
    (hdata : ∀ y ∈ Metric.thickening δ K, ∃ p : FormalMultilinearSeries ℝ X Y,
        HasFPowerSeriesOnBall f p y (ENNReal.ofReal ρ) ∧ ∀ n, ‖p n‖ ≤ M * ρ⁻¹ ^ n)
    (S : Finset ℤ) (v : ℤ → X)
    (hγ : ∀ θ : AddCircle (1:ℝ), (∑ n ∈ S, fourier n θ • v n) ∈ Metric.thickening δ K)
    (k : ℕ) :
    Continuous (fun θ : AddCircle (1:ℝ) =>
      ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f (∑ m ∈ S, fourier m θ • v m))) := by
  have hγc : Continuous (fun θ : AddCircle (1:ℝ) => ∑ n ∈ S, fourier n θ • v n) :=
    continuous_finsetSum _ fun n _ => (fourier n).continuous.smul continuous_const
  have hD : Continuous (fun θ : AddCircle (1:ℝ) =>
      iteratedFDeriv ℝ k f (∑ m ∈ S, fourier m θ • v m)) := by
    refine continuous_iff_continuousAt.2 fun θ => ?_
    obtain ⟨p, hp, _⟩ := hdata _ (hγ θ)
    have h1 : ContinuousAt (iteratedFDeriv ℝ k f) (∑ n ∈ S, fourier n θ • v n) :=
      (hasFPowerSeriesAt_iteratedFDeriv hp k).continuousAt
    exact ContinuousAt.comp (f := fun θ : AddCircle (1:ℝ) => ∑ n ∈ S, fourier n θ • v n)
      h1 hγc.continuousAt
  exact hD.const_smul ((k.factorial : ℝ)⁻¹)

end Main

end NlsGge.Composition
