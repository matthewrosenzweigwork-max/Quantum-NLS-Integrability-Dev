import Mathlib
import QuantumNLS.Local007Final
import QuantumNLS.Local007Zeta

/-! LOCAL-007 `prop:reset-exact-factor`: the single named theorem `reset_exact_factor`.

Printed statement (`exact_action_factor.tex:25-48`), with the hypotheses of the printed LOCAL-003 reduction
(`0 < L`, `0 < κ`, a contour radius `0 < r < 2π/L`):

On one sufficiently small open ball `ball 0 ρ` of `L²(𝕋_L)` there are the LOCAL-003 reduction data
`(a_n, b_n)` (`Pkg`: the polar-normalized Riesz reduction `B_n = [[a_n, conj b_n],[b_n, a_n]]` with its
eigenvalue structure and the estimates of `g_n = √L/(2i√κ) b_n`) and a real-analytic map
`rr : L² → ℓ∞(ℤ;ℝ)` with `I_n(u) = |g_n(u)|² rr_n(u)` (`I_n` = the indexed mass of R-950BFB30), `1/2 < rr_n < 3/2`,
`rr(0) = 1`, `‖rr(u) - 1‖_∞ ≤ C‖u‖²`, `‖D rr(u)‖ ≤ C‖u‖`;
and if in addition the full map `g` is real analytic from the ball into `ℓ²` with `‖Dg(u) - 𝓕‖ ≤ C_g‖u‖²`
(`𝓕 = ` Fourier coefficient map `u ↦ (û(n))`), then `ζ_n = g_n √rr_n` is real analytic into `ℓ²`,
`‖Dζ(u) - 𝓕‖ ≤ C_ζ‖u‖²` and `‖ζ(u)‖² = ‖u‖²`. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open MeasureTheory Set Metric Filter Topology BoundedContinuousFunction
namespace QuantumNLS.Local007Statement
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.Local007Final (gcoef Pkg)
open QuantumNLS.Local007Mul (mulCLM Seq)
variable {L κ r : ℝ} [Fact (0 < L)]

/-- The Fourier coefficient map `𝓕 u = (û(n))_n` as a bounded real-linear map `L²(𝕋_L) → ℓ²(ℤ)`. -/
def Fmap : L2T L →L[ℝ] lp (fun _ : ℤ => ℂ) 2 :=
  (((QuantumNLS.Fourier.fourierL2 L).toLinearIsometry.toContinuousLinearMap).restrictScalars ℝ)

theorem Fmap_apply (u : L2T L) (n : ℤ) :
    Fmap u n = QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n :=
  QuantumNLS.Fourier.fourierL2_apply L u n

theorem norm_Fmap (h : L2T L) : ‖Fmap h‖ ≤ ‖h‖ :=
  ((QuantumNLS.Fourier.fourierL2 L).norm_map h).le

theorem analyticAt_sqrt_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (h1 : f x = 1) : AnalyticAt ℝ (fun y => Real.sqrt (f y)) x := by
  have hg : AnalyticAt ℂ (fun z : ℂ => (1 + z) ^ (1 / 2 : ℂ)) 0 :=
    Complex.one_add_cpow_hasFPowerSeriesAt_zero.analyticAt
  have hgR : AnalyticAt ℝ (fun z : ℂ => (1 + z) ^ (1 / 2 : ℂ)) 0 := hg.restrictScalars
  have hf' : AnalyticAt ℝ (fun y => ((f y - 1 : ℝ) : ℂ)) x :=
    (Complex.ofRealCLM.analyticAt _).comp (hf.sub analyticAt_const)
  have hcomp := hgR.comp_of_eq hf' (by simp [h1])
  have hre := (Complex.reCLM.analyticAt _).comp hcomp
  refine hre.congr ?_
  have hpos : ∀ᶠ y in 𝓝 x, 0 < f y := hf.continuousAt.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hpos] with y hy
  show ((1 + ((f y - 1 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)).re = Real.sqrt (f y)
  have e : (1 + ((f y - 1 : ℝ) : ℂ)) = ((f y : ℝ) : ℂ) := by push_cast; ring
  rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow hy.le,
    Complex.ofReal_re, Real.sqrt_eq_rpow]

theorem pkg_b_zero (hκ : 0 < κ) {ρ C : ℝ} (hρ : 0 < ρ) {n : ℤ} {a : L2T L → ℝ} {b : L2T L → ℂ}
    (hp : Pkg L κ r ρ C n a b) : b 0 = 0 := by
  have h7 := hp.2.2.2.2.2.2.1 0 (mem_ball_self hρ)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at h7
  have hc0 : QuantumNLS.Fourier.coeff L ((0 : L2T L) : AddCircle L → ℂ) n = 0 := by
    rw [← QuantumNLS.Fourier.fourierL2_apply]; simp
  have : gcoef L κ * b 0 = 0 := by
    have := norm_le_zero_iff.1 h7
    rw [hc0] at this; simpa using this
  have hg : gcoef L κ ≠ 0 := by
    intro h
    have := QuantumNLS.Local007Final.norm_gcoef_sq (L := L) hκ
    rw [h, norm_zero] at this
    have : 0 < L / (4 * κ) := by have := (Fact.out : 0 < L); positivity
    norm_num at *; linarith
  exact (mul_eq_zero.1 this).resolve_left hg

theorem abs_sqrt_sub_one_le {x : ℝ} (hx : 0 ≤ x) : |Real.sqrt x - 1| ≤ |x - 1| := by
  have h := Real.sq_sqrt hx
  have h0 := Real.sqrt_nonneg x
  set y := Real.sqrt x
  rw [← h]
  have : y ^ 2 - 1 = (y - 1) * (y + 1) := by ring
  rw [this, abs_mul, abs_of_pos (by linarith : 0 < y + 1)]
  nlinarith [abs_nonneg (y - 1)]

theorem reset_exact_factor (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ (a : ℤ → L2T L → ℝ) (b : ℤ → L2T L → ℂ) (rr : L2T L → (ℤ →ᵇ ℝ)),
        (∀ n, Pkg L κ r ρ C n (a n) (b n)) ∧ AnalyticOnNhd ℝ rr (ball (0 : L2T L) ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
          (QuantumNLS.RootIndexedMasses.masses hκ u).1 n = ‖gcoef L κ * b n u‖ ^ 2 * rr u n) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, 1 / 2 < rr u n ∧ rr u n < 3 / 2) ∧ rr 0 = 1 ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ‖rr u - 1‖ ≤ C * ‖u‖ ^ 2) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ‖fderiv ℝ rr u‖ ≤ C * ‖u‖) ∧
        (∀ (G : L2T L → lp (fun _ : ℤ => ℂ) 2) (Cg : ℝ), 0 ≤ Cg →
          (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, G u n = gcoef L κ * b n u) →
          AnalyticOnNhd ℝ G (ball (0 : L2T L) ρ) →
          (∀ u ∈ ball (0 : L2T L) ρ, ‖fderiv ℝ G u - Fmap‖ ≤ Cg * ‖u‖ ^ 2) →
          ∃ (Z : L2T L → lp (fun _ : ℤ => ℂ) 2) (Cz : ℝ), 0 ≤ Cz ∧
            (∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
              Z u n = gcoef L κ * b n u * ((Real.sqrt (rr u n) : ℝ) : ℂ)) ∧
            AnalyticOnNhd ℝ Z (ball (0 : L2T L) ρ) ∧
            (∀ u ∈ ball (0 : L2T L) ρ, ‖fderiv ℝ Z u - Fmap‖ ≤ Cz * ‖u‖ ^ 2) ∧
            (∀ u ∈ ball (0 : L2T L) ρ, ‖Z u‖ ^ 2 = ‖u‖ ^ 2)) := by
  obtain ⟨ρ0, hρ0, C, hC, a, b, rr, hpk, hrr, hmass, hbd, hrr0, hrr1, hrr2, hcov⟩ :=
    QuantumNLS.Local007Final.reset_exact_factor_main (L := L) hκ hr hr2
  let T : ℤ → L2T L →L[ℝ] L2T L := fun n =>
    ((QuantumNLS.Local007Gauge.boostLI (L := L) (-n)).toContinuousLinearMap).restrictScalars ℝ
  have hnorm : ∀ n (u : L2T L), ‖T n u‖ = ‖u‖ := fun n u =>
    (QuantumNLS.Local007Gauge.boostLI (L := L) (-n)).norm_map u
  have hT : ∀ n u, ‖T n u‖ ≤ ‖u‖ := fun n u => (hnorm n u).le
  have hR0a : AnalyticAt ℝ (fun x : L2T L => (rr x) 0) 0 := by
    have h := ((BoundedContinuousFunction.evalCLM ℝ (0 : ℤ)).analyticAt (rr 0)).comp
      (hrr 0 (mem_ball_self hρ0))
    exact h
  have hrr00 : (rr 0) 0 = 1 := by rw [hrr0]; rfl
  have hR'a : AnalyticAt ℝ (fun x : L2T L => Real.sqrt ((rr x) 0)) 0 := analyticAt_sqrt_one hR0a hrr00
  obtain ⟨ρs, hρs, ss, hss, hssv⟩ := QuantumNLS.Local007Lp.lp_lift T hT hR'a
  set ρ : ℝ := min ρ0 ρs with hρdef
  have hρpos : 0 < ρ := lt_min hρ0 hρs
  have hs0 : ball (0 : L2T L) ρ ⊆ ball (0 : L2T L) ρ0 := ball_subset_ball (min_le_left _ _)
  have hs1 : ball (0 : L2T L) ρ ⊆ ball (0 : L2T L) ρs := ball_subset_ball (min_le_right _ _)
  refine ⟨ρ, hρpos, C, hC, a, b, rr, fun n => (hpk n).mono (min_le_left _ _) le_rfl, hrr.mono hs0,
    fun u hu => hmass u (hs0 hu), fun u hu => hbd u (hs0 hu), hrr0, fun u hu => hrr1 u (hs0 hu),
    fun u hu => hrr2 u (hs0 hu), ?_⟩
  intro G Cg hCg hGv hGa hGd
  have hssn : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ, ss u n = Real.sqrt (rr u n) := by
    intro u hu n
    rw [hssv u (hs1 hu) n]
    show Real.sqrt ((rr (QuantumNLS.RootMassBoostSymbol.boost (-n) u)) 0) = _
    rw [← hcov u (hs0 hu) n]
  have hss1 : ∀ u ∈ ball (0 : L2T L) ρ, ‖ss u - 1‖ ≤ C * ‖u‖ ^ 2 := by
    intro u hu
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun n => ?_
    change ‖ss u n - 1‖ ≤ _
    rw [hssn u hu n, Real.norm_eq_abs]
    have hpos : 0 ≤ rr u n := by have := (hbd u (hs0 hu) n).1; linarith
    refine (abs_sqrt_sub_one_le hpos).trans ?_
    have h1 := (rr u - 1).norm_coe_le_norm n
    change ‖rr u n - 1‖ ≤ ‖rr u - 1‖ at h1
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hrr1 u (hs0 hu))
  have hss2 : ∀ u ∈ ball (0 : L2T L) ρ, ‖fderiv ℝ ss u‖ ≤ C * ‖u‖ := by
    intro u hu
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun n => ?_
    have hx : T n u ∈ ball (0 : L2T L) ρ0 := by
      rw [mem_ball_zero_iff, hnorm]; exact hs0 hu |> fun h => by simpa using h
    have hpos : 0 < (rr (T n u)) 0 := by have := (hbd (T n u) hx 0).1; linarith
    have hf : DifferentiableAt ℝ (fun x : L2T L => (rr x) 0) (T n u) := by
      have h := ((BoundedContinuousFunction.evalCLM ℝ (0 : ℤ)).differentiableAt (x := rr (T n u))).comp
        (T n u) ((hrr _ hx).differentiableAt)
      exact h
    have hRd : DifferentiableAt ℝ (fun x : L2T L => Real.sqrt ((rr x) 0)) (T n u) := hf.sqrt hpos.ne'
    have hder := QuantumNLS.Local007Lp.lp_deriv T hT hss hssv (hs1 hu) n hRd h
    rw [hder, Real.norm_eq_abs]
    have hH : HasFDerivAt (fun x : L2T L => (rr x) 0)
        ((BoundedContinuousFunction.evalCLM ℝ (0 : ℤ)).comp (fderiv ℝ rr (T n u))) (T n u) := by
      have e1 := (BoundedContinuousFunction.evalCLM ℝ (0 : ℤ)).hasFDerivAt (x := rr (T n u))
      have h1' := e1.comp (T n u) ((hrr _ hx).differentiableAt.hasFDerivAt)
      exact h1'
    have hS := hH.sqrt hpos.ne'
    rw [hS.fderiv]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    have hsq : (1 / 2 : ℝ) ≤ Real.sqrt ((rr (T n u)) 0) * 1 := by
      have : (1 / 2 : ℝ) ≤ (rr (T n u)) 0 := by have := (hbd (T n u) hx 0).1; linarith
      nlinarith [Real.sqrt_nonneg ((rr (T n u)) 0), Real.sq_sqrt hpos.le]
    have hcoef : |1 / (2 * Real.sqrt ((rr (T n u)) 0))| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one (by positivity)]
      linarith
    have hk : |(fderiv ℝ rr (T n u) (T n h)) 0| ≤ C * ‖u‖ * ‖h‖ := by
      have h1 := (fderiv ℝ rr (T n u) (T n h)).norm_coe_le_norm 0
      rw [Real.norm_eq_abs] at h1
      refine h1.trans ?_
      have h2 := (fderiv ℝ rr (T n u)).le_opNorm (T n h)
      have h3 := hrr2 (T n u) hx
      rw [hnorm] at h3
      exact h2.trans (mul_le_mul h3 (hT n h) (norm_nonneg _) (by positivity))
    rw [abs_mul]
    calc |1 / (2 * Real.sqrt ((rr (T n u)) 0))| * |(fderiv ℝ rr (T n u) (T n h)) 0| ≤ 1 * (C * ‖u‖ * ‖h‖) :=
          mul_le_mul hcoef hk (abs_nonneg _) zero_le_one
      _ = C * ‖u‖ * ‖h‖ := one_mul _
  -- G(0) = 0
  have hG0 : G 0 = 0 := by
    apply lp.ext
    funext n
    rw [hGv 0 (mem_ball_self hρpos) n, pkg_b_zero hκ hρ0 (hpk n), mul_zero]
    rfl
  obtain ⟨K, hK, hZa, hZd⟩ := QuantumNLS.Local007Zeta.zeta_clause hρpos hC hCg (hss.mono hs1)
    hss1 hss2 hGa hG0 Fmap norm_Fmap hGd
  have hZn : ∀ u ∈ ball (0 : L2T L) ρ, ∀ n : ℤ,
      (mulCLM (ss u) (G u)) n = gcoef L κ * b n u * ((Real.sqrt (rr u n) : ℝ) : ℂ) := by
    intro u hu n
    rw [QuantumNLS.Local007Mul.mulCLM_apply, hssn u hu n, hGv u hu n, mul_comm]
  refine ⟨fun u => mulCLM (ss u) (G u), K, hK, hZn, hZa, hZd, ?_⟩
  intro u hu
  obtain ⟨-, -, -, hsum, -⟩ := QuantumNLS.RootIndexedMassesCollapsed.root_indexed_masses_collapsed hκ u
  rw [← QuantumNLS.Local007Mul.tsum_sq, ← hsum]
  refine tsum_congr fun n => ?_
  rw [hZn u hu n, hmass u (hs0 hu) n, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by have := (hbd u (hs0 hu) n).1; linarith)]

end QuantumNLS.Local007Statement
#print axioms QuantumNLS.Local007Statement.reset_exact_factor
