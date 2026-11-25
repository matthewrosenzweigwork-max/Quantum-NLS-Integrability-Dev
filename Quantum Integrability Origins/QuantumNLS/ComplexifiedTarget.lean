import QuantumNLS.ProductTorusComplexMultilinear
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Complexified analytic infrastructure, stage X5: holomorphic extension with a complex target

Item (i) of the R-3FEAD88B E5 assignment: the stage C2/C3 constructions (frozen, read-only) generalized from
`F → F` to `F → W` with `W` a complex Banach space (e.g. `W = ℂ`). For a real inner product space `F`:
* `cxMLW F W n`: complexification of continuous real `n`-linear maps `F^n → W` to complex `n`-linear maps
  `(Cx F)^n → W` (currying, with C2's `cxLin`), `‖cxMLW F W n‖ ≤ 2ⁿ`, and `q_n(ι a₁,…,ι aₙ) = p_n(a₁,…,aₙ)`;
* `cxExtW p u z = Σ q_n((z − ι u)ⁿ)`: from `HasFPowerSeriesOnBall T p u r` and `‖p n‖ rⁿ ≤ C`, a power series at
  `ι u` on the complex ball of radius `r/2`, bounded by `2C` on the `r/4` ball, with `T̃(ι x) = T x`;
* `exists_majorant_of_analyticAt` and **`holomorphic_extension_of_analyticAt`**: every real-analytic `T : F → W`
  at `u` has a complex-analytic (hence complex-differentiable) extension `T̃ : Cx F → W` on a complex ball around
  `ι u`, bounded there, with `T̃ ∘ ι = T` on the real ball; `holomorphic_extension_of_majorantW` gives the version
  uniform over a family with a common radius and majorant.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped NNReal ENNReal

namespace QuantumNLS.ComplexifiedTarget

open QuantumNLS.ProductTorusComplexification QuantumNLS.ProductTorusComplexMultilinear

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]

omit [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W] in
theorem curryLeft_add_applyW {n : ℕ} (p q : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) W) (x : F) :
    (p + q).curryLeft x = p.curryLeft x + q.curryLeft x := by
  ext m
  simp

omit [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W] in
theorem curryLeft_smul_applyW {n : ℕ} (c : ℝ) (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) W)
    (x : F) : (c • p).curryLeft x = c • p.curryLeft x := by
  ext m
  simp

variable (F W) in
/-- Complexification of continuous real multilinear maps `F^n → W`, by currying. -/
def cxMLW : (n : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin n => F) W →L[ℝ]
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Cx F) W
  | 0 => LinearMap.mkContinuous
      { toFun := fun p => ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => Cx F) (p 0)
        map_add' := fun p q => by
          ext v
          simp
        map_smul' := fun c p => by
          ext v
          simp }
      1 (fun p => by
        show ‖ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => Cx F) (p 0)‖ ≤ 1 * ‖p‖
        rw [ContinuousMultilinearMap.norm_constOfIsEmpty, one_mul]
        exact (p.le_opNorm 0).trans (by simp))
  | n + 1 => LinearMap.mkContinuous
      { toFun := fun p => (cxLin ((cxMLW n).comp p.curryLeft)).uncurryLeft
        map_add' := fun p q => by
          ext v
          simp only [ContinuousLinearMap.uncurryLeft_apply, cxLin_apply, ContinuousLinearMap.comp_apply,
            curryLeft_add_applyW, map_add, _root_.add_apply, smul_add]
          abel
        map_smul' := fun c p => by
          ext v
          simp only [ContinuousLinearMap.uncurryLeft_apply, cxLin_apply, ContinuousLinearMap.comp_apply,
            curryLeft_smul_applyW, map_smul, _root_.smul_apply, RingHom.id_apply]
          rw [smul_comm Complex.I c]
          rw [← smul_add]; rfl }
      (2 * ‖cxMLW n‖) (fun p => by
        refine (ContinuousLinearMap.uncurryLeft_norm (Ei := fun _ : Fin (n + 1) => Cx F)
          (cxLin ((cxMLW n).comp p.curryLeft))).le.trans ?_
        calc ‖cxLin ((cxMLW n).comp p.curryLeft)‖ ≤ 2 * ‖(cxMLW n).comp p.curryLeft‖ := norm_cxLin_le _
          _ ≤ 2 * (‖cxMLW n‖ * ‖p.curryLeft‖) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
          _ = 2 * ‖cxMLW n‖ * ‖p‖ := by rw [ContinuousMultilinearMap.curryLeft_norm, mul_assoc])

theorem cxMLW_zero_eq (p : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => F) W) :
    cxMLW F W 0 p = ContinuousMultilinearMap.constOfIsEmpty ℂ (fun _ : Fin 0 => Cx F) (p 0) := rfl

theorem cxMLW_succ_eq {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) W) :
    cxMLW F W (n + 1) p = (cxLin ((cxMLW F W n).comp p.curryLeft)).uncurryLeft := rfl

theorem cxMLW_succ_apply {n : ℕ} (p : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => F) W)
    (v : Fin (n + 1) → Cx F) :
    cxMLW F W (n + 1) p v = cxMLW F W n (p.curryLeft (Cx.re (v 0))) (Fin.tail v) +
      Complex.I • cxMLW F W n (p.curryLeft (Cx.im (v 0))) (Fin.tail v) := by
  rw [cxMLW_succ_eq, ContinuousLinearMap.uncurryLeft_apply, cxLin_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, _root_.add_apply, _root_.smul_apply]

/-- `‖cxMLW F W n‖ ≤ 2ⁿ`. -/
theorem norm_cxMLW_le : ∀ n : ℕ, ‖cxMLW F W n‖ ≤ 2 ^ n
  | 0 => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
    rw [cxMLW_zero_eq, ContinuousMultilinearMap.norm_constOfIsEmpty, pow_zero, one_mul]
    exact (p.le_opNorm 0).trans (by simp)
  | n + 1 => by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun p => ?_
    rw [cxMLW_succ_eq, ContinuousLinearMap.uncurryLeft_norm]
    calc ‖cxLin ((cxMLW F W n).comp p.curryLeft)‖ ≤ 2 * ‖(cxMLW F W n).comp p.curryLeft‖ := norm_cxLin_le _
      _ ≤ 2 * (‖cxMLW F W n‖ * ‖p.curryLeft‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * (2 ^ n * ‖p‖) := by
        rw [ContinuousMultilinearMap.curryLeft_norm]
        gcongr
        exact norm_cxMLW_le n
      _ = 2 ^ (n + 1) * ‖p‖ := by ring

/-- Agreement at real points: `q_n (ι a₁, …, ι aₙ) = p_n (a₁, …, aₙ)`. -/
theorem cxMLW_ι : ∀ (n : ℕ) (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => F) W) (a : Fin n → F),
    cxMLW F W n p (fun i => Cx.ι (a i)) = p a
  | 0, p, a => by
    rw [cxMLW_zero_eq, ContinuousMultilinearMap.constOfIsEmpty_apply, Subsingleton.elim a 0]
  | n + 1, p, a => by
    rw [cxMLW_succ_apply]
    simp only [Cx.re_ι, Cx.im_ι, map_zero, zero_apply, smul_zero, add_zero]
    have h := cxMLW_ι n (p.curryLeft (a 0)) (Fin.tail a)
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · rw [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]

/-- Termwise complexification of a real formal multilinear series `F → W`. -/
def cxSeriesW (p : FormalMultilinearSeries ℝ F W) : FormalMultilinearSeries ℂ (Cx F) W :=
  fun n => cxMLW F W n (p n)

theorem norm_cxSeriesW_le (p : FormalMultilinearSeries ℝ F W) (n : ℕ) : ‖cxSeriesW p n‖ ≤ 2 ^ n * ‖p n‖ :=
  ((cxMLW F W n).le_opNorm (p n)).trans (mul_le_mul_of_nonneg_right (norm_cxMLW_le n) (norm_nonneg _))

/-- The extension `T̃ z = Σ q n ((z − ι u)ⁿ)`. -/
def cxExtW (p : FormalMultilinearSeries ℝ F W) (u : F) (z : Cx F) : W := (cxSeriesW p).sum (z - Cx.ι u)

theorem cxSeriesW_bound (p : FormalMultilinearSeries ℝ F W) {r C : ℝ} (hC : ∀ n, ‖p n‖ * r ^ n ≤ C)
    (hr : 0 < r) (n : ℕ) : ‖cxSeriesW p n‖ * (r / 2) ^ n ≤ C := by
  have e : (2 : ℝ) ^ n * (r / 2) ^ n = r ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  calc ‖cxSeriesW p n‖ * (r / 2) ^ n ≤ (2 ^ n * ‖p n‖) * (r / 2) ^ n :=
        mul_le_mul_of_nonneg_right (norm_cxSeriesW_le p n) (by positivity)
    _ = ‖p n‖ * r ^ n := by rw [← e]; ring
    _ ≤ C := hC n

theorem hasFPowerSeriesOnBall_cxExtW [CompleteSpace W] (p : FormalMultilinearSeries ℝ F W) (u : F) {r C : ℝ}
    (hr : 0 < r) (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) :
    HasFPowerSeriesOnBall (cxExtW p u) (cxSeriesW p) (Cx.ι u) (ENNReal.ofReal (r / 2)) := by
  have hrad : ENNReal.ofReal (r / 2) ≤ (cxSeriesW p).radius :=
    (cxSeriesW p).le_radius_of_bound C (r := (r / 2).toNNReal) (fun n => by
      rw [Real.coe_toNNReal _ (by positivity)]
      exact cxSeriesW_bound p hC hr n)
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (r / 2) := ENNReal.ofReal_pos.2 (by positivity)
  have H1 := (((cxSeriesW p).hasFPowerSeriesOnBall (hpos.trans_le hrad)).mono hpos hrad).comp_sub (Cx.ι u)
  rw [zero_add] at H1
  exact H1

theorem norm_cxExtW_le (p : FormalMultilinearSeries ℝ F W) (u : F) {r C : ℝ}
    (hC : ∀ n, ‖p n‖ * r ^ n ≤ C) (z : Cx F) (hz : z ∈ ball (Cx.ι u) (r / 4)) : ‖cxExtW p u z‖ ≤ 2 * C := by
  have hy : ‖z - Cx.ι u‖ < r / 4 := mem_ball_iff_norm.1 hz
  have hb : ∀ n : ℕ, ‖cxSeriesW p n (fun _ => z - Cx.ι u)‖ ≤ C * (1 / 2) ^ n := fun n => by
    have e : (2 : ℝ) ^ n * (r / 4) ^ n = r ^ n * (1 / 2) ^ n := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      ring
    calc ‖cxSeriesW p n (fun _ => z - Cx.ι u)‖ ≤ ‖cxSeriesW p n‖ * ∏ _i : Fin n, ‖z - Cx.ι u‖ :=
          (cxSeriesW p n).le_opNorm _
      _ = ‖cxSeriesW p n‖ * ‖z - Cx.ι u‖ ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ (2 ^ n * ‖p n‖) * (r / 4) ^ n :=
          mul_le_mul (norm_cxSeriesW_le p n) (pow_le_pow_left₀ (norm_nonneg _) hy.le n)
            (by positivity) (by positivity)
      _ = (‖p n‖ * r ^ n) * (1 / 2) ^ n := by
          rw [show (2 : ℝ) ^ n * ‖p n‖ * (r / 4) ^ n = ‖p n‖ * (2 ^ n * (r / 4) ^ n) by ring, e]
          ring
      _ ≤ C * (1 / 2) ^ n := mul_le_mul_of_nonneg_right (hC n) (by positivity)
  have h := tsum_of_norm_bounded (hasSum_geometric_two.mul_left C) hb
  calc ‖cxExtW p u z‖ = ‖∑' n, cxSeriesW p n (fun _ => z - Cx.ι u)‖ := rfl
    _ ≤ C * 2 := h
    _ = 2 * C := mul_comm _ _

theorem cxExtW_ι {T : F → W} {p : FormalMultilinearSeries ℝ F W} {u : F} {r : ℝ}
    (hT : HasFPowerSeriesOnBall T p u (ENNReal.ofReal r)) (x : F) (hx : x ∈ ball u r) :
    cxExtW p u (Cx.ι x) = T x := by
  have hy : x - u ∈ Metric.eball (0 : F) (ENNReal.ofReal r) := by
    rw [Metric.eball_ofReal, mem_ball_zero_iff, ← dist_eq_norm]
    exact hx
  have h2 := hT.hasSum hy
  have hux : u + (x - u) = x := by abel
  rw [hux] at h2
  have e : (fun n => cxSeriesW p n (fun _ => Cx.ι x - Cx.ι u)) = fun n => p n (fun _ => x - u) := by
    funext n
    rw [← ι_sub]
    exact cxMLW_ι n (p n) (fun _ => x - u)
  have h3 : HasSum (fun n => cxSeriesW p n (fun _ => Cx.ι x - Cx.ι u)) (T x) := by
    rw [e]
    exact h2
  exact h3.tsum_eq

/-- Common bounded holomorphic extension from a uniform Taylor majorant, complex target `W`. -/
theorem holomorphic_extension_of_majorantW [CompleteSpace W] {ι : Type*} (T : ι → F → W) (u : F) {r C : ℝ}
    (hr : 0 < r) (hT : ∀ i, ∃ p : FormalMultilinearSeries ℝ F W,
      HasFPowerSeriesOnBall (T i) p u (ENNReal.ofReal r) ∧ ∀ n, ‖p n‖ * r ^ n ≤ C) :
    ∃ R > (0 : ℝ), ∃ M : ℝ, ∀ i, ∃ Tc : Cx F → W,
      DifferentiableOn ℂ Tc (ball (Cx.ι u) R) ∧ AnalyticOnNhd ℂ Tc (ball (Cx.ι u) R) ∧
      (∀ z ∈ ball (Cx.ι u) R, ‖Tc z‖ ≤ M) ∧ ∀ x ∈ ball u R, Tc (Cx.ι x) = T i x := by
  refine ⟨r / 4, by positivity, 2 * C, fun i => ?_⟩
  obtain ⟨p, hp, hC⟩ := hT i
  have H := hasFPowerSeriesOnBall_cxExtW p u hr hC
  have hsub : ball (Cx.ι u) (r / 4) ⊆ Metric.eball (Cx.ι u) (ENNReal.ofReal (r / 2)) := by
    rw [Metric.eball_ofReal]
    exact ball_subset_ball (by linarith)
  exact ⟨cxExtW p u, H.differentiableOn.mono hsub, fun z hz => H.analyticOnNhd z (hsub hz),
    fun z hz => norm_cxExtW_le p u hC z hz, fun x hx => cxExtW_ι hp x (ball_subset_ball (by linarith) hx)⟩

omit [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W] in
/-- A real-analytic map has a power series at `u` with a Taylor majorant on some positive radius. -/
theorem exists_majorant_of_analyticAt {T : F → W} {u : F} (hT : AnalyticAt ℝ T u) :
    ∃ r > (0 : ℝ), ∃ C : ℝ, ∃ p : FormalMultilinearSeries ℝ F W,
      HasFPowerSeriesOnBall T p u (ENNReal.ofReal r) ∧ ∀ n, ‖p n‖ * r ^ n ≤ C := by
  obtain ⟨p, R, hp⟩ := hT
  obtain ⟨r', hr'0, hr'R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius (hr'R.trans_le hp.r_le)
  refine ⟨r', by exact_mod_cast hr'0, C, p, ?_, hC⟩
  rw [ENNReal.ofReal_coe_nnreal]
  exact hp.mono hr'0 hr'R.le

/-- **Item (i)**: every real-analytic `T : F → W` at `u` has a holomorphic extension to a complex ball around `ι u`
in `Cx F`, bounded there, agreeing with `T` on the real ball. -/
theorem holomorphic_extension_of_analyticAt [CompleteSpace W] {T : F → W} {u : F} (hT : AnalyticAt ℝ T u) :
    ∃ R > (0 : ℝ), ∃ M : ℝ, ∃ Tc : Cx F → W,
      DifferentiableOn ℂ Tc (ball (Cx.ι u) R) ∧ AnalyticOnNhd ℂ Tc (ball (Cx.ι u) R) ∧
      (∀ z ∈ ball (Cx.ι u) R, ‖Tc z‖ ≤ M) ∧ ∀ x ∈ ball u R, Tc (Cx.ι x) = T x := by
  obtain ⟨r, hr, C, p, hp, hC⟩ := exists_majorant_of_analyticAt hT
  obtain ⟨R, hR, M, h⟩ := holomorphic_extension_of_majorantW (fun _ : Unit => T) u hr (fun _ => ⟨p, hp, hC⟩)
  exact ⟨R, hR, M, h ()⟩

end QuantumNLS.ComplexifiedTarget

#print axioms QuantumNLS.ComplexifiedTarget.norm_cxMLW_le
#print axioms QuantumNLS.ComplexifiedTarget.cxMLW_ι
#print axioms QuantumNLS.ComplexifiedTarget.hasFPowerSeriesOnBall_cxExtW
#print axioms QuantumNLS.ComplexifiedTarget.norm_cxExtW_le
#print axioms QuantumNLS.ComplexifiedTarget.cxExtW_ι
#print axioms QuantumNLS.ComplexifiedTarget.holomorphic_extension_of_majorantW
#print axioms QuantumNLS.ComplexifiedTarget.holomorphic_extension_of_analyticAt
