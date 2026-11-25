import QuantumNLS.ResetMoserWinding
import QuantumNLS.ResetMoserYDiff

/-!
# `thm:reset-moser` (LOCAL-017), stage 3b-1 (item 2(b), infrastructure): the primitive `α`, bounds on `DX_j`, uniform bound on `Dφ_j^s`

Source: `symplectic_correction.tex`, "The periods of a radial primitive": `α_z(h) = ∫_0^1 t Ω_{tz}(z,h) dt`, `dα = Ω`, `α^0_z(h) = Im⟨z,h⟩`,
`β = α − α^0`; and the first derivative of `A_j` needs "the variation of the integral of a one-form along this loop".

* `d2q`, `hasFDerivAt_fderiv_q`, `norm_d2q_le`: second derivative of `q_n` (`‖D²q_n‖ ≤ 2`);
* `Hyp.hasFDerivAt_Xn`: on `B_ρ`, `X_j` is Fréchet differentiable with `‖DX_j(w)‖ ≤ 2Mρ² + 2` (from the explicit `DYcov` formula, `norm_Ycov_deriv_le`);
* `Hyp.norm_fderiv_phi_le`: Gronwall, `‖Dφ_j^s(z)‖ ≤ exp((2Mρ²+2)·2π)` for `z ∈ B_ρ`, `s ∈ [0, 2π]` (uniform in `z`);
* `alphaR S z = betaR S z + ½ ω(z,·)` (`alphaR_apply` shows it is the source formula `∫_0^1 t Ω_{tz}(z,h) dt`), `alphaD` its derivative,
  `alphaR_hasFDerivAt`, `alphaD_antisym` (`Dα_x(a)(h) − Dα_x(h)(a) = Ω_x(a,h)`, i.e. `dα = Ω`), `norm_alphaR_le`, `norm_alphaD_le`,
  `alphaD_continuousAt`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric MeasureTheory
open scoped Interval

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket QuantumNLS.RealAnalyticDef
open QuantumNLS.ResetMoserFlow

theorem norm_apply_le_norm' (w : K) (n : ℤ) : ‖w n‖ ≤ ‖w‖ := lp.norm_apply_le_norm (by norm_num) w n

/-- The (constant) second derivative of `q_n`. -/
def d2q (n : ℤ) : K →L[ℝ] Cov :=
  LinearMap.mkContinuous
    { toFun := fun w => fderiv ℝ (q n) w
      map_add' := by
        intro a b
        ext h
        simp only [fderiv_q_apply, ContinuousLinearMap.add_apply]
        simp [mul_add, add_mul, Complex.add_re]
      map_smul' := by
        intro r a
        ext h
        simp only [fderiv_q_apply, ContinuousLinearMap.smul_apply, RingHom.id_apply, smul_eq_mul]
        rw [rsmul_apply]
        simp only [map_mul, Complex.conj_ofReal, mul_assoc]
        rw [Complex.re_ofReal_mul]
        ring }
    2 (fun w => by
      refine (norm_fderiv_q_le n w).trans ?_
      have := norm_apply_le_norm' w n
      linarith)

theorem d2q_apply (n : ℤ) (w : K) : d2q n w = fderiv ℝ (q n) w := rfl

theorem norm_d2q_le (n : ℤ) : ‖d2q n‖ ≤ 2 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem hasFDerivAt_fderiv_q (n : ℤ) (w : K) : HasFDerivAt (fderiv ℝ (q n)) (d2q n) w := by
  have : fderiv ℝ (q n) = ⇑(d2q n) := funext fun w => (d2q_apply n w).symm
  rw [this]
  exact (d2q n).hasFDerivAt

theorem Hyp.hasFDerivAt_Xn (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {w : K} (hw : w ∈ ball (0 : K) ρ) (j : ℤ) :
    HasFDerivAt (Xn S.Ω j) (fderiv ℝ (Xn S.Ω j) w) w ∧
      ‖fderiv ℝ (Xn S.Ω j) w‖ ≤ 2 * M * ρ ^ 2 + 2 := by
  have hwR := ball_mono_R hL hw
  have hD := Dl_hasFDerivAt S hwR
  have hb : HasFDerivAt (fun v => -(fderiv ℝ (q j) v)) (-(d2q j)) w := (hasFDerivAt_fderiv_q j w).neg
  have hsm : ‖Dl S w‖ < 1 := S.Ω_lt w hwR
  obtain ⟨L, hL1, hL2⟩ := hasFDerivAt_Ycov hD hb hsm
  have hXeq : Xn S.Ω j = fun v => Ycov (Dl S v) (-(fderiv ℝ (q j) v)) := funext fun v => rfl
  rw [hXeq]
  have hfd : fderiv ℝ (fun v => Ycov (Dl S v) (-(fderiv ℝ (q j) v))) w = L := hL1.fderiv
  refine ⟨by rw [hfd]; exact hL1, ?_⟩
  rw [hfd]
  have hwn : ‖w‖ < ρ := mem_ball_zero_iff.1 hw
  have hD' : ‖fderiv ℝ S.Ω w‖ ≤ M * ρ := (hL.b1 w hw).trans (mul_le_mul_of_nonneg_left hwn.le hL.M0)
  have hb0 : ‖-(fderiv ℝ (q j) w)‖ ≤ 2 * ρ := by
    rw [norm_neg]
    refine (norm_fderiv_q_le j w).trans ?_
    have := norm_apply_le_norm' w j
    linarith
  have hb' : ‖-(d2q j)‖ ≤ 2 := by rw [norm_neg]; exact norm_d2q_le j
  refine ContinuousLinearMap.opNorm_le_bound _ (by have := hL.M0; have := hL.ρpos; positivity) fun h => ?_
  rw [hL2 h]
  have := norm_Ycov_deriv_le (D := Dl S) (b := fun v => -(fderiv ℝ (q j) v)) (D' := fderiv ℝ S.Ω w)
    (b' := -(d2q j)) (z := w) hsm h
  refine this.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  have h1 : ‖fderiv ℝ S.Ω w‖ * ‖-(fderiv ℝ (q j) w)‖ ≤ (M * ρ) * (2 * ρ) :=
    mul_le_mul hD' hb0 (norm_nonneg _) (by have := hL.M0; have := hL.ρpos; positivity)
  nlinarith

/-- Uniform Gronwall bound for the variational flow on `[0, 2π]`. -/
theorem Hyp.norm_fderiv_phi_le (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) (j : ℤ) {z : K}
    (hz : z ∈ ball (0 : K) ρ) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (2 * Real.pi)) :
    ‖fderiv ℝ (S.φ j s) z‖ ≤ Real.exp ((2 * M * ρ ^ 2 + 2) * (2 * Real.pi)) := by
  have hρ := hL.ρR
  have hLc : 0 ≤ 2 * M * ρ ^ 2 + 2 := by have := hL.M0; positivity
  have hvar := fun r => S.variational_flow hρ j hz r
  have hmem : ∀ r : ℝ, S.φ j r z ∈ ball (0 : K) ρ := fun r => by
    rw [mem_ball_zero_iff, S.norm_flow (ball_mono_R hL hz) j r]
    exact mem_ball_zero_iff.1 hz
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := fun r => fderiv ℝ (S.φ j r) z)
    (f' := fun r => (fderiv ℝ (Xn S.Ω j) (S.φ j r z)).comp (fderiv ℝ (S.φ j r) z))
    (δ := 1) (K := 2 * M * ρ ^ 2 + 2) (ε := 0) (a := 0) (b := 2 * Real.pi)
    (fun r _ => (hvar r).continuousAt.continuousWithinAt)
    (fun r _ => (hvar r).hasDerivWithinAt)
    (by
      have h0 : S.φ j 0 = id := funext (S.φ_zero j)
      simp only [h0, fderiv_id]
      exact ContinuousLinearMap.norm_id_le)
    (fun r _ => by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      rw [add_zero]
      exact mul_le_mul_of_nonneg_right ((S.hasFDerivAt_Xn hL (hmem r) j).2) (norm_nonneg _)) s hs
  rw [gronwallBound_ε0, sub_zero] at hG
  refine hG.trans ?_
  rw [one_mul]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hs.2 hLc)

/-- `α_z = β_z + ½ ω(z,·)`. -/
def alphaR (S : Hyp) (z : K) : Cov := betaR S z + (1 / 2 : ℝ) • omegaF z

/-- The derivative of `alphaR`. -/
def alphaD (S : Hyp) (x : K) : K →L[ℝ] Cov :=
  (∫ t in (0 : ℝ)..1, Lval S x t) + (1 / 2 : ℝ) • (omegaF : K →L[ℝ] Cov)

theorem alphaR_hasFDerivAt (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) :
    HasFDerivAt (alphaR S) (alphaD S x) x := by
  have h1 := betaR_hasFDerivAt S hL hx
  have h2 : HasFDerivAt (fun z : K => omegaF z) (omegaF : K →L[ℝ] Cov) x :=
    (omegaF : K →L[ℝ] Cov).hasFDerivAt
  exact h1.add (h2.const_smul (1 / 2 : ℝ))

/-- `dα = Ω`: the antisymmetrised derivative of `α` is `Ω` (from `betaR_antisym` and `Ω = Dl + ω`). -/
theorem alphaD_antisym (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) (a h : K) :
    alphaD S x a h - alphaD S x h a = S.Ω x a h := by
  have h1 := betaR_antisym S hL hx a h
  have e1 : alphaD S x a h = (∫ t in (0 : ℝ)..1, Lval S x t) a h + (1 / 2 : ℝ) * omegaF a h := by
    simp [alphaD]
  have e2 : alphaD S x h a = (∫ t in (0 : ℝ)..1, Lval S x t) h a + (1 / 2 : ℝ) * omegaF h a := by
    simp [alphaD]
  rw [e1, e2]
  have h3 : omegaF a h = - omegaF h a := omegaF_alt a h
  have h4 : S.Ω x a h = Dl S x a h + omegaF a h := by simp [Dl]
  rw [h4, ← h1, h3]
  ring

theorem norm_alphaR_le (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ) :
    ‖alphaR S z‖ ≤ M * ρ ^ 3 + ‖(omegaF : Form)‖ * ρ := by
  have hzn : ‖z‖ < ρ := mem_ball_zero_iff.1 hz
  have h1 : ‖betaR S z‖ ≤ M * ρ ^ 3 := by
    refine (norm_betaR_le S hL hz).trans (mul_le_mul_of_nonneg_left ?_ hL.M0)
    exact pow_le_pow_left₀ (norm_nonneg _) hzn.le 3
  have h2 : ‖(1 / 2 : ℝ) • omegaF z‖ ≤ ‖(omegaF : Form)‖ * ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have : ‖omegaF z‖ ≤ ‖(omegaF : Form)‖ * ‖z‖ := (omegaF : Form).le_opNorm z
    have h0 := norm_nonneg (omegaF : Form)
    have h5 := mul_le_mul_of_nonneg_left hzn.le h0
    have h6 := norm_nonneg (omegaF z)
    linarith
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem norm_alphaD_le (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) :
    ‖alphaD S x‖ ≤ 2 * M * ρ ^ 2 + ‖(omegaF : Form)‖ := by
  have h1 : ‖∫ t in (0 : ℝ)..1, Lval S x t‖ ≤ 2 * M * ρ ^ 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun t => Lval S x t) (C := 2 * M * ρ ^ 2) (fun t ht => by
        rw [uIoc_of_le zero_le_one] at ht
        exact norm_Lval_le S hL hx ⟨ht.1.le, ht.2⟩)
    simpa using this
  have h2 : ‖(1 / 2 : ℝ) • (omegaF : K →L[ℝ] Cov)‖ ≤ ‖(omegaF : Form)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h0 := norm_nonneg (omegaF : Form)
    show _ * ‖(omegaF : Form)‖ ≤ _
    linarith
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

theorem alphaD_continuousAt (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x₀ : K} (hx₀ : x₀ ∈ ball (0 : K) ρ) :
    ContinuousAt (alphaD S) x₀ := by
  have hT : ball (0 : K) ρ ∈ 𝓝 x₀ := isOpen_ball.mem_nhds hx₀
  have hI : ContinuousAt (fun x => ∫ t in (0 : ℝ)..1, Lval S x t) x₀ := by
    refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => 2 * M * ρ ^ 2) ?_ ?_ ?_ ?_
    · filter_upwards [hT] with x hx
      rw [uIoc_of_le zero_le_one]
      exact (Lval_cont S hL hx).aestronglyMeasurable_of_subset_isCompact isCompact_Icc
        measurableSet_Ioc Ioc_subset_Icc_self
    · filter_upwards [hT] with x hx
      refine Filter.Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le zero_le_one] at ht
      exact norm_Lval_le S hL hx ⟨ht.1.le, ht.2⟩
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [uIoc_of_le zero_le_one] at ht
      have htm : ∀ x ∈ ball (0 : K) ρ, t • x ∈ ball (0 : K) ρ := fun x hx => scale_mem' hx ⟨ht.1.le, ht.2⟩
      have hsm : ContinuousAt (fun x : K => t • x) x₀ := by fun_prop
      have hD : ContinuousAt (fun x : K => Dl S (t • x)) x₀ :=
        ContinuousAt.comp (g := Dl S) (f := fun x : K => t • x) (x := x₀)
          ((Dl_continuousOn S).continuousAt (isOpen_ball.mem_nhds (ball_mono_R hL (htm x₀ hx₀)))) hsm
      have hF : ContinuousAt (fun x : K => fderiv ℝ S.Ω (t • x)) x₀ :=
        ContinuousAt.comp (g := fderiv ℝ S.Ω) (f := fun x : K => t • x) (x := x₀)
          ((fderivΩ_continuousOn S).continuousAt (isOpen_ball.mem_nhds (ball_mono_R hL (htm x₀ hx₀)))) hsm
      have hA : ContinuousAt (fun x : K => (ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))) x₀ :=
        ContinuousAt.clm_comp ((ContinuousLinearMap.apply ℝ Cov).continuous.continuousAt) hF
      have : (fun x : K => Lval S x t) =
          fun x => t • Dl S (t • x) + (t ^ 2) • ((ContinuousLinearMap.apply ℝ Cov x).comp (fderiv ℝ S.Ω (t • x))) :=
        funext fun x => rfl
      rw [this]
      exact (hD.const_smul t).add (hA.const_smul (t ^ 2))
  have : alphaD S = fun x => (∫ t in (0 : ℝ)..1, Lval S x t) + (1 / 2 : ℝ) • (omegaF : K →L[ℝ] Cov) :=
    funext fun x => rfl
  rw [this]
  exact hI.add continuousAt_const

theorem alphaR_continuousAt (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {x : K} (hx : x ∈ ball (0 : K) ρ) :
    ContinuousAt (alphaR S) x := (alphaR_hasFDerivAt S hL hx).continuousAt

/-- The source formula `α_z(h) = ∫_0^1 t Ω_{tz}(z,h) dt`. -/
theorem alphaR_apply (S : Hyp) {ρ M : ℝ} (hL : Loc S ρ M) {z : K} (hz : z ∈ ball (0 : K) ρ) (h : K) :
    alphaR S z h = ∫ t in (0 : ℝ)..1, t * S.Ω (t • z) z h := by
  have hint : IntervalIntegrable (fun t : ℝ => t • (Dl S (t • z) z)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using radial_cont S hL hz
  have hb : betaR S z h = ∫ t in (0 : ℝ)..1, t * Dl S (t • z) z h := by
    unfold betaR
    rw [ContinuousLinearMap.intervalIntegral_apply hint h]
    simp
  have hc1 : Continuous (fun t : ℝ => t * Dl S (t • z) z h) → True := fun _ => trivial
  have hc : ContinuousOn (fun t : ℝ => t * Dl S (t • z) z h) (Icc (0 : ℝ) 1) := by
    have := (ContinuousLinearMap.apply ℝ ℝ h).continuous.comp_continuousOn (radial_cont S hL hz)
    refine this.congr fun t _ => ?_
    simp
  have hI2 : ∫ t in (0 : ℝ)..1, t * omegaF z h = (1 / 2 : ℝ) * omegaF z h := by
    rw [intervalIntegral.integral_mul_const]
    simp
  have hsum : ∀ t : ℝ, t * S.Ω (t • z) z h = t * Dl S (t • z) z h + t * omegaF z h := by
    intro t; simp [Dl]; ring
  have hcongr : ∫ t in (0 : ℝ)..1, t * S.Ω (t • z) z h =
      ∫ t in (0 : ℝ)..1, (t * Dl S (t • z) z h + t * omegaF z h) :=
    intervalIntegral.integral_congr fun t _ => hsum t
  rw [hcongr, intervalIntegral.integral_add (hc.intervalIntegrable_of_Icc zero_le_one)
    (show IntervalIntegrable (fun t : ℝ => t * omegaF z h) volume 0 1 from
      (continuous_id.mul continuous_const).intervalIntegrable _ _), hI2, ← hb]
  simp [alphaR]

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.hasFDerivAt_fderiv_q
#print axioms QuantumNLS.ResetMoser.Hyp.hasFDerivAt_Xn
#print axioms QuantumNLS.ResetMoser.Hyp.norm_fderiv_phi_le
#print axioms QuantumNLS.ResetMoser.alphaR_hasFDerivAt
#print axioms QuantumNLS.ResetMoser.alphaD_antisym
#print axioms QuantumNLS.ResetMoser.norm_alphaR_le
#print axioms QuantumNLS.ResetMoser.norm_alphaD_le
#print axioms QuantumNLS.ResetMoser.alphaD_continuousAt
#print axioms QuantumNLS.ResetMoser.alphaR_apply
