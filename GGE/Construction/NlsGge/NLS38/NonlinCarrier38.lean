import NlsGge.NLS38.WeightedTrilinear38

/-! # GWP piece A2: the nonlinearity as a map of the real Hilbert carrier `h^m`

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A2.  The sequence-level estimates of A1
(`hn_nonlin_le`, `hn_nonlin_sub_le`) show that `nonlin` maps `h^m` to `h^m`, is bounded on balls,
and is Lipschitz on balls.  Here these are repackaged on `SobolevCarrier38 m` (real normed
structure only), together with the reflection covariance `nonlin (refl x) = refl (nonlin x)`
(used for the symmetry `S_t 𝓕 = 𝓕 S_t`) and the phase gauge covariance.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open scoped ComplexConjugate NNReal

/-! ## Sequence level: `nonlin` maps `h^m` to `h^m` -/

theorem nonlin_mem38 (m : ℕ) (hm : 1 ≤ m) :
    ∀ x ∈ seqSobolev38 (m : ℝ), nonlin x ∈ seqSobolev38 (m : ℝ) := by
  obtain ⟨C, -, hC⟩ := hn_nonlin_le m hm
  exact fun x hx => (hC x hx).1

/-- `‖x‖_{h^m}` of a carrier element is `hn m` of its coordinate sequence. -/
theorem hn_coe38 (m : ℕ) (x : SobolevCarrier38 (m : ℝ)) : hn m (carrierCoe38 (m : ℝ) x) = ‖x‖ := by
  have h := norm_carrierMk38_eq_hn m (carrierCoe38 (m : ℝ) x) (carrierCoe38_mem (m : ℝ) x)
  exact h.symm.trans (by rfl)

/-- The sequence `x - y` of two carrier elements is the coordinate sequence of `x - y`. -/
theorem carrierCoe38_sub' (m : ℕ) (x y : SobolevCarrier38 (m : ℝ)) :
    carrierCoe38 (m : ℝ) (x - y) = fun n => carrierCoe38 (m : ℝ) x n - carrierCoe38 (m : ℝ) y n :=
  rfl

/-- Monotonicity `‖d‖_{h^1} ≤ ‖d‖_{h^m}` for `m ≥ 1`. -/
theorem hn_one_le_hn38 (m : ℕ) (hm : 1 ≤ m) (d : ℤ → ℂ) (hd : d ∈ seqSobolev38 (m : ℝ)) :
    hn 1 d ≤ hn m d := by
  unfold hn
  apply Real.sqrt_le_sqrt
  have h1 : Summable fun n : ℤ => japaneseBracket n ^ (2 * 1) * ‖d n‖ ^ 2 :=
    summable_hn_of_mem 1 d (mem_h1_of_mem_nat m hm hd)
  refine Summable.tsum_le_tsum (fun n => ?_) h1 (summable_hn_of_mem m d hd)
  have hb : 1 ≤ japaneseBracket n := by
    unfold japaneseBracket
    exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg (n : ℝ)])
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb (by omega)) (sq_nonneg _)

/-! ## The carrier map -/

/-- The nonlinearity `x ↦ 2 ((x * x) * x̃)` (coefficients of `2|u|²u`) as a map of the carrier `h^m`. -/
def nonlinC (m : ℕ) (hm : 1 ≤ m) : SobolevCarrier38 (m : ℝ) → SobolevCarrier38 (m : ℝ) :=
  carrierMap38 (m : ℝ) (m : ℝ) nonlin (nonlin_mem38 m hm)

@[simp] theorem carrierCoe38_nonlinC (m : ℕ) (hm : 1 ≤ m) (x : SobolevCarrier38 (m : ℝ)) :
    carrierCoe38 (m : ℝ) (nonlinC m hm x) = nonlin (carrierCoe38 (m : ℝ) x) := rfl

theorem norm_nonlinC_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : SobolevCarrier38 (m : ℝ),
      ‖nonlinC m hm x‖ ≤ C * hn 1 (carrierCoe38 (m : ℝ) x) ^ 2 * ‖x‖ := by
  obtain ⟨C, hC, hb⟩ := hn_nonlin_le m hm
  refine ⟨C, hC, fun x => ?_⟩
  have := (hb _ (carrierCoe38_mem (m : ℝ) x)).2
  rwa [← hn_coe38 m (nonlinC m hm x), ← hn_coe38 m x]

theorem nonlinC_sub_le (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : SobolevCarrier38 (m : ℝ),
      ‖nonlinC m hm x - nonlinC m hm y‖ ≤
        C * ((hn 1 (carrierCoe38 (m : ℝ) x) + hn 1 (carrierCoe38 (m : ℝ) y)) ^ 2 * ‖x - y‖ +
          (hn 1 (carrierCoe38 (m : ℝ) x) + hn 1 (carrierCoe38 (m : ℝ) y)) * (‖x‖ + ‖y‖) *
            hn 1 (carrierCoe38 (m : ℝ) (x - y))) := by
  obtain ⟨C, hC, hb⟩ := hn_nonlin_sub_le m hm
  refine ⟨C, hC, fun x y => ?_⟩
  have h := hb _ (carrierCoe38_mem (m : ℝ) x) _ (carrierCoe38_mem (m : ℝ) y)
  have e1 : ‖nonlinC m hm x - nonlinC m hm y‖ =
      hn m (fun n => nonlin (carrierCoe38 (m : ℝ) x) n - nonlin (carrierCoe38 (m : ℝ) y) n) :=
    (hn_coe38 m (nonlinC m hm x - nonlinC m hm y)).symm
  have e2 : ‖x - y‖ = hn m (fun n => carrierCoe38 (m : ℝ) x n - carrierCoe38 (m : ℝ) y n) :=
    (hn_coe38 m (x - y)).symm
  rw [e1, e2]
  rwa [hn_coe38 m x, hn_coe38 m y] at h

/-! ## Lipschitz, bounded, continuous -/

theorem nonlinC_bounded (m : ℕ) (hm : 1 ≤ m) (R : ℝ) :
    ∃ B : ℝ, ∀ x ∈ Metric.closedBall (0 : SobolevCarrier38 (m : ℝ)) R, ‖nonlinC m hm x‖ ≤ B := by
  obtain ⟨C, hC, hb⟩ := norm_nonlinC_le m hm
  refine ⟨C * R ^ 3, fun x hx => ?_⟩
  have hxR : ‖x‖ ≤ R := by simpa using hx
  have h0 : 0 ≤ ‖x‖ := norm_nonneg x
  have h1 : hn 1 (carrierCoe38 (m : ℝ) x) ≤ ‖x‖ := by
    rw [← hn_coe38 m x]
    exact hn_one_le_hn38 m hm _ (carrierCoe38_mem (m : ℝ) x)
  have h1' : 0 ≤ hn 1 (carrierCoe38 (m : ℝ) x) := hn_nonneg38 1 _
  calc ‖nonlinC m hm x‖ ≤ C * hn 1 (carrierCoe38 (m : ℝ) x) ^ 2 * ‖x‖ := hb x
    _ ≤ C * R ^ 2 * R := by
      have hh : hn 1 (carrierCoe38 (m : ℝ) x) ≤ R := h1.trans hxR
      have hh2 : hn 1 (carrierCoe38 (m : ℝ) x) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ h1' hh 2
      exact mul_le_mul (mul_le_mul_of_nonneg_left hh2 hC.le) hxR h0 (by positivity)
    _ = C * R ^ 3 := by ring

theorem nonlinC_lipschitzOn (m : ℕ) (hm : 1 ≤ m) (R : ℝ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (nonlinC m hm) (Metric.closedBall 0 R) := by
  obtain ⟨C, hC, hb⟩ := nonlinC_sub_le m hm
  refine ⟨(8 * C * R ^ 2).toNNReal, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hxR : ‖x‖ ≤ R := by simpa using hx
  have hyR : ‖y‖ ≤ R := by simpa using hy
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
  have hR0 : 0 ≤ R := hx0.trans hxR
  have hle1 : ∀ z : SobolevCarrier38 (m : ℝ), hn 1 (carrierCoe38 (m : ℝ) z) ≤ ‖z‖ := fun z => by
    rw [← hn_coe38 m z]
    exact hn_one_le_hn38 m hm _ (carrierCoe38_mem (m : ℝ) z)
  have hnn : ∀ z : SobolevCarrier38 (m : ℝ), 0 ≤ hn 1 (carrierCoe38 (m : ℝ) z) :=
    fun z => hn_nonneg38 1 _
  have hs0 : 0 ≤ hn 1 (carrierCoe38 (m : ℝ) x) + hn 1 (carrierCoe38 (m : ℝ) y) :=
    add_nonneg (hnn x) (hnn y)
  have hs : hn 1 (carrierCoe38 (m : ℝ) x) + hn 1 (carrierCoe38 (m : ℝ) y) ≤ 2 * R := by
    linarith [hle1 x, hle1 y]
  have hs2 : (hn 1 (carrierCoe38 (m : ℝ) x) + hn 1 (carrierCoe38 (m : ℝ) y)) ^ 2 ≤ (2 * R) ^ 2 :=
    pow_le_pow_left₀ hs0 hs 2
  have hxy : ‖x‖ + ‖y‖ ≤ 2 * R := by linarith
  have hd1 : hn 1 (carrierCoe38 (m : ℝ) (x - y)) ≤ ‖x - y‖ := hle1 _
  have hd0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hdn := hnn (x - y)
  have hprod : (hn 1 (carrierCoe38 (m : ℝ) x) + hn 1 (carrierCoe38 (m : ℝ) y)) * (‖x‖ + ‖y‖) ≤
      (2 * R) * (2 * R) := mul_le_mul hs hxy (by positivity) (by positivity)
  have hmain' := hb x y
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
  calc ‖nonlinC m hm x - nonlinC m hm y‖ ≤ C * ((hn 1 (carrierCoe38 (m : ℝ) x) +
          hn 1 (carrierCoe38 (m : ℝ) y)) ^ 2 * ‖x - y‖ +
          (hn 1 (carrierCoe38 (m : ℝ) x) + hn 1 (carrierCoe38 (m : ℝ) y)) * (‖x‖ + ‖y‖) *
            hn 1 (carrierCoe38 (m : ℝ) (x - y))) := hmain'
    _ ≤ C * ((2 * R) ^ 2 * ‖x - y‖ + (2 * R) * (2 * R) * ‖x - y‖) := by
      refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC.le
      · exact mul_le_mul_of_nonneg_right hs2 hd0
      · exact mul_le_mul hprod hd1 hdn (by positivity)
    _ = 8 * C * R ^ 2 * ‖x - y‖ := by ring

theorem continuous_nonlinC (m : ℕ) (hm : 1 ≤ m) : Continuous (nonlinC m hm) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨K, hK⟩ := nonlinC_lipschitzOn m hm (‖x‖ + 1)
  have hmem : Metric.closedBall (0 : SobolevCarrier38 (m : ℝ)) (‖x‖ + 1) ∈ nhds x := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x one_pos) fun y hy => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_sub_norm_le y x
    linarith
  exact hK.continuousOn.continuousAt hmem

/-! ## Reflection covariance and phase gauge -/

theorem conv_refl_refl38 (f g : ℤ → ℂ) (n : ℤ) :
    conv (refl f) (refl g) n = conv f g (-n) := by
  unfold conv
  rw [← (Equiv.neg ℤ).tsum_eq (fun b => f b * g (-n - b))]
  refine tsum_congr fun a => ?_
  have e : -(n - a) = -n - -a := by ring
  simp only [refl, Equiv.neg_apply, e]
  ring

theorem conv_rev_refl38 (P Q : ℤ → ℂ) (n : ℤ) :
    conv (fun k => P (-k)) (refl Q) n = - conv P Q (-n) := by
  unfold conv
  rw [← (Equiv.neg ℤ).tsum_eq (fun b => P b * Q (-n - b)), ← tsum_neg]
  refine tsum_congr fun a => ?_
  have e : -(n - a) = -n - -a := by ring
  simp only [refl, Equiv.neg_apply, e]
  ring

theorem cstar_refl38 (x : ℤ → ℂ) : cstar (refl x) = refl (cstar x) := by
  funext n
  simp [cstar, refl]

/-- Reflection covariance of the nonlinearity: `N(𝓕 x) = 𝓕 N(x)`, `(𝓕 x)_n = -x_{-n}`. -/
theorem nonlin_refl (x : ℤ → ℂ) : nonlin (refl x) = refl (nonlin x) := by
  funext n
  have h1 : conv (refl x) (refl x) = fun k => conv x x (-k) := funext (conv_refl_refl38 x x)
  simp only [nonlin, h1, cstar_refl38, conv_rev_refl38, refl]
  ring

/-- Phase gauge covariance: `N(e^{iθ} x) = e^{iθ} N(x)`. -/
theorem nonlin_phase_gauge (θ : ℝ) (x : ℤ → ℂ) :
    nonlin (fun n => Complex.exp (θ * Complex.I) * x n) =
      fun n => Complex.exp (θ * Complex.I) * nonlin x n := by
  set c : ℂ := Complex.exp (θ * Complex.I) with hc
  have hcc : c * conj c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc, Complex.norm_exp_ofReal_mul_I]
    simp
  have h : (fun n => c * x n) = c • x := rfl
  funext n
  rw [h]
  simp only [nonlin, conv_smul_left, conv_smul_right, cstar_smul, Pi.smul_apply, smul_eq_mul]
  linear_combination (2 * conv (conv x x) (cstar x) n * c) * hcc

/-! ## Probes -/

theorem nonlin_zero38 : nonlin (0 : ℤ → ℂ) = 0 := by
  funext k
  simp [nonlin, conv]

theorem nonlinC_zero (m : ℕ) (hm : 1 ≤ m) : nonlinC m hm 0 = 0 := by
  apply carrierExt38
  have h0 : carrierCoe38 (m : ℝ) (0 : SobolevCarrier38 (m : ℝ)) = 0 := rfl
  rw [carrierCoe38_nonlinC, h0, nonlin_zero38]

theorem single_mem_seqSobolev38 (r : ℝ) (k : ℤ) (a : ℂ) : (Pi.single k a : ℤ → ℂ) ∈ seqSobolev38 r :=
  finiteSupport_mem_seqSobolev38 r _ ((Set.finite_singleton k).subset fun n hn => by
    by_contra h
    exact hn (by simp [show n ≠ k from h]))

/-- Plane-wave probe on the carrier: `N(a δ_k) = 2|a|² a δ_k`. -/
theorem nonlinC_planeWave (m : ℕ) (hm : 1 ≤ m) (k : ℤ) (a : ℂ) :
    carrierCoe38 (m : ℝ) (nonlinC m hm (carrierMk38 (m : ℝ) (Pi.single k a)
      (single_mem_seqSobolev38 _ k a))) = Pi.single k (2 * ((‖a‖ ^ 2 : ℝ) : ℂ) * a) := by
  rw [carrierCoe38_nonlinC, carrierCoe38_mk]
  exact nonlin_single k a

/-- Probe: reflection of a plane wave is the plane wave at `-k` with amplitude `-a`, and `nonlin_refl`
agrees with the explicit plane-wave formula `nonlin_single`. -/
theorem refl_single38 (k : ℤ) (a : ℂ) : refl (Pi.single k a) = Pi.single (-k) (-a) := by
  funext n
  by_cases h : n = -k
  · subst h; simp [refl]
  · have h' : -n ≠ k := fun e => h (by rw [← e]; ring)
    simp [refl, h, h']

theorem nonlin_refl_single_probe (k : ℤ) (a : ℂ) :
    nonlin (Pi.single (-k) (-a)) = Pi.single (-k) (2 * ((‖a‖ ^ 2 : ℝ) : ℂ) * (-a)) := by
  rw [← refl_single38, nonlin_refl, nonlin_single, refl_single38]
  simp

end NlsGge.NLS38
