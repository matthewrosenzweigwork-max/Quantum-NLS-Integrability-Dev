import NlsGge.Hierarchy.ALPlaneWaveGap38
import NlsGge.Hierarchy.ALFullEnergy38
import NlsGge.Hierarchy.FullEnergySpectralIdentification38
import NlsGge.Weights.Regularity

set_option autoImplicit false
noncomputable section

namespace NlsGge.AblowitzLadik

open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.HierarchyRiccati.Core MeasureTheory

/-! ### Continuum side: ZS monodromy of the plane wave -/

/-- Solutions of `c' = μ d`, `d' = c` with `c(0)=1`, `d(0)=0`, `c(1)=cosh σ` for `σ² = μ`. -/
theorem cd_exists38 (σ : ℂ) :
    ∃ c d : ℝ → ℂ, (∀ x, HasDerivAt c (σ ^ 2 * d x) x ∧ HasDerivAt d (c x) x) ∧
      c 0 = 1 ∧ d 0 = 0 ∧ c 1 = Complex.cosh σ := by
  by_cases hσ : σ = 0
  · subst hσ
    refine ⟨fun _ => 1, fun x => (x : ℂ), fun x => ⟨?_, ?_⟩, by simp, by simp, by simp⟩
    · simpa using hasDerivAt_const x (1 : ℂ)
    · simpa using (hasDerivAt_id (x : ℂ)).comp_ofReal
  · refine ⟨fun x => Complex.cosh (σ * x), fun x => Complex.sinh (σ * x) / σ, fun x => ⟨?_, ?_⟩,
      by simp, by simp, by simp⟩
    · have h1 : HasDerivAt (fun y : ℂ => Complex.cosh (σ * y)) (Complex.sinh (σ * x) * σ) (x : ℂ) := by
        simpa using ((hasDerivAt_id (x : ℂ)).const_mul σ).ccosh
      have h2 := h1.comp_ofReal
      convert h2 using 1
      field_simp
    · have h1 : HasDerivAt (fun y : ℂ => Complex.sinh (σ * y) / σ) (Complex.cosh (σ * x)) (x : ℂ) := by
        have := (((hasDerivAt_id (x : ℂ)).const_mul σ).csinh).div_const σ
        simpa [id, mul_div_assoc, mul_div_cancel_right₀ _ hσ] using this
      exact h1.comp_ofReal

theorem hasDerivAt_cexpMulReal38 (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (w * (y : ℂ))) (w * Complex.exp (w * (x : ℂ))) x := by
  have h1 : HasDerivAt (fun y : ℂ => Complex.exp (w * y)) (Complex.exp (w * (x : ℂ)) * w) (x : ℂ) := by
    simpa using ((hasDerivAt_id (x : ℂ)).const_mul w).cexp
  have := h1.comp_ofReal
  convert this using 1
  ring

/-- The plane wave `U(x) = t e^{2πikx}` as a function on `ℝ`. -/
def planeU38 (k : ℤ) (t : ℝ) (x : ℝ) : ℂ :=
  (t : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ))

/-- Explicit fundamental matrix of the ZS system with plane-wave potential. -/
def planeFund38 (k : ℤ) (t : ℝ) (a : ℂ) (c d : ℝ → ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (Complex.I * Real.pi * k * x) * (c x - Complex.I * a * d x),
     Complex.exp (Complex.I * Real.pi * k * x) * (Complex.I * t * d x);
     Complex.exp (-(Complex.I * Real.pi * k) * x) * (-(Complex.I * t) * d x),
     Complex.exp (-(Complex.I * Real.pi * k) * x) * (c x + Complex.I * a * d x)]

theorem planeFund_deriv38 (k : ℤ) (t : ℝ) (z a σ : ℂ) (ha : a = z + Real.pi * k)
    (hσ : σ ^ 2 = (t : ℂ) ^ 2 - a ^ 2) (c d : ℝ → ℂ)
    (hcd : ∀ x, HasDerivAt c (σ ^ 2 * d x) x ∧ HasDerivAt d (c x) x) (x : ℝ) :
    HasDerivAt (planeFund38 k t a c d) (zsCoefficientComplex (planeU38 k t) z x * planeFund38 k t a c d x) x := by
  set e := Complex.exp (Complex.I * Real.pi * k * x) with he
  set E := Complex.exp (-(Complex.I * Real.pi * k) * x) with hE
  have heE : e * E = 1 := by
    rw [he, hE, ← Complex.exp_add]; simp
  have hU : planeU38 k t x = (t : ℂ) * (e * e) := by
    unfold planeU38; rw [he, ← Complex.exp_add]; congr 2; ring
  have hUs : star (planeU38 k t x) = (t : ℂ) * (E * E) := by
    rw [hU, hE, ← Complex.exp_add]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj,
      ← Complex.exp_add]
    congr 2
    simp [Complex.conj_ofReal]
  have de := hasDerivAt_cexpMulReal38 (Complex.I * Real.pi * k) x
  have dE := hasDerivAt_cexpMulReal38 (-(Complex.I * Real.pi * k)) x
  have dc := (hcd x).1
  have dd := (hcd x).2
  have hE2 : Complex.exp (-(Complex.I * Real.pi * k * x)) = E := by rw [hE, neg_mul]
  have hE3 : Complex.exp (-(Complex.I * Real.pi * k) * x) = E := hE.symm
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  fin_cases i <;> fin_cases j
  · have h := de.mul (dc.sub (dd.const_mul (Complex.I * a)))
    refine h.congr_deriv ?_
    simp [planeFund38, zsCoefficientComplex, Matrix.mul_apply, Fin.sum_univ_two, hU, ← he]
    simp only [hE2]
    linear_combination (norm := (ring_nf; try simp only [Complex.I_sq]; try ring_nf)) (e*d x)*hσ + (-(e*c x*Complex.I) - e*a*d x)*ha + (-((t:ℂ)^2*e*d x))*heE
  · have h := de.mul (dd.const_mul (Complex.I * t))
    refine h.congr_deriv ?_
    simp [planeFund38, zsCoefficientComplex, Matrix.mul_apply, Fin.sum_univ_two, hU, ← he]
    simp only [hE2]
    linear_combination (norm := (ring_nf; try simp only [Complex.I_sq]; try ring_nf)) (e*(t:ℂ)*d x)*ha + (e*((t:ℂ)*d x*a - Complex.I*t*c x))*heE
  · have h := dE.mul (dd.const_mul (-(Complex.I * t)))
    refine h.congr_deriv ?_
    simp [planeFund38, zsCoefficientComplex, Matrix.mul_apply, Fin.sum_univ_two, hUs, ← he]
    simp only [hE2]
    linear_combination (norm := (ring_nf; try simp only [Complex.I_sq]; try ring_nf)) (E*(t:ℂ)*d x)*ha + (E*((t:ℂ)*a*d x + Complex.I*t*c x))*heE
  · have h := dE.mul (dc.add (dd.const_mul (Complex.I * a)))
    refine h.congr_deriv ?_
    simp [planeFund38, zsCoefficientComplex, Matrix.mul_apply, Fin.sum_univ_two, hUs, ← he]
    simp only [hE2]
    linear_combination (norm := (ring_nf; try simp only [Complex.I_sq]; try ring_nf)) (E*Complex.I*c x - E*a*d x)*ha + (E*d x)*hσ + (-(E*(t:ℂ)^2*d x))*heE

theorem continuous_planeU38 (k : ℤ) (t : ℝ) : Continuous (planeU38 k t) := by
  unfold planeU38; fun_prop

theorem planeFund_zero38 (k : ℤ) (t : ℝ) (a : ℂ) (c d : ℝ → ℂ) (hc : c 0 = 1) (hd : d 0 = 0) :
    planeFund38 k t a c d 0 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [planeFund38, hc, hd]

theorem planeFund_trace38 (k : ℤ) (t : ℝ) (a : ℂ) (c d : ℝ → ℂ) :
    Matrix.trace (planeFund38 k t a c d 1) = 2 * (-1 : ℂ) ^ k * c 1 := by
  have h1 : Complex.exp (Complex.I * Real.pi * k * ((1 : ℝ) : ℂ)) = (-1 : ℂ) ^ k := by
    have : Complex.I * Real.pi * k * ((1 : ℝ) : ℂ) = (k : ℂ) * (Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have h2 : Complex.exp (-(Complex.I * Real.pi * k) * ((1 : ℝ) : ℂ)) = (-1 : ℂ) ^ k := by
    have : -(Complex.I * Real.pi * k) * ((1 : ℝ) : ℂ) = (-k : ℤ) * (Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul, Complex.exp_pi_mul_I, zpow_neg, ← inv_zpow, inv_neg_one]
  simp only [planeFund38, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, h1, h2]
  ring

/-- The Dyson fundamental matrix of the plane-wave ZS system at time one. -/
theorem planeDyson38 (k : ℤ) (t : ℝ) (z a σ : ℂ) (ha : a = z + Real.pi * k)
    (hσ : σ ^ 2 = (t : ℂ) ^ 2 - a ^ 2) (c d : ℝ → ℂ)
    (hcd : ∀ x, HasDerivAt c (σ ^ 2 * d x) x ∧ HasDerivAt d (c x) x) (hc : c 0 = 1) (hd : d 0 = 0) :
    actualComplexZsDysonTsum (planeU38 k t) z 1 = planeFund38 k t a c d 1 := by
  have hU : ContinuousOn (planeU38 k t) (Set.Icc (0:ℝ) 2) := (continuous_planeU38 k t).continuousOn
  ext i j
  have key := actualComplexZsDysonTsum_mulVec_eq_of_solution_E02_38 (planeU38 k t) z hU
    (fun x => fun i => planeFund38 k t a c d x i j) (fun x _ => by
      refine (hasDerivAt_pi.2 fun i => ?_).hasDerivWithinAt
      have h := planeFund_deriv38 k t z a σ ha hσ c d hcd x
      have h2 := (hasDerivAt_pi.1 (hasDerivAt_pi.1 h i) j)
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h2 ) 1 (by norm_num)
  have e0 : (fun i => planeFund38 k t a c d 0 i j) = Pi.single j 1 := by
    rw [planeFund_zero38 k t a c d hc hd]
    ext i; simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [e0] at key
  have := congrFun key i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- The continuum plane-wave gap height `√(t² - a²)₊`. -/
def planeGapCont38 (t a : ℝ) : ℝ := Real.sqrt (max 0 (t ^ 2 - a ^ 2))

/-- Half trace of the plane-wave ZS monodromy at real `λ`: `(-1)^k cosh σ`, `σ² = t² - (λ+πk)²`;
its gap height is `√(t² - (λ+πk)²)₊`. -/
theorem planeGapHeight_real38 (k : ℤ) (t : ℝ) (lam : ℝ) :
    Real.arcosh (max 1 ‖Matrix.trace (actualComplexZsDysonTsum (planeU38 k t) (lam : ℂ) 1) / 2‖) =
      planeGapCont38 t (lam + Real.pi * k) := by
  set μ : ℝ := t ^ 2 - (lam + Real.pi * k) ^ 2 with hμ
  have ha : ((lam + Real.pi * k : ℝ) : ℂ) = (lam : ℂ) + Real.pi * k := by push_cast; ring
  have main : ∀ σ : ℂ, σ ^ 2 = (μ : ℂ) →
      ‖Matrix.trace (actualComplexZsDysonTsum (planeU38 k t) (lam : ℂ) 1) / 2‖ =
        ‖Complex.cosh σ‖ := by
    intro σ hσ
    obtain ⟨c, d, hcd, hc, hd, h1⟩ := cd_exists38 σ
    have hσ' : σ ^ 2 = (t : ℂ) ^ 2 - (((lam + Real.pi * k : ℝ) : ℂ)) ^ 2 := by
      rw [hσ, hμ]; push_cast; ring
    rw [planeDyson38 k t (lam : ℂ) _ σ ha hσ' c d hcd hc hd, planeFund_trace38, h1,
      norm_div, norm_mul, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow]
    simp
  unfold planeGapCont38
  rcases le_or_gt 0 μ with h | h
  · have hs : ((Real.sqrt μ : ℝ) : ℂ) ^ 2 = (μ : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt h]
    rw [main _ hs, ← Complex.ofReal_cosh, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.cosh_pos _), max_eq_right (Real.one_le_cosh _), ← hμ, max_eq_right h,
      Real.arcosh_cosh (Real.sqrt_nonneg _)]
  · have hs : (Complex.I * ((Real.sqrt (-μ) : ℝ) : ℂ)) ^ 2 = (μ : ℂ) := by
      rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by linarith), Complex.I_sq]; push_cast; ring
    rw [main _ hs, mul_comm, Complex.cosh_mul_I, ← Complex.ofReal_cos, Complex.norm_real,
      Real.norm_eq_abs, max_eq_left (Real.abs_cos_le_one _), Real.arcosh_zero,
      max_eq_left h.le, Real.sqrt_zero]

/-- The coefficient vector of `t e^{2πikx}` in the finite plane of cutoff `N`. -/
def planeWaveCoeff38 (N : ℕ) (k : ℤ) (t : ℝ) : FourierPlane N :=
  fun i => if modeIndex N i = k then (t : ℂ) else 0

theorem planeReal_planeWave38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t : ℝ) :
    planeReal N (planeWaveCoeff38 N k t) = planeU38 k t := by
  obtain ⟨i0, hi0⟩ := modeIndex_covers N k (by omega) (by omega)
  funext x
  rw [planeReal_apply_exp38, Finset.sum_eq_single i0]
  · simp [planeWaveCoeff38, hi0, planeU38]
  · intro i _ hi
    have : modeIndex N i ≠ k := fun h => hi (modeIndex_injective N (h.trans hi0.symm))
    simp [planeWaveCoeff38, this]
  · simp

theorem actualGapHeight_planeWave38 (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) (t : ℝ) (lam : ℝ) :
    actualGapHeightE02_38 (planeL2 N (planeWaveCoeff38 N k t)) lam =
      planeGapCont38 t (lam + Real.pi * k) := by
  rw [← planeGapHeight_real38 k t lam]
  unfold actualGapHeightE02_38 actualPhysicalUnitHalfTrace32
  rw [actualComplexZsDysonTsum_eq_of_ae_eq _ (planeReal N (planeWaveCoeff38 N k t)) (lam : ℂ)
    (planeReal_cover_ae38 N (planeWaveCoeff38 N k t)) 1 (by norm_num),
    planeReal_planeWave38 N k hk t]

/-- Continuum side: the complete energy of the plane wave `t e^{2πikx}`,
`E_W = (2/π) ∫ W(2λ) √(t² - (λ+πk)²)₊ dλ`. -/
theorem planeEnergy_cont38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) (k : ℤ)
    (hk : k.natAbs ≤ N) (t : ℝ) :
    fullEnergy38 c N (planeWaveCoeff38 N k t) = (2 / Real.pi) *
      ∫ lam : ℝ, NlsGge.Weights.weight c.val (2 * lam) * planeGapCont38 t (lam + Real.pi * k) := by
  rw [(fullEnergy38_eq_spectral c N (planeWaveCoeff38 N k t)).2]
  simp_rw [actualGapHeight_planeWave38 N k hk t]

/-! ### Lattice side -/

theorem alPlaneWave_isAL38 (L : ℕ) [NeZero L] (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t / L < 1) :
    IsALField38 (alPlaneWave38 L k t) := by
  intro j
  unfold alPlaneWave38
  have : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((j.val : ℕ) : ℂ) / (L : ℂ) =
      ((2 * Real.pi * k * j.val / L : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  exact ht1

/-- The lattice integrand of `D:eq:planeconsistency` in the variable `μ = λ - πk`:
`W(2 sin(h(μ+πk))/h) · h⁻¹ arcosh (max 1 (|cos(hμ)|/√(1-h²t²)))`. -/
def latF38 (W : ℝ → ℝ) (k : ℤ) (t h : ℝ) (μ : ℝ) : ℝ :=
  W (2 * Real.sin (h * (μ + Real.pi * k)) / h) *
    (h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * μ)| / Real.sqrt (1 - h ^ 2 * t ^ 2))))

/-- The lattice energy of the plane wave as an integral over `ℝ` in `μ = λ - πk`. -/
theorem alEnergy_plane_integral38 {lo up : ℝ} (c : BoundedCoefficients lo up) (L : ℕ) [NeZero L]
    (hodd : Odd L) (k : ℤ) {t h : ℝ} (hh : h = (L : ℝ)⁻¹) (ht0 : 0 ≤ t) (hht : h * t < 1) :
    alEnergy38 c.val h (alPlaneWave38 L k t) = (2 / Real.pi) *
      ∫ μ : ℝ, Set.indicator {μ : ℝ | μ + Real.pi * k ∈ Set.Ioc (-(Real.pi / (2 * h))) (Real.pi / (2 * h))}
        (latF38 (NlsGge.Weights.weight c.val) k t h) μ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hh0 : 0 < h := by rw [hh]; positivity
  have hh1 : h = 1 / (L : ℝ) := by rw [hh]; simp
  have ht1 : t / L < 1 := by
    have : t / (L : ℝ) = h * t := by rw [hh]; ring
    rw [this]; exact hht
  rw [alEnergy38_spectral c.property (alPlaneWave_isAL38 L k ht0 ht1) hodd hh]
  congr 1
  have hab : -(Real.pi / (2 * h)) ≤ Real.pi / (2 * h) := by
    have : 0 ≤ Real.pi / (2 * h) := by positivity
    linarith
  have e1 : ∀ lam : ℝ, NlsGge.Weights.weight c.val (2 * Real.sin (h * lam) / h) *
      alVh38 h (alPlaneWave38 L k t) lam =
      latF38 (NlsGge.Weights.weight c.val) k t h (lam - Real.pi * k) := by
    intro lam
    unfold alVh38 latF38
    rw [sub_add_cancel, alPlaneWave_gap38 L k hh1 ht0 hht lam]
    congr 4
    ring_nf
  simp_rw [e1]
  rw [intervalIntegral.integral_of_le hab, ← MeasureTheory.integral_indicator measurableSet_Ioc]
  rw [← MeasureTheory.integral_add_right_eq_self _ (Real.pi * k)]
  congr 1
  funext μ
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, add_sub_cancel_right]

/-! ### Arsinh form of the lattice gap and its limit -/

/-- `arcosh (max 1 (|cos x|/s)) = arsinh (√(max 0 (h²t² - sin²x))/s)` for `s = √(1-h²t²)`. -/
theorem arcosh_max_eq_arsinh38 (x ht : ℝ) (hht : ht ^ 2 < 1) :
    Real.arcosh (max 1 (|Real.cos x| / Real.sqrt (1 - ht ^ 2))) =
      Real.arsinh (Real.sqrt (max 0 (ht ^ 2 - Real.sin x ^ 2)) / Real.sqrt (1 - ht ^ 2)) := by
  have hs0 : 0 < 1 - ht ^ 2 := by linarith
  have hs : 0 < Real.sqrt (1 - ht ^ 2) := Real.sqrt_pos.mpr hs0
  have hs2 : Real.sqrt (1 - ht ^ 2) ^ 2 = 1 - ht ^ 2 := Real.sq_sqrt hs0.le
  have hcs : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  by_cases hw : ht ^ 2 - Real.sin x ^ 2 ≤ 0
  · have hr : |Real.cos x| / Real.sqrt (1 - ht ^ 2) ≤ 1 := by
      rw [div_le_one hs]
      exact Real.abs_le_sqrt (by rw [hcs]; linarith)
    rw [max_eq_left hr, max_eq_left hw]; simp
  · rw [not_le] at hw
    have hcpos : 0 < |Real.cos x| := by
      apply abs_pos.mpr
      intro h0
      rw [h0] at hcs
      nlinarith
    have hlt : Real.sqrt (1 - ht ^ 2) < |Real.cos x| := by
      rw [Real.sqrt_lt' hcpos, sq_abs, hcs]; linarith
    have hr : 1 < |Real.cos x| / Real.sqrt (1 - ht ^ 2) := by rw [lt_div_iff₀ hs]; linarith
    rw [max_eq_right hr.le, max_eq_right hw.le]
    set r := |Real.cos x| / Real.sqrt (1 - ht ^ 2) with hr_def
    have hr2 : r ^ 2 - 1 = (ht ^ 2 - Real.sin x ^ 2) / Real.sqrt (1 - ht ^ 2) ^ 2 := by
      rw [hr_def, div_pow, sq_abs, hcs, hs2]
      field_simp
      ring
    have := Real.sinh_arcosh hr.le
    rw [← Real.arsinh_sinh (Real.arcosh r), this, hr2, Real.sqrt_div hw.le, Real.sqrt_sq hs.le]

/-- `y_h(μ) = √(t² - (sin(hμ)/h)²)₊ / √(1 - h²t²)`; the gap height is `h⁻¹ arsinh (h y_h)`. -/
def yL38 (t h μ : ℝ) : ℝ :=
  Real.sqrt (max 0 (t ^ 2 - (Real.sin (h * μ) / h) ^ 2)) / Real.sqrt (1 - h ^ 2 * t ^ 2)

/-- `A(x) = arsinh x / x`, with `A(0) = 1`. -/
def A38 : ℝ → ℝ := Function.update (fun x : ℝ => x⁻¹ * Real.arsinh x) 0 1

theorem gapL_arsinh38 {t h : ℝ} (μ : ℝ) (hh : 0 < h) (ht0 : 0 ≤ t) (hht : h * t < 1) :
    h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * μ)| / Real.sqrt (1 - h ^ 2 * t ^ 2))) =
      h⁻¹ * Real.arsinh (h * yL38 t h μ) := by
  have hht2 : (h * t) ^ 2 < 1 := by nlinarith [mul_nonneg hh.le ht0]
  have e1 := arcosh_max_eq_arsinh38 (h * μ) (h * t) hht2
  rw [mul_pow] at e1
  rw [e1]
  have hy : h * yL38 t h μ = Real.sqrt (max 0 (h ^ 2 * t ^ 2 - Real.sin (h * μ) ^ 2)) /
      Real.sqrt (1 - h ^ 2 * t ^ 2) := by
    unfold yL38
    rw [← mul_div_assoc]
    congr 1
    have : max 0 (h ^ 2 * t ^ 2 - Real.sin (h * μ) ^ 2) =
        h ^ 2 * max 0 (t ^ 2 - (Real.sin (h * μ) / h) ^ 2) := by
      rw [mul_max_of_nonneg _ _ (sq_nonneg h), mul_zero]
      congr 1
      field_simp
    rw [this, Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le]
  rw [hy]

theorem gapL_eq38 {t h : ℝ} (μ : ℝ) (hh : 0 < h) (ht0 : 0 ≤ t) (hht : h * t < 1) :
    h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * μ)| / Real.sqrt (1 - h ^ 2 * t ^ 2))) =
      yL38 t h μ * A38 (h * yL38 t h μ) := by
  rw [gapL_arsinh38 μ hh ht0 hht]
  by_cases h0 : h * yL38 t h μ = 0
  · have : yL38 t h μ = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd h1 hh.ne'
      · exact h1
    rw [h0, this]; simp
  · unfold A38
    rw [Function.update_of_ne h0]
    have hy0 : yL38 t h μ ≠ 0 := fun h' => h0 (by rw [h', mul_zero])
    field_simp

open Filter Topology

theorem tendsto_sin_div38 (μ : ℝ) :
    Tendsto (fun h : ℝ => Real.sin (h * μ) / h) (𝓝[>] 0) (𝓝 μ) := by
  have hd : HasDerivAt (fun h : ℝ => Real.sin (h * μ)) μ 0 := by
    have := (Real.hasDerivAt_sin (0 * μ)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).mul_const μ)
    simp only [zero_mul, Real.cos_zero, one_mul] at this
    exact this
  have := (hasDerivAt_iff_tendsto_slope_zero.mp hd).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  refine this.congr fun h => ?_
  simp [div_eq_inv_mul]

theorem continuousAt_A38 : ContinuousAt A38 0 := by
  unfold A38
  rw [continuousAt_update_same]
  have hd := Real.hasDerivAt_arsinh 0
  have := hasDerivAt_iff_tendsto_slope_zero.mp hd
  simpa [div_eq_inv_mul] using this

theorem tendsto_yL38 (t μ : ℝ) :
    Tendsto (fun h : ℝ => yL38 t h μ) (𝓝[>] 0) (𝓝 (Real.sqrt (max 0 (t ^ 2 - μ ^ 2)))) := by
  unfold yL38
  have h1 : Tendsto (fun h : ℝ => Real.sin (h * μ) / h) (𝓝[>] 0) (𝓝 μ) := tendsto_sin_div38 μ
  have h2 : Tendsto (fun h : ℝ => 1 - h ^ 2 * t ^ 2) (𝓝[>] 0) (𝓝 1) := by
    have : Tendsto (fun h : ℝ => 1 - h ^ 2 * t ^ 2) (𝓝 0) (𝓝 (1 - 0 ^ 2 * t ^ 2)) := by
      apply Continuous.tendsto; fun_prop
    simpa using this.mono_left nhdsWithin_le_nhds
  have h3 := (Real.continuous_sqrt.tendsto _).comp h2
  have h4 := (Real.continuous_sqrt.tendsto _).comp
    ((tendsto_const_nhds (x := (0 : ℝ))).max (((tendsto_const_nhds (x := t ^ 2)).sub (h1.pow 2))))
  have h5 := h4.div h3 (by simp)
  simp only [Real.sqrt_one, div_one] at h5
  exact h5

theorem tendsto_gapL38 (t μ : ℝ) :
    Tendsto (fun h : ℝ => yL38 t h μ * A38 (h * yL38 t h μ)) (𝓝[>] 0)
      (𝓝 (planeGapCont38 t μ)) := by
  have hy := tendsto_yL38 t μ
  have hA : Tendsto (fun h : ℝ => A38 (h * yL38 t h μ)) (𝓝[>] 0) (𝓝 1) := by
    have h0 : Tendsto (fun h : ℝ => h * yL38 t h μ) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds (f := fun h : ℝ => h) (a := (0:ℝ))
        (s := Set.Ioi 0) tendsto_id).mul hy
    have : A38 0 = 1 := by simp [A38]
    have h6 := continuousAt_A38.tendsto.comp h0
    rw [this] at h6
    exact h6
  simpa [planeGapCont38] using hy.mul hA

/-! ### Uniform majorant on the fixed interval `[-2t, 2t]` -/

theorem sin_core38 (u ht : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 5 * Real.pi / 6) (hht : ht ≤ 1 / 2)
    (hs : Real.sin u < ht) : u ≤ Real.pi / 2 * ht := by
  have hpi := Real.pi_pos
  by_cases h1 : u ≤ Real.pi / 2
  · have := Real.mul_le_sin hu0 h1
    have h2 : 2 / Real.pi * u < ht := lt_of_le_of_lt this hs
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpi] at h2
    nlinarith
  · exfalso
    rw [not_le] at h1
    have : Real.sin (Real.pi / 6) ≤ Real.sin (Real.pi - u) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    rw [Real.sin_pi_sub, Real.sin_pi_div_six] at this
    linarith

theorem support38 (t h μ : ℝ) (k : ℤ) (hh : 0 < h) (ht0 : 0 ≤ t) (hht : h * t ≤ 1 / 2)
    (hk : |(k : ℝ)| * h ≤ 1 / 3) (hS : |h * (μ + Real.pi * k)| ≤ Real.pi / 2)
    (hy : yL38 t h μ ≠ 0) : |μ| ≤ 2 * t := by
  have hpi := Real.pi_pos
  have hsq : 0 < t ^ 2 - (Real.sin (h * μ) / h) ^ 2 := by
    by_contra hcon
    apply hy
    unfold yL38
    rw [max_eq_left (not_lt.mp hcon), Real.sqrt_zero, zero_div]
  have hlt : |Real.sin (h * μ)| < h * t := by
    have : |Real.sin (h * μ) / h| < t := by
      apply abs_lt_of_sq_lt_sq (by nlinarith) ht0
    rw [abs_div, abs_of_pos hh, div_lt_iff₀ hh] at this
    linarith
  have hx : |h * μ| ≤ 5 * Real.pi / 6 := by
    have e : h * μ = h * (μ + Real.pi * k) - Real.pi * k * h := by ring
    have h1 : |Real.pi * k * h| ≤ Real.pi / 3 := by
      rw [abs_mul, abs_mul, abs_of_pos hpi, abs_of_pos hh]
      nlinarith
    calc |h * μ| = |h * (μ + Real.pi * k) - Real.pi * k * h| := by rw [← e]
      _ ≤ |h * (μ + Real.pi * k)| + |Real.pi * k * h| := abs_sub _ _
      _ ≤ 5 * Real.pi / 6 := by linarith
  have hcore : |h * μ| ≤ Real.pi / 2 * (h * t) := by
    apply sin_core38 _ _ (abs_nonneg _) hx hht
    rcases le_total 0 (h * μ) with h0 | h0
    · rw [abs_of_nonneg h0]
      have : 0 ≤ Real.sin (h * μ) := Real.sin_nonneg_of_nonneg_of_le_pi h0
        (by have := abs_of_nonneg h0; linarith)
      rwa [abs_of_nonneg this] at hlt
    · rw [abs_of_nonpos h0, Real.sin_neg]
      have : Real.sin (h * μ) ≤ 0 := Real.sin_nonpos_of_nonpos_of_neg_pi_le h0
        (by have := abs_of_nonpos h0; linarith)
      rwa [abs_of_nonpos this] at hlt
  rw [abs_mul, abs_of_pos hh] at hcore
  have : |μ| ≤ Real.pi / 2 * t := by nlinarith
  nlinarith [Real.pi_lt_four]

theorem arsinh_le_self38 {x : ℝ} (hx : 0 ≤ x) : Real.arsinh x ≤ x := by
  have h0 : 0 ≤ Real.arsinh x := Real.arsinh_nonneg_iff.mpr hx
  have := Real.self_le_sinh_iff.mpr h0
  rwa [Real.sinh_arsinh] at this

theorem yL_nonneg38 (t h μ : ℝ) : 0 ≤ yL38 t h μ := by
  unfold yL38; positivity

theorem yL_le38 {t h : ℝ} (μ : ℝ) (ht0 : 0 ≤ t) (hht : h * t ≤ 1 / 2) (hh : 0 < h) :
    yL38 t h μ ≤ 2 * t := by
  unfold yL38
  have hs : 1 / 2 ≤ Real.sqrt (1 - h ^ 2 * t ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [mul_nonneg hh.le ht0]
  have hnum : Real.sqrt (max 0 (t ^ 2 - (Real.sin (h * μ) / h) ^ 2)) ≤ t := by
    calc _ ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt (by
          apply max_le (sq_nonneg t); nlinarith [sq_nonneg (Real.sin (h * μ) / h)])
      _ = t := Real.sqrt_sq ht0
  rw [div_le_iff₀ (by linarith)]
  nlinarith [Real.sqrt_nonneg (max 0 (t ^ 2 - (Real.sin (h * μ) / h) ^ 2))]

theorem gapL_bounds38 {t h : ℝ} (μ : ℝ) (hh : 0 < h) (ht0 : 0 ≤ t) (hht : h * t ≤ 1 / 2) :
    0 ≤ h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * μ)| / Real.sqrt (1 - h ^ 2 * t ^ 2))) ∧
    h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * μ)| / Real.sqrt (1 - h ^ 2 * t ^ 2))) ≤ 2 * t := by
  have hht1 : h * t < 1 := by linarith
  rw [gapL_arsinh38 μ hh ht0 hht1]
  have hy0 := yL_nonneg38 t h μ
  have hy1 := yL_le38 μ ht0 hht hh
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hh.le)
      (Real.arsinh_nonneg_iff.mpr (mul_nonneg hh.le hy0))
  · calc h⁻¹ * Real.arsinh (h * yL38 t h μ) ≤ h⁻¹ * (h * yL38 t h μ) :=
          mul_le_mul_of_nonneg_left (arsinh_le_self38 (mul_nonneg hh.le hy0)) (inv_nonneg.mpr hh.le)
      _ = yL38 t h μ := by field_simp
      _ ≤ 2 * t := hy1

theorem weight_cont38 {lo up : ℝ} (c : BoundedCoefficients lo up) :
    Continuous (NlsGge.Weights.weight c.val) :=
  continuous_iff_continuousAt.2 fun r =>
    (NlsGge.Weights.weight_hasDerivAt lo up c.val c.property.1 (fun j => (c.property.2.2 j).1)
      (fun j => (c.property.2.2 j).2) r).continuousAt

theorem weight_nonneg38 {lo up : ℝ} (c : BoundedCoefficients lo up) (r : ℝ) :
    0 ≤ NlsGge.Weights.weight c.val r :=
  (NlsGge.Weights.weight_pos lo up c.val c.property.1 (fun j => (c.property.2.2 j).1)
    (fun j => (c.property.2.2 j).2) r).le

/-- A uniform bound for `W(2 sin(hv)/h)` when `|v| ≤ V`. -/
theorem weight_sin_le38 {lo up : ℝ} (c : BoundedCoefficients lo up) {h : ℝ} (hh : 0 < h)
    (v V : ℝ) (hv : |v| ≤ V) :
    NlsGge.Weights.weight c.val (2 * Real.sin (h * v) / h) ≤
      up * Real.exp (4 * Real.sqrt (2 * V)) := by
  refine (NlsGge.Weights.weight_upper lo up c.val c.property.1 (fun j => (c.property.2.2 j).1)
    (fun j => (c.property.2.2 j).2) _).trans ?_
  have hup : 0 ≤ up := c.property.1.le.trans c.property.2.1
  apply mul_le_mul_of_nonneg_left _ hup
  apply Real.exp_le_exp.mpr
  have : |2 * Real.sin (h * v) / h| ≤ 2 * V := by
    rw [abs_div, abs_mul, abs_of_pos hh, abs_two, div_le_iff₀ hh]
    have := Real.abs_sin_le_abs (x := h * v)
    rw [abs_mul, abs_of_pos hh] at this
    nlinarith
  nlinarith [Real.sqrt_le_sqrt this]

theorem eventually_small38 (t : ℝ) (ht0 : 0 ≤ t) (k : ℤ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h ∧ h * t ≤ 1 / 2 ∧ |(k : ℝ)| * h ≤ 1 / 3 := by
  have hb : 0 < min (1 / (2 * (t + 1))) (1 / (3 * (|(k : ℝ)| + 1))) := by
    apply lt_min <;> positivity
  filter_upwards [Ioo_mem_nhdsGT hb] with h hh
  have h1 : h < 1 / (2 * (t + 1)) := lt_of_lt_of_le hh.2 (min_le_left _ _)
  have h2 : h < 1 / (3 * (|(k : ℝ)| + 1)) := lt_of_lt_of_le hh.2 (min_le_right _ _)
  rw [lt_div_iff₀ (by positivity)] at h1 h2
  refine ⟨hh.1, ?_, ?_⟩
  · nlinarith
  · nlinarith [abs_nonneg (k : ℝ)]

/-- The shifted lattice window `{μ : μ + πk ∈ (-π/(2h), π/(2h)]}`. -/
def latWin38 (k : ℤ) (h : ℝ) : Set ℝ :=
  {μ : ℝ | μ + Real.pi * k ∈ Set.Ioc (-(Real.pi / (2 * h))) (Real.pi / (2 * h))}

theorem measurableSet_latWin38 (k : ℤ) (h : ℝ) : MeasurableSet (latWin38 k h) :=
  measurableSet_Ioc.preimage (measurable_add_const _)

theorem continuous_latF38 {lo up : ℝ} (c : BoundedCoefficients lo up) (k : ℤ) {t h : ℝ} :
    Continuous (latF38 (NlsGge.Weights.weight c.val) k t h) := by
  unfold latF38
  have hW := weight_cont38 c
  have h1 : Continuous fun μ : ℝ => Real.arcosh (max 1 (|Real.cos (h * μ)| /
      Real.sqrt (1 - h ^ 2 * t ^ 2))) :=
    Real.continuousOn_arcosh.comp_continuous (by fun_prop) (fun μ => (le_max_left _ _ : (1:ℝ) ≤ _))
  exact (hW.comp (by fun_prop)).mul (continuous_const.mul h1)

theorem latF_bound38 {lo up : ℝ} (c : BoundedCoefficients lo up) (k : ℤ) {t h : ℝ} (ht0 : 0 ≤ t)
    (hh : 0 < h) (hht : h * t ≤ 1 / 2) (hk : |(k : ℝ)| * h ≤ 1 / 3) (μ : ℝ) :
    ‖Set.indicator (latWin38 k h) (latF38 (NlsGge.Weights.weight c.val) k t h) μ‖ ≤
      Set.indicator (Set.Icc (-(2 * t)) (2 * t))
        (fun _ => up * Real.exp (4 * Real.sqrt (2 * (2 * t + Real.pi * |(k : ℝ)|))) * (2 * t)) μ := by
  set Wm := up * Real.exp (4 * Real.sqrt (2 * (2 * t + Real.pi * |(k : ℝ)|))) with hWm
  have hWm0 : 0 ≤ Wm := by
    have hup : 0 ≤ up := c.property.1.le.trans c.property.2.1
    positivity
  by_cases hμ : μ ∈ latWin38 k h
  · rw [Set.indicator_of_mem hμ]
    unfold latF38
    obtain ⟨g0, g1⟩ := gapL_bounds38 (t := t) μ hh ht0 hht
    have hw0 := weight_nonneg38 c (2 * Real.sin (h * (μ + Real.pi * k)) / h)
    by_cases hy : yL38 t h μ = 0
    · have : h⁻¹ * Real.arcosh (max 1 (|Real.cos (h * μ)| / Real.sqrt (1 - h ^ 2 * t ^ 2))) = 0 := by
        rw [gapL_arsinh38 μ hh ht0 (by linarith), hy]; simp
      rw [this, mul_zero, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => by positivity) _
    · have hS : |h * (μ + Real.pi * k)| ≤ Real.pi / 2 := by
        have h1 := hμ
        simp only [latWin38, Set.mem_ofPred_eq, Set.mem_Ioc] at h1
        rw [abs_le]
        have hpi := Real.pi_pos
        have e1 : Real.pi / (2 * h) * h = Real.pi / 2 := by field_simp
        constructor
        · have := mul_le_mul_of_nonneg_left h1.1.le hh.le
          have e2 : h * (-(Real.pi / (2 * h))) = -(Real.pi / 2) := by field_simp
          nlinarith
        · have := mul_le_mul_of_nonneg_left h1.2 hh.le
          have e2 : h * (Real.pi / (2 * h)) = Real.pi / 2 := by field_simp
          linarith
      have hsup := support38 t h μ k hh ht0 hht hk hS hy
      have hmem : μ ∈ Set.Icc (-(2 * t)) (2 * t) := abs_le.mp hsup
      rw [Set.indicator_of_mem hmem]
      have hv : |μ + Real.pi * k| ≤ 2 * t + Real.pi * |(k : ℝ)| := by
        calc |μ + Real.pi * k| ≤ |μ| + |Real.pi * k| := abs_add_le _ _
          _ ≤ 2 * t + Real.pi * |(k : ℝ)| := by
            rw [abs_mul, abs_of_pos Real.pi_pos]; linarith
      have hW := weight_sin_le38 c hh (μ + Real.pi * k) _ hv
      rw [Real.norm_of_nonneg (mul_nonneg hw0 (by simpa using g0))]
      exact mul_le_mul hW g1 g0 hWm0
  · rw [Set.indicator_of_notMem hμ, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => by positivity) _

theorem eventually_window38 (k : ℤ) (μ : ℝ) : ∀ᶠ h : ℝ in 𝓝[>] 0, μ ∈ latWin38 k h := by
  have hpi := Real.pi_pos
  set v := μ + Real.pi * k with hv
  have hb : 0 < Real.pi / (2 * (|v| + 1)) := by positivity
  filter_upwards [Ioo_mem_nhdsGT hb] with h hh
  have h1 : h < Real.pi / (2 * (|v| + 1)) := hh.2
  rw [lt_div_iff₀ (by positivity)] at h1
  have hh0 := hh.1
  have h2 : |v| < Real.pi / (2 * h) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith [abs_nonneg v]
  simp only [latWin38, Set.mem_ofPred_eq, Set.mem_Ioc]
  rw [← hv]
  exact ⟨by linarith [neg_abs_le v], by linarith [le_abs_self v]⟩

/-- Dominated convergence for the shifted lattice integrals. -/
theorem latInt_tendsto38 {lo up : ℝ} (c : BoundedCoefficients lo up) (k : ℤ) {t : ℝ} (ht0 : 0 ≤ t) :
    Tendsto (fun h : ℝ => ∫ μ : ℝ, Set.indicator (latWin38 k h)
        (latF38 (NlsGge.Weights.weight c.val) k t h) μ) (𝓝[>] 0)
      (𝓝 (∫ μ : ℝ, NlsGge.Weights.weight c.val (2 * (μ + Real.pi * k)) * planeGapCont38 t μ)) := by
  have hev := eventually_small38 t ht0 k
  refine tendsto_integral_filter_of_dominated_convergence
    (Set.indicator (Set.Icc (-(2 * t)) (2 * t))
        (fun _ => up * Real.exp (4 * Real.sqrt (2 * (2 * t + Real.pi * |(k : ℝ)|))) * (2 * t))) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun h =>
      (continuous_latF38 c k).aestronglyMeasurable.indicator (measurableSet_latWin38 k h)
  · filter_upwards [hev] with h hh
    exact Filter.Eventually.of_forall fun μ => latF_bound38 c k ht0 hh.1 hh.2.1 hh.2.2 μ
  · exact (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  · refine Filter.Eventually.of_forall fun μ => ?_
    have hsin := (tendsto_sin_div38 (μ + Real.pi * k))
    have hW : Tendsto (fun h : ℝ => NlsGge.Weights.weight c.val (2 * Real.sin (h * (μ + Real.pi * k)) / h))
        (𝓝[>] 0) (𝓝 (NlsGge.Weights.weight c.val (2 * (μ + Real.pi * k)))) := by
      have := ((weight_cont38 c).tendsto (2 * (μ + Real.pi * k))).comp (hsin.const_mul 2)
      refine this.congr fun h => ?_
      simp [mul_div_assoc]
    have hlim := hW.mul (tendsto_gapL38 t μ)
    refine hlim.congr' ?_
    filter_upwards [hev, eventually_window38 k μ] with h hh hin
    rw [Set.indicator_of_mem hin]
    unfold latF38
    rw [gapL_eq38 μ hh.1 ht0 (by linarith [hh.2.1])]

/-- Reflection and shift: the continuum integral `∫ W(2λ) √(t²-(λ+πk)²)₊ dλ` equals the lattice
limit `∫ W(2(μ+πk)) √(t²-μ²)₊ dμ` (`W` even, `λ = -(μ+πk)`). -/
theorem cont_change38 {lo up : ℝ} (c : BoundedCoefficients lo up) (k : ℤ) (t : ℝ) :
    ∫ lam : ℝ, NlsGge.Weights.weight c.val (2 * lam) * planeGapCont38 t (lam + Real.pi * k) =
      ∫ μ : ℝ, NlsGge.Weights.weight c.val (2 * (μ + Real.pi * k)) * planeGapCont38 t μ := by
  set f : ℝ → ℝ := fun lam =>
    NlsGge.Weights.weight c.val (2 * lam) * planeGapCont38 t (lam + Real.pi * k) with hf
  have e1 : ∀ μ : ℝ, NlsGge.Weights.weight c.val (2 * (μ + Real.pi * k)) * planeGapCont38 t μ =
      f (-(μ + Real.pi * k)) := by
    intro μ
    simp only [hf, planeGapCont38]
    have h1 : NlsGge.Weights.weight c.val (2 * -(μ + Real.pi * k)) =
        NlsGge.Weights.weight c.val (2 * (μ + Real.pi * k)) := by
      rw [mul_neg, NlsGge.Weights.weight_even]
    rw [h1]
    congr 3
    ring
  simp_rw [e1]
  rw [MeasureTheory.integral_add_right_eq_self (fun μ => f (-μ)) (Real.pi * k),
    MeasureTheory.integral_neg_eq_self f]

/-- `D:eq:planeconsistency` (paper/v2.tex l.2313-2327): for `u(x) = t e^{2πikx}` (fixed `k ∈ ℤ`,
`t ≥ 0`) and every full-energy weight `W` with admitted coefficients,
`E_{W,h}((h t e^{2πikjh})_j) → E_W(t e^{2πikx})` as `h = 1/L → 0` (`L` odd), where the lattice
energy is the full charge series `Σ_j β_j Q_{2j,h}` of the lattice plane wave and the continuum
energy `E_W` is the full charge series of the plane wave in the finite plane `FourierPlane N`,
`N ≥ |k|`. -/
theorem alPlaneConsistency38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) (k : ℤ)
    (hk : k.natAbs ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℕ, ∀ (L : ℕ) [NeZero L], Odd L → L₀ ≤ L →
      |alEnergy38 c.val (L : ℝ)⁻¹ (alPlaneWave38 L k t) -
        fullEnergy38 c N (planeWaveCoeff38 N k t)| < ε := by
  intro ε hε
  set E := fullEnergy38 c N (planeWaveCoeff38 N k t) with hE
  have hE' : E = (2 / Real.pi) *
      ∫ μ : ℝ, NlsGge.Weights.weight c.val (2 * (μ + Real.pi * k)) * planeGapCont38 t μ := by
    rw [hE, planeEnergy_cont38 c N k hk t, cont_change38]
  have hT := (latInt_tendsto38 c k ht).const_mul (2 / Real.pi)
  rw [← hE'] at hT
  have hinv : Tendsto (fun L : ℕ => ((L : ℝ))⁻¹) atTop (𝓝[>] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.comp tendsto_natCast_atTop_atTop
  have h1 := hT.comp hinv
  have hball := h1.eventually (Metric.ball_mem_nhds E hε)
  have hsmall := hinv.eventually (eventually_small38 t ht k)
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1 (hball.and hsmall)
  refine ⟨L₀, fun L _ hodd hL => ?_⟩
  obtain ⟨hb, hs⟩ := hL₀ L hL
  have hht : (L : ℝ)⁻¹ * t < 1 := by linarith [hs.2.1]
  have := alEnergy_plane_integral38 c L hodd k (h := (L : ℝ)⁻¹) rfl ht hht
  rw [this]
  have hb2 : |(2 / Real.pi * ∫ μ : ℝ, Set.indicator (latWin38 k (L : ℝ)⁻¹)
      (latF38 (NlsGge.Weights.weight c.val) k t (L : ℝ)⁻¹) μ) - E| < ε := by
    simpa [Function.comp, Metric.mem_ball, Real.dist_eq] using hb
  exact hb2

/-- The same statement along `L = 2n + 1`, i.e. `h = 1/(2n+1) → 0`. -/
theorem alPlaneConsistency_tendsto38 {lo up : ℝ} (c : BoundedCoefficients lo up) (N : ℕ) (k : ℤ)
    (hk : k.natAbs ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => alEnergy38 c.val (((2 * n + 1 : ℕ) : ℝ))⁻¹
        (alPlaneWave38 (2 * n + 1) k t)) atTop (𝓝 (fullEnergy38 c N (planeWaveCoeff38 N k t))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := alPlaneConsistency38 c N k hk ht ε hε
  refine ⟨L₀, fun n hn => ?_⟩
  rw [Real.dist_eq]
  exact hL₀ (2 * n + 1) ⟨n, rfl⟩ (by omega)

end NlsGge.AblowitzLadik
end
