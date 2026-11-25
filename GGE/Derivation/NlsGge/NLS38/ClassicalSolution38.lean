import NlsGge.NLS38.ClassicalSolution38a
import NlsGge.NLS38.FlowMaps38

/-! # GWP piece A11: classical solutions for `h³` data

Plan: `campaign/GWP_PLAN.md` §7 Part A, piece A11 (the evaluation series `serU` and its `ℓ¹`
calculus are in `NlsGge.NLS38.ClassicalSolution38a`).

For `x ∈ h³` the flow `u(t) = nlsFlowSeq t x` is an `h³`-continuous curve (A6a persistence, via A9)
which is a `C¹` curve of the `h¹` carrier (A6a `cutSol_C1_h1`); the evaluation
`ev_θ : ℓ¹ → ℂ`, `x ↦ serU x θ`, is a bounded linear functional on `h¹` (`ℓ¹ ≤ C₁ h¹`).  Hence

* `U = serU (u t) θ`, `U_x = serU (dx u)`, `U_xx = serU (dx dx u)` are jointly continuous
  (the `ℓ¹` norm of a difference is bounded by `C₁ (2π)^j hn 3` of the difference);
* `U_t = serU (u')` by the chain rule through `ev_θ ∘ γ`;
* the PDE `i U_t = -U_xx + 2|U|² U` is `serU_mul`, `serU_conj` for the coefficient identity
  `u' = -i((2πn)² uₙ + nonlin u)`; `U_t` is then also jointly continuous because the PDE exhibits it
  as a continuous expression in `U`, `U_xx`.

Also `serU_eq_physicalH1Continuous` (the physical `H¹` representative, A-existing
`physicalH1Continuous`) and a plane-wave regression probe.
-/

set_option autoImplicit false
noncomputable section

namespace NlsGge.NLS38

open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff Filter Topology
open scoped ComplexConjugate

/-! ## The evaluation functional on `h¹` -/

/-- `ev_θ : h¹ → ℂ`, `x ↦ serU x θ`, as a bounded real-linear functional (norm `≤ C₁`). -/
def evC (θ : ℝ) : SobolevCarrier38 ((1 : ℕ) : ℝ) →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun x => serU (carrierCoe38 ((1 : ℕ) : ℝ) x) θ
      map_add' := fun x y => by
        have hx := (isL1_of_h1_nat _ (carrierCoe38_mem _ x)).1
        have hy := (isL1_of_h1_nat _ (carrierCoe38_mem _ y)).1
        exact serU_add hx hy θ
      map_smul' := fun c x => by
        have e : carrierCoe38 ((1 : ℕ) : ℝ) (c • x) = (c : ℂ) • carrierCoe38 ((1 : ℕ) : ℝ) x := by
          funext n
          show c • carrierCoe38 ((1 : ℕ) : ℝ) x n = (c : ℂ) * carrierCoe38 ((1 : ℕ) : ℝ) x n
          exact Complex.real_smul
        simp only [e, serU_smul, RingHom.id_apply, Complex.real_smul] } C1
    (fun x => by
      have h := isL1_of_h1_nat _ (carrierCoe38_mem ((1 : ℕ) : ℝ) x)
      exact (norm_serU_le h.1 θ).trans h.2)

theorem evC_apply (θ : ℝ) (x : SobolevCarrier38 ((1 : ℕ) : ℝ)) :
    evC θ x = serU (carrierCoe38 ((1 : ℕ) : ℝ) x) θ := rfl

theorem evC_mk (θ : ℝ) (y : ℤ → ℂ) (hy : y ∈ seqSobolev38 ((1 : ℕ) : ℝ)) :
    evC θ (carrierMk38 ((1 : ℕ) : ℝ) y hy) = serU y θ := rfl

/-! ## `ℓ¹` bounds of differences in terms of `hn 3` -/

section Bounds

variable {d : ℤ → ℂ}

theorem l1_le_hn3 (hd : d ∈ seqSobolev38 ((3 : ℕ) : ℝ)) : IsL1 d ∧ l1 d ≤ C1 * hn 3 d := by
  obtain ⟨h1, h2⟩ := isL1_of_hn_one d (seqSobolev38_mono (by norm_num) hd)
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left (hn_mono38 (by norm_num) hd) (by
    unfold C1; exact norm_nonneg _))⟩

theorem dx_mem_h2 (hd : d ∈ seqSobolev38 ((3 : ℕ) : ℝ)) : dx d ∈ seqSobolev38 ((2 : ℕ) : ℝ) :=
  dx_mem 2 hd

theorem dxdx_mem_h1 (hd : d ∈ seqSobolev38 ((3 : ℕ) : ℝ)) :
    dx (dx d) ∈ seqSobolev38 ((1 : ℕ) : ℝ) := dx_mem 1 (dx_mem 2 hd)

theorem l1_dx_le_hn3 (hd : d ∈ seqSobolev38 ((3 : ℕ) : ℝ)) :
    IsL1 (dx d) ∧ l1 (dx d) ≤ C1 * (2 * Real.pi) * hn 3 d := by
  have h2 := dx_mem_h2 hd
  have h1 : dx d ∈ seqSobolev38 ((1 : ℕ) : ℝ) := seqSobolev38_mono (by norm_num) h2
  obtain ⟨hL, hb⟩ := isL1_of_hn_one _ h1
  refine ⟨hL, hb.trans ?_⟩
  have hC : 0 ≤ C1 := by unfold C1; exact norm_nonneg _
  have h4 : hn 1 (dx d) ≤ 2 * Real.pi * hn 3 d := by
    have a1 := hn_dx_le 1 (seqSobolev38_mono (by norm_num) hd : d ∈ seqSobolev38 ((1 + 1 : ℕ) : ℝ))
    have a2 := hn_mono38 (a := 2) (b := 3) (by norm_num) hd
    calc hn 1 (dx d) ≤ 2 * Real.pi * hn (1 + 1) d := a1
      _ ≤ 2 * Real.pi * hn 3 d := mul_le_mul_of_nonneg_left a2 (by positivity)
  calc C1 * hn 1 (dx d) ≤ C1 * (2 * Real.pi * hn 3 d) := mul_le_mul_of_nonneg_left h4 hC
    _ = _ := by ring

theorem l1_dxdx_le_hn3 (hd : d ∈ seqSobolev38 ((3 : ℕ) : ℝ)) :
    IsL1 (dx (dx d)) ∧ l1 (dx (dx d)) ≤ C1 * (2 * Real.pi) ^ 2 * hn 3 d := by
  have h1 := dxdx_mem_h1 hd
  obtain ⟨hL, hb⟩ := isL1_of_hn_one _ h1
  refine ⟨hL, hb.trans ?_⟩
  have hC : 0 ≤ C1 := by unfold C1; exact norm_nonneg _
  have h4 : hn 1 (dx (dx d)) ≤ (2 * Real.pi) ^ 2 * hn 3 d := by
    have a1 := hn_dx_le 1 (dx_mem_h2 hd)
    have a2 := hn_dx_le 2 hd
    calc hn 1 (dx (dx d)) ≤ 2 * Real.pi * hn 2 (dx d) := a1
      _ ≤ 2 * Real.pi * (2 * Real.pi * hn 3 d) :=
          mul_le_mul_of_nonneg_left a2 (by positivity)
      _ = _ := by ring
  calc C1 * hn 1 (dx (dx d)) ≤ C1 * ((2 * Real.pi) ^ 2 * hn 3 d) :=
        mul_le_mul_of_nonneg_left h4 hC
    _ = _ := by ring

end Bounds

/-! ## The PDE identity on the coefficient side -/

theorem nonlin_eq_smul (v : ℤ → ℂ) : nonlin v = (2 : ℂ) • conv (conv v v) (cstar v) := by
  funext n; simp [nonlin]

theorem serU_nonlin {v : ℤ → ℂ} (hv : IsL1 v) (θ : ℝ) :
    serU (nonlin v) θ = 2 * ((‖serU v θ‖ ^ 2 : ℝ) : ℂ) * serU v θ := by
  have hc : IsL1 (cstar v) := (isL1_cstar_iff v).2 hv
  have h1 := (isL1_conv hv hv).1
  rw [nonlin_eq_smul, serU_smul, ← serU_mul h1 hc, ← serU_mul hv hv, ← serU_conj]
  have e : ((‖serU v θ‖ ^ 2 : ℝ) : ℂ) = serU v θ * conj (serU v θ) := by
    rw [Complex.mul_conj']; push_cast; ring
  rw [e]; ring

theorem disp_mul_eq_neg_dxdx (v : ℤ → ℂ) :
    (fun n => ((disp n : ℝ) : ℂ) * v n) = fun n => -dx (dx v) n := by
  funext n
  simp only [dx, disp]
  push_cast
  have : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination ((2 * (Real.pi : ℂ) * (n : ℂ)) ^ 2 * v n) * this

/-- The right-hand side `-i(Λ v + nonlin v)` as a sequence. -/
def rhsSeq (v : ℤ → ℂ) : ℤ → ℂ := fun n => -Complex.I * (((disp n : ℝ) : ℂ) * v n + nonlin v n)

theorem isL1_rhsSeq {v : ℤ → ℂ} (hv : IsL1 v) (hdd : IsL1 (dx (dx v))) : IsL1 (rhsSeq v) := by
  have h1 : IsL1 (fun n => ((disp n : ℝ) : ℂ) * v n) := by
    rw [disp_mul_eq_neg_dxdx]; exact isL1_neg hdd
  have h2 := (isL1_nonlin hv).1
  have := isL1_smul (-Complex.I) (isL1_add h1 h2)
  exact this.congr fun n => by simp [rhsSeq]

theorem pde_coeff {v : ℤ → ℂ} (hv : IsL1 v) (hdd : IsL1 (dx (dx v))) (θ : ℝ) :
    Complex.I * serU (rhsSeq v) θ =
      -serU (dx (dx v)) θ + 2 * ((‖serU v θ‖ ^ 2 : ℝ) : ℂ) * serU v θ := by
  have h1 : IsL1 (fun n => ((disp n : ℝ) : ℂ) * v n) := by
    rw [disp_mul_eq_neg_dxdx]; exact isL1_neg hdd
  have h2 := (isL1_nonlin hv).1
  have e : rhsSeq v = (-Complex.I) • ((fun n => ((disp n : ℝ) : ℂ) * v n) + nonlin v) := by
    funext n; simp [rhsSeq]
  rw [e, serU_smul, serU_add h1 h2, serU_nonlin hv, disp_mul_eq_neg_dxdx, serU_neg]
  have : Complex.I * (-Complex.I) = 1 := by simp
  linear_combination ((-(serU (dx (dx v)) θ)) + 2 * ((‖serU v θ‖ ^ 2 : ℝ) : ℂ) * serU v θ) * this

/-! ## The classical solution -/

/-- Generic form of `classical_solution` for a cutoff solution that is `h³`-valued, `h³`-continuous
and in the region where the cutoff is inactive. -/
theorem classical_solution_aux {R : ℝ} (hR : 0 < R) {u : ℝ → ℤ → ℂ} (hcut : IsCutSol R u)
    (hM3 : IsCutSolM 3 R u) (h3 : u 0 ∈ seqSobolev38 ((3 : ℕ) : ℝ))
    (hχ : ∀ t, cutoff R (hn 1 (u t)) = 1) :
    ∃ Ux Uxx Ut : ℝ → ℝ → ℂ,
      Continuous (Function.uncurry fun t θ => serU (u t) θ) ∧ Continuous (Function.uncurry Ux) ∧
      Continuous (Function.uncurry Uxx) ∧ Continuous (Function.uncurry Ut) ∧
      (∀ t θ, HasDerivAt (fun θ => serU (u t) θ) (Ux t θ) θ) ∧ (∀ t θ, HasDerivAt (Ux t) (Uxx t θ) θ) ∧
      (∀ t θ, HasDerivAt (fun s => serU (u s) θ) (Ut t θ) t) ∧
      (∀ t θ, Complex.I * Ut t θ = -Uxx t θ + 2 * ((‖serU (u t) θ‖ ^ 2 : ℝ) : ℂ) * serU (u t) θ) ∧
      (∀ t θ, serU (u t) (θ + 1) = serU (u t) θ ∧ Ux t (θ + 1) = Ux t θ) := by
  have hmem : ∀ t, u t ∈ seqSobolev38 ((3 : ℕ) : ℝ) := hM3.mem
  have hL0 : ∀ t, IsL1 (u t) := fun t => (l1_le_hn3 (hmem t)).1
  have hL1 : ∀ t, IsL1 (dx (u t)) := fun t => (l1_dx_le_hn3 (hmem t)).1
  have hL2 : ∀ t, IsL1 (dx (dx (u t))) := fun t => (l1_dxdx_le_hn3 (hmem t)).1
  -- `h³`-continuity of `u`, measured by `hn 3` of differences
  have hc3 : ∀ t0, Tendsto (fun t => hn 3 (fun n => u t n - u t0 n)) (𝓝 t0) (𝓝 0) := by
    intro t0
    have hc := hM3.cont.tendsto t0
    have h0 := (tendsto_iff_norm_sub_tendsto_zero.1 hc)
    refine h0.congr fun t => ?_
    rw [norm_sub_eq_hn38 3]
    rfl
  have hdm : ∀ t t0, (fun n => u t n - u t0 n) ∈ seqSobolev38 ((3 : ℕ) : ℝ) :=
    fun t t0 => sub_mem_nat38 3 (hmem t) (hmem t0)
  have hcurve : ∀ (y : ℝ → ℤ → ℂ) (K : ℝ), (∀ t, IsL1 (y t)) →
      (∀ t t0, l1 (y t - y t0) ≤ K * hn 3 (fun n => u t n - u t0 n)) →
      Continuous (Function.uncurry fun t θ => serU (y t) θ) := by
    intro y K hy hb
    refine continuous_serU_curve hy fun t0 => ?_
    have h := ((hc3 t0).const_mul K)
    rw [mul_zero] at h
    exact squeeze_zero (fun t => l1_nonneg _) (fun t => hb t t0) h
  have hUc : Continuous (Function.uncurry fun t θ => serU (u t) θ) :=
    hcurve u C1 hL0 fun t t0 => (l1_le_hn3 (hdm t t0)).2
  have hUxc : Continuous (Function.uncurry fun t θ => serU (dx (u t)) θ) :=
    hcurve (fun t => dx (u t)) (C1 * (2 * Real.pi)) hL1 fun t t0 => by
      have := (l1_dx_le_hn3 (hdm t t0)).2
      rw [show (fun n => u t n - u t0 n) = u t - u t0 from rfl, dx_sub] at this
      exact this
  have hUxxc : Continuous (Function.uncurry fun t θ => serU (dx (dx (u t))) θ) :=
    hcurve (fun t => dx (dx (u t))) (C1 * (2 * Real.pi) ^ 2) hL2 fun t t0 => by
      have := (l1_dxdx_le_hn3 (hdm t t0)).2
      rw [show (fun n => u t n - u t0 n) = u t - u t0 from rfl, dx_sub, dx_sub] at this
      exact this
  refine ⟨fun t θ => serU (dx (u t)) θ, fun t θ => serU (dx (dx (u t))) θ,
    fun t θ => serU (rhsSeq (u t)) θ, hUc, hUxc, hUxxc, ?_, fun t θ => hasDerivAt_serU (hL0 t) (hL1 t) θ,
    fun t θ => hasDerivAt_serU (hL1 t) (hL2 t) θ, ?_, ?_, fun t θ => ⟨serU_periodic _ _, serU_periodic _ _⟩⟩
  · -- `U_t` is continuous: it is `-i (-U_xx + 2|U|² U)` by the PDE
    have hpde := fun t θ => pde_coeff (hL0 t) (hL2 t) θ
    have hcont : Continuous fun p : ℝ × ℝ => -Complex.I * (-serU (dx (dx (u p.1))) p.2 +
        2 * ((‖serU (u p.1) p.2‖ ^ 2 : ℝ) : ℂ) * serU (u p.1) p.2) := by
      have a : Continuous fun p : ℝ × ℝ => serU (u p.1) p.2 := hUc
      have b : Continuous fun p : ℝ × ℝ => serU (dx (dx (u p.1))) p.2 := hUxxc
      fun_prop
    refine hcont.congr fun p => ?_
    simp only [Function.uncurry]
    rw [← hpde, ← mul_assoc]
    simp
  · -- time derivative through `ev_θ ∘ γ`
    intro t θ
    obtain ⟨γ, hγ0, hγ⟩ := cutSol_C1_h1 R hR u hcut h3
    have h := (evC θ).hasFDerivAt.comp_hasDerivAt t (hγ t)
    have e1 : (evC θ ∘ γ) = fun s => serU (u s) θ := by
      funext s
      show serU (carrierCoe38 _ (γ s)) θ = _
      rw [hγ0 s]
    have e2 : (fun n => -Complex.I * (((disp n : ℝ) : ℂ) * u t n +
        ((cutoff R (hn 1 (u t)) : ℝ) : ℂ) * nonlin (u t) n)) = rhsSeq (u t) := by
      funext n; rw [hχ t]; simp [rhsSeq]
    rw [e1] at h
    rw [evC_mk, e2] at h
    exact h
  · intro t θ
    exact pde_coeff (hL0 t) (hL2 t) θ

/-- §6.0 transport: the literal index `3 : ℝ` and the cast `((3 : ℕ) : ℝ)` give the same space. -/
theorem seqSobolev38_three_cast : seqSobolev38 ((3 : ℕ) : ℝ) = seqSobolev38 3 := by
  rw [Nat.cast_ofNat]

/-- The cutoff is inactive along the flow: `‖u(t)‖_{h¹} ≤ B(x) < R`. -/
theorem flow_cutoff_eq_one38 {x : ℤ → ℂ} (hx : x ∈ seqSobolev38 ((1 : ℕ) : ℝ)) (t : ℝ) :
    cutoff (Bx x + 2) (hn 1 (nlsFlowSeq t x)) = 1 := by
  obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx
  apply cutoff_eq_one (by linarith [Bx_nonneg38 x])
  have h := hn_le_Bx38 (hs.mem t)
  have : Bx (nlsFlowSeq t x) = Bx x := by
    unfold Bx
    rw [(nls_conserved hs t).1, (nls_conserved hs t).2]
    simp only [h0]
  linarith

/-- **A11** (`h³` data): the NLS flow gives a classical solution: `U`, `U_x`, `U_xx`, `U_t`
are jointly continuous and `i U_t = -U_xx + 2|U|² U`.  (§6.0: `seqSobolev38 3` is the cast
`((3 : ℕ) : ℝ)`.) -/
theorem classical_solution (x : ℤ → ℂ) (hx : x ∈ seqSobolev38 ((3 : ℕ) : ℝ)) :
    ∃ Ux Uxx Ut : ℝ → ℝ → ℂ,
      Continuous (Function.uncurry fun t θ => serU (nlsFlowSeq t x) θ) ∧ Continuous (Function.uncurry Ux) ∧
      Continuous (Function.uncurry Uxx) ∧ Continuous (Function.uncurry Ut) ∧
      (∀ t θ, HasDerivAt (fun θ => serU (nlsFlowSeq t x) θ) (Ux t θ) θ) ∧ (∀ t θ, HasDerivAt (Ux t) (Uxx t θ) θ) ∧
      (∀ t θ, HasDerivAt (fun s => serU (nlsFlowSeq s x) θ) (Ut t θ) t) ∧
      (∀ t θ, Complex.I * Ut t θ = -Uxx t θ + 2 * ((‖serU (nlsFlowSeq t x) θ‖ ^ 2 : ℝ) : ℂ) * serU (nlsFlowSeq t x) θ) ∧
      (∀ t θ, serU (nlsFlowSeq t x) (θ + 1) = serU (nlsFlowSeq t x) θ ∧ Ux t (θ + 1) = Ux t θ) := by
  have hx1 : x ∈ seqSobolev38 ((1 : ℕ) : ℝ) := mem_h1_of_mem_nat 3 (by norm_num) hx
  obtain ⟨hs, h0⟩ := nlsFlowSeq_spec x hx1
  have hR0 : 0 < Bx x + 2 := by linarith [Bx_nonneg38 x]
  have hcut : IsCutSol (Bx x + 2) (fun t => nlsFlowSeq t x) :=
    nlsSol_isCutSol38 hs (by simp only [h0]; linarith)
  have hM3 := flow_isCutSolM38 3 (by norm_num) hx (le_refl (Bx x + 2))
  exact classical_solution_aux hR0 hcut hM3 (by simp only [h0]; exact hx)
    (flow_cutoff_eq_one38 hx1)

/-! ## The physical `H¹` representative -/

open NlsGge.Analysis in
/-- `serU` of the physical Fourier coefficients is the continuous `H¹` representative. -/
theorem serU_eq_physicalH1Continuous {w : PhysicalL2}
    (hw : SobolevSquareSummable 1 (physicalFourier w)) (θ : ℝ) :
    serU (physicalFourier w) θ = (physicalH1Continuous w hw) (θ : PhysicalCircle) := by
  unfold physicalH1Continuous
  have h := ContinuousMap.tsum_apply (physicalH1_continuous_fourier_summable w hw)
    (θ : PhysicalCircle)
  rw [← h]
  unfold serU
  refine tsum_congr fun p => ?_
  rw [ContinuousMap.smul_apply, smul_eq_mul, fourier_coe_apply]
  simp

/-! ## Regression probe: a plane wave, where `serU` is an explicit exponential -/

section PlaneWaveProbe

theorem serU_single (k : ℤ) (b : ℂ) (θ : ℝ) : serU (Pi.single k b) θ = b * eT k θ := by
  rw [serU_def, tsum_eq_single k]
  · simp
  · intro n hn; simp [hn]

/-- The plane-wave frequency `W = (2πk)² + 2|a|²` (real, cast to `ℂ`). -/
def pwFreq38 (k : ℤ) (a : ℂ) : ℂ := (2 * Real.pi * k) ^ 2 + 2 * (‖a‖ : ℂ) ^ 2

/-- `serU` of the flow of a plane wave is the explicit exponential
`a e^{2πikθ - i W t}`. -/
theorem serU_flow_planeWave (k : ℤ) (a : ℂ) (t θ : ℝ) :
    serU (nlsFlowSeq t (Pi.single k a)) θ =
      Complex.exp (-(Complex.I * t * pwFreq38 k a)) * a * eT k θ := by
  rw [nlsFlowSeq_planeWave, serU_single]
  rfl

theorem norm_serU_flow_planeWave (k : ℤ) (a : ℂ) (t θ : ℝ) :
    ‖serU (nlsFlowSeq t (Pi.single k a)) θ‖ = ‖a‖ := by
  rw [serU_flow_planeWave, norm_mul, norm_mul, norm_eT, mul_one]
  have : -(Complex.I * (t : ℂ) * pwFreq38 k a) =
      ((-(t * ((2 * Real.pi * k) ^ 2 + 2 * ‖a‖ ^ 2)) : ℝ) : ℂ) * Complex.I := by
    unfold pwFreq38; push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Any triple of derivatives for the plane-wave flow is the explicit one. -/
theorem classical_solution_planeWave_values38 (k : ℤ) (a : ℂ) (Ux Uxx Ut : ℝ → ℝ → ℂ)
    (h1 : ∀ t θ, HasDerivAt (fun θ => serU (nlsFlowSeq t (Pi.single k a)) θ) (Ux t θ) θ)
    (h2 : ∀ t θ, HasDerivAt (Ux t) (Uxx t θ) θ)
    (h3 : ∀ t θ, HasDerivAt (fun s => serU (nlsFlowSeq s (Pi.single k a)) θ) (Ut t θ) t) (t θ : ℝ) :
    Ux t θ = (2 * Real.pi * Complex.I * k) * serU (nlsFlowSeq t (Pi.single k a)) θ ∧
    Uxx t θ = -((2 * Real.pi * k : ℂ) ^ 2) * serU (nlsFlowSeq t (Pi.single k a)) θ ∧
    Ut t θ = -(Complex.I * pwFreq38 k a) * serU (nlsFlowSeq t (Pi.single k a)) θ := by
  have hc : ∀ t : ℝ, serU (nlsFlowSeq t (Pi.single k a)) = fun θ =>
      (Complex.exp (-(Complex.I * t * pwFreq38 k a)) * a) * eT k θ := fun t => by
    funext θ; rw [serU_flow_planeWave]
  have hUx : ∀ t θ, Ux t θ = (Complex.exp (-(Complex.I * t * pwFreq38 k a)) * a) *
      (eT k θ * (2 * Real.pi * Complex.I * k)) := by
    intro t θ
    have h := h1 t θ
    rw [hc t] at h
    exact h.unique ((hasDerivAt_eT k θ).const_mul _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hUx, serU_flow_planeWave]; ring
  · have h := h2 t θ
    have e : Ux t = fun θ => (Complex.exp (-(Complex.I * t * pwFreq38 k a)) * a) *
        (eT k θ * (2 * Real.pi * Complex.I * k)) := funext (hUx t)
    rw [e] at h
    have h' := ((hasDerivAt_eT k θ).mul_const (2 * Real.pi * Complex.I * k)).const_mul
      (Complex.exp (-(Complex.I * t * pwFreq38 k a)) * a)
    rw [h.unique h', serU_flow_planeWave]
    have : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
    linear_combination ((Complex.exp (-(Complex.I * t * pwFreq38 k a)) * a * eT k θ) *
      (2 * Real.pi * k : ℂ) ^ 2) * this
  · have h := h3 t θ
    have hs : (fun s : ℝ => serU (nlsFlowSeq s (Pi.single k a)) θ) = fun s : ℝ =>
        Complex.exp (-(Complex.I * s * pwFreq38 k a)) * a * eT k θ := funext fun s => by
      rw [serU_flow_planeWave]
    rw [hs] at h
    have hl : HasDerivAt (fun s : ℝ => -(Complex.I * (s : ℂ) * pwFreq38 k a))
        (-(Complex.I * pwFreq38 k a)) t := by
      have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (Complex.I)
      have := (this.mul_const (pwFreq38 k a)).fun_neg
      simpa using this
    have h' := ((hl.cexp).mul_const a).mul_const (eT k θ)
    rw [h.unique h', serU_flow_planeWave]
    ring

/-- **Regression probe** (`classical_solution` on a plane wave): the classical solution through
`δ_k a` has `U = a e^{2πikθ - i W t}` explicitly, `U_x = 2πik U`, `U_xx = -(2πk)² U`,
`U_t = -iW U`, and the PDE of `classical_solution` holds with `|U| = |a|`. -/
theorem classical_solution_planeWave38 (k : ℤ) (a : ℂ) :
    ∃ Ux Uxx Ut : ℝ → ℝ → ℂ,
      Continuous (Function.uncurry Ut) ∧
      (∀ t θ, serU (nlsFlowSeq t (Pi.single k a)) θ =
        Complex.exp (-(Complex.I * t * pwFreq38 k a)) * a * eT k θ) ∧
      (∀ t θ, Ux t θ = (2 * Real.pi * Complex.I * k) * serU (nlsFlowSeq t (Pi.single k a)) θ) ∧
      (∀ t θ, Uxx t θ = -((2 * Real.pi * k : ℂ) ^ 2) * serU (nlsFlowSeq t (Pi.single k a)) θ) ∧
      (∀ t θ, Ut t θ = -(Complex.I * pwFreq38 k a) * serU (nlsFlowSeq t (Pi.single k a)) θ) ∧
      (∀ t θ, Complex.I * Ut t θ = -Uxx t θ + 2 * ((‖a‖ ^ 2 : ℝ) : ℂ) *
        serU (nlsFlowSeq t (Pi.single k a)) θ) := by
  obtain ⟨Ux, Uxx, Ut, -, -, -, hUt, h1, h2, h3, hpde, -⟩ :=
    classical_solution (Pi.single k a) (single_mem_seqSobolev38 _ k a)
  refine ⟨Ux, Uxx, Ut, hUt, serU_flow_planeWave k a, fun t θ =>
    (classical_solution_planeWave_values38 k a Ux Uxx Ut h1 h2 h3 t θ).1, fun t θ =>
    (classical_solution_planeWave_values38 k a Ux Uxx Ut h1 h2 h3 t θ).2.1, fun t θ =>
    (classical_solution_planeWave_values38 k a Ux Uxx Ut h1 h2 h3 t θ).2.2, fun t θ => ?_⟩
  rw [hpde, norm_serU_flow_planeWave]

/-- Independent algebraic check of the plane-wave normalisation: the explicit `U_t` and `U_xx`
satisfy `i U_t = -U_xx + 2|a|² U`. -/
theorem planeWave_pde_explicit38 (k : ℤ) (a P : ℂ) :
    Complex.I * (-(Complex.I * pwFreq38 k a) * P) =
      -(-((2 * Real.pi * k : ℂ) ^ 2) * P) + 2 * ((‖a‖ ^ 2 : ℝ) : ℂ) * P := by
  unfold pwFreq38
  have : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  push_cast
  linear_combination (-(((2 * Real.pi * k : ℂ) ^ 2 + 2 * (‖a‖ : ℂ) ^ 2) * P)) * this

end PlaneWaveProbe

end NlsGge.NLS38
