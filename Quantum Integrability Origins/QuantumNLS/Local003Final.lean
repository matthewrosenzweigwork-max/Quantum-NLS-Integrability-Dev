import Mathlib
import QuantumNLS.Local003First
import QuantumNLS.Local003Spectrum
import QuantumNLS.Fourier
import QuantumNLS.Local002Bridge

/-! LOCAL-003 `thm:reset-uniform-reduction` (spectral_reduction.tex:87-110): the final theorem.

`reset_uniform_reduction` (potentials in `L²(0,L)`, the interval model of `LocalSpectralOperator`) and
`reset_uniform_reduction_profile` (the DEF-001 profile `u ∈ L²(𝕋_L)`, entering through `circleRep u`, with `u_n = Fourier.coeff`).
Only the printed hypotheses `0 < L`, `0 < κ`, `0 < r < 2π/L`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.Local003Final
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002SA QuantumNLS.Local003Analytic
  QuantumNLS.Local003Isometry QuantumNLS.Local003Inst QuantumNLS.Local003First

variable {L κ r : ℝ}

theorem reset_uniform_reduction (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
      ∃ (a : Lp ℂ 2 (μI L) → ℝ) (b : Lp ℂ 2 (μI L) → ℂ),
        AnalyticOnNhd ℝ a (ball 0 ρ) ∧ AnalyticOnNhd ℝ b (ball 0 ρ) ∧
        (∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, SmallCompression L κ (u : ℝ → ℂ) n r) ∧
        (∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, ∀ h : SmallCompression L κ (u : ℝ → ℂ) n r, ∀ v : E2,
          reducedMatrix2 L κ (u : ℝ → ℂ) n r h v =
            vec2 ((a u : ℂ) * v 0 + conj (b u) * v 1) (b u * v 0 + (a u : ℂ) * v 1)) ∧
        (∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ,
          (∀ lam : ℂ, ‖lam - (pm L n : ℂ)‖ < r →
            ∃ Eig : Submodule ℂ (H2 L),
              (∀ f : H2 L, f ∈ Eig ↔ (f, lam • f) ∈ LuGraph L κ (u : ℝ → ℂ) (parity n)) ∧
              Module.finrank ℂ Eig =
                Multiset.count lam {((a u + ‖b u‖ : ℝ) : ℂ), ((a u - ‖b u‖ : ℝ) : ℂ)}) ∧
          ‖((a u + ‖b u‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r ∧ ‖((a u - ‖b u‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r ∧
          (∀ lam : ℂ, ‖lam - (pm L n : ℂ)‖ < r → lam ≠ ((a u + ‖b u‖ : ℝ) : ℂ) →
            lam ≠ ((a u - ‖b u‖ : ℝ) : ℂ) →
            ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (u : ℝ → ℂ) (parity n) lam R) ∧
          (((a u + ‖b u‖ : ℝ) : ℂ) = ((a u - ‖b u‖ : ℝ) : ℂ) ↔ b u = 0)) ∧
        AnalyticOnNhd ℝ (fun u : Lp ℂ 2 (μI L) => ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b u)
          (ball 0 ρ) ∧
        (∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ,
          ‖((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b u - uCoeff L n u‖ ≤ C * ‖u‖ ^ 3) ∧
        (∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ,
          DifferentiableAt ℝ (fun w : Lp ℂ 2 (μI L) =>
            ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b w) u ∧
          ‖fderiv ℝ (fun w : Lp ℂ 2 (μI L) =>
              ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b w) u -
            fderiv ℝ (fun w : Lp ℂ 2 (μI L) =>
              ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b w) 0‖ ≤ C * ‖u‖ ^ 2) := by
  obtain ⟨ρ0, hρ0, hform⟩ := reducedMatrix_form_analytic (κ := κ) hL hr hr2
  set ρ : ℝ := min ρ0 (rho1 κ L r) with hρdef
  have hρpos : 0 < ρ := lt_min hρ0 (rho1_pos κ L r)
  set k : ℂ := ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) with hk
  have hsqκ : (0 : ℝ) < Real.sqrt κ := Real.sqrt_pos.mpr hκ
  have hsqL : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hknorm : ‖k‖ = Real.sqrt L / (2 * Real.sqrt κ) := by
    rw [hk, norm_div, Complex.norm_real, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg hsqL.le, Real.norm_of_nonneg hsqκ.le]
    simp
  have hC1 : 0 ≤ C1c κ L r := by unfold C1c; have := Kc_nonneg κ L r; have := hr; positivity
  have hC2 : 0 ≤ C2c κ L r := by unfold C2c; have := Kc_nonneg κ L r; have := hr; positivity
  refine ⟨ρ, hρpos, ‖k‖ * max (C1c κ L r) (C2c κ L r),
    mul_nonneg (norm_nonneg _) (le_trans hC1 (le_max_left _ _)), fun n => ?_⟩
  obtain ⟨a, b0, ha, hb, hmat⟩ := hform n
  obtain ⟨F0, G, hF0e, hF0n, hP0, hGn, hMul, hbr, hcub, hder⟩ := inst_est (κ := κ) hL hr hr2 n
  have hρ0le : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ0 := fun u hu =>
    ball_subset_ball (min_le_left _ _) hu
  have hρ1 : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, ‖u‖ < rho1 κ L r := fun u hu => by
    have := mem_ball_zero_iff.mp hu
    exact lt_of_lt_of_le this (min_le_right _ _)
  have hgood : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, ‖u‖ < goodRadius κ L r := fun u hu =>
    lt_of_lt_of_le (hρ1 u hu) (rho1_le_good κ L r)
  have hSC : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, SmallCompression L κ (u : ℝ → ℂ) n r := fun u hu =>
    (ctx_of_ball hL hr hr2 n u (hgood u hu)).hsmall
  have hmat' : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, ∀ h : SmallCompression L κ (u : ℝ → ℂ) n r, ∀ v : E2,
      reducedMatrix2 L κ (u : ℝ → ℂ) n r h v =
        vec2 ((a u : ℂ) * v 0 + conj (b0 u) * v 1) (b0 u * v 0 + (a u : ℂ) * v 1) :=
    fun u hu h v => hmat u (hρ0le u hu) h v
  have hbe : ∀ u ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, b0 u = Bf L κ (u : ℝ → ℂ) n r (vec2 1 0) 1 := by
    intro u hu
    have e := hmat' u hu (hSC u hu) (vec2 1 0)
    rw [reducedMatrix2_eq] at e
    have := congrArg (fun w : E2 => w 1) e
    simpa [vec2] using this.symm
  have hmono : ball (0 : Lp ℂ 2 (μI L)) ρ ⊆ ball (0 : Lp ℂ 2 (μI L)) ρ0 := ball_subset_ball (min_le_left _ _)
  refine ⟨a, b0, ha.mono hmono, hb.mono hmono, hSC, hmat', ?_, ?_, ?_, ?_⟩
  · -- spectral statement
    intro u hu
    have hab := fun v => hmat' u hu (ctx_of_ball hL hr hr2 n u (hgood u hu)).hsmall v
    obtain ⟨hmult, hin1, hin2⟩ := QuantumNLS.Local003Mult.operator_multiplicity hL hr hr2 n u (hgood u hu)
      (a u) (b0 u) hab
    refine ⟨hmult, hin1, hin2, fun lam hlam h1 h2 => ?_, ?_⟩
    · exact QuantumNLS.Local003Spectrum.spectrum_resolvent (n := n) hL hr hr2 (hgood u hu) (a u) (b0 u) hab
        lam hlam h1 h2
    · constructor
      · intro h
        have h' := Complex.ofReal_injective h
        have : ‖b0 u‖ = 0 := by linarith
        exact norm_eq_zero.mp this
      · intro h
        rw [h]; simp
  · exact fun w hw => analyticAt_const.mul (hb.mono hmono w hw)
  · -- cubic estimate
    intro u hu
    have hℓ := first_order (κ := κ) hL hr hr2 n F0 hF0e hP0 hκ.le u (G u) (hMul u)
    have hkℓ : k * (2 * Complex.I * ((Real.sqrt (κ / L) : ℝ) : ℂ)) = 1 := by
      rw [hk, Real.sqrt_div hκ.le L]
      have h1 : ((Real.sqrt κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqκ.ne'
      have h2 : ((Real.sqrt L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsqL.ne'
      push_cast
      field_simp
    have hc := hcub u (hρ1 u hu)
    rw [hℓ, ← hbe u hu] at hc
    have e : k * b0 u - uCoeff L n u = k * (b0 u - 2 * Complex.I * ((Real.sqrt (κ / L) : ℝ) : ℂ) * uCoeff L n u) := by
      rw [mul_sub]
      congr 1
      rw [← mul_assoc, hkℓ, one_mul]
    rw [e, norm_mul]
    calc ‖k‖ * ‖b0 u - 2 * Complex.I * ((Real.sqrt (κ / L) : ℝ) : ℂ) * uCoeff L n u‖
        ≤ ‖k‖ * (C1c κ L r * ‖u‖ ^ 3) := by gcongr
      _ ≤ ‖k‖ * max (C1c κ L r) (C2c κ L r) * ‖u‖ ^ 3 := by
        have := le_max_left (C1c κ L r) (C2c κ L r)
        have h3 : 0 ≤ ‖u‖ ^ 3 := by positivity
        nlinarith [norm_nonneg k, mul_nonneg (norm_nonneg k) h3]
  · -- derivative estimate
    intro u hu
    have hev : ∀ w ∈ ball (0 : Lp ℂ 2 (μI L)) ρ,
        b0 =ᶠ[nhds w] fun x : Lp ℂ 2 (μI L) => Bf L κ (x : ℝ → ℂ) n r (vec2 1 0) 1 := fun w hw =>
      Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hw) (fun x hx => hbe x hx)
    have h0mem : (0 : Lp ℂ 2 (μI L)) ∈ ball (0 : Lp ℂ 2 (μI L)) ρ := mem_ball_self hρpos
    have hdiff : ∀ w ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, DifferentiableAt ℝ b0 w := fun w hw =>
      ((hder w (hρ1 w hw)).1).congr_of_eventuallyEq (hev w hw)
    have hfd : ∀ w ∈ ball (0 : Lp ℂ 2 (μI L)) ρ, fderiv ℝ (fun w : Lp ℂ 2 (μI L) => k * b0 w) w =
        k • fderiv ℝ b0 w := fun w hw => fderiv_const_mul (hdiff w hw) k
    refine ⟨(hdiff u hu).const_mul k, ?_⟩
    rw [hfd u hu, hfd 0 h0mem]
    have hC : 0 ≤ ‖k‖ * max (C1c κ L r) (C2c κ L r) * ‖u‖ ^ 2 := by positivity
    refine ContinuousLinearMap.opNorm_le_bound _ hC (fun v => ?_)
    have hv := (hder u (hρ1 u hu)).2 v
    rw [(hev u hu).fderiv_eq, (hev 0 h0mem).fderiv_eq]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← mul_sub, norm_mul]
    calc ‖k‖ * ‖(fderiv ℝ (fun x : Lp ℂ 2 (μI L) => Bf L κ (x : ℝ → ℂ) n r (vec2 1 0) 1) u) v -
          (fderiv ℝ (fun x : Lp ℂ 2 (μI L) => Bf L κ (x : ℝ → ℂ) n r (vec2 1 0) 1) 0) v‖
        ≤ ‖k‖ * (C2c κ L r * ‖u‖ ^ 2 * ‖v‖) := by gcongr
      _ ≤ ‖k‖ * max (C1c κ L r) (C2c κ L r) * ‖u‖ ^ 2 * ‖v‖ := by
        have := le_max_right (C1c κ L r) (C2c κ L r)
        have h3 : 0 ≤ ‖u‖ ^ 2 * ‖v‖ := by positivity
        nlinarith [norm_nonneg k, mul_nonneg (norm_nonneg k) h3]

/-! ### The DEF-001 profile -/

section Profile
open QuantumNLS.Local002Bridge QuantumNLS.PhysicalTensor

/-- The report Fourier coefficient `û(n) = ⟨e_n, u⟩` of the profile is the interval coefficient of its interval class. -/
lemma coeff_eq_uCoeff [Fact (0 < L)] (v : L2T L) (n : ℤ) :
    QuantumNLS.Fourier.coeff L (v : AddCircle L → ℂ) n = uCoeff L n (toInterval L v) := by
  have hL : 0 < L := Fact.out
  unfold QuantumNLS.Fourier.coeff
  rw [← AddCircle.integral_preimage L 0 (fun x : AddCircle L =>
    conj (QuantumNLS.Fourier.mode L n x) * (v : AddCircle L → ℂ) x)]
  unfold uCoeff
  rw [zero_add, ← integral_const_mul]
  have hae := toInterval_coe L v
  show ∫ a in Ioc 0 L, _ = ∫ x, _ ∂(μI L)
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]
  have hc : conj (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (x : ℂ) / (L : ℂ)) =
      -(Complex.I * (pm L n : ℂ) * (x : ℂ)) := by
    simp [pm, Complex.conj_ofReal, map_div₀, map_ofNat]
    ring
  rw [QuantumNLS.Fourier.mode_coe, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, hc]
  unfold circleRep
  ring

lemma smallCompression_congr {u u' : ℝ → ℂ} (h : u =ᵐ[μI L] u') (n : ℤ) (r : ℝ) :
    SmallCompression L κ u n r ↔ SmallCompression L κ u' n r := by
  unfold SmallCompression compressionMatrix
  rw [perturbedProj_congr h]

lemma analytic_comp_T [Fact (0 < L)] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {ρ : ℝ}
    {F : Lp ℂ 2 (μI L) → X} (hF : AnalyticOnNhd ℝ F (ball 0 ρ)) :
    AnalyticOnNhd ℝ (fun v : L2T L => F (toIntervalR L v)) (ball 0 ρ) := by
  refine AnalyticOnNhd.comp (t := ball (0 : Lp ℂ 2 (μI L)) ρ) hF ((toIntervalR L).analyticOnNhd _) ?_
  intro v hv
  rw [mem_ball_zero_iff] at hv ⊢
  rw [toIntervalR_apply, norm_toInterval]; exact hv

theorem reset_uniform_reduction_profile [Fact (0 < L)] (hL : 0 < L) (hκ : 0 < κ) (hr : 0 < r)
    (hr2 : r < 2 * Real.pi / L) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
      ∃ (a : L2T L → ℝ) (b : L2T L → ℂ),
        AnalyticOnNhd ℝ a (ball 0 ρ) ∧ AnalyticOnNhd ℝ b (ball 0 ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, SmallCompression L κ (circleRep u) n r) ∧
        (∀ u ∈ ball (0 : L2T L) ρ, ∀ h : SmallCompression L κ (circleRep u) n r, ∀ v : E2,
          reducedMatrix2 L κ (circleRep u) n r h v =
            vec2 ((a u : ℂ) * v 0 + conj (b u) * v 1) (b u * v 0 + (a u : ℂ) * v 1)) ∧
        (∀ u ∈ ball (0 : L2T L) ρ,
          (∀ lam : ℂ, ‖lam - (pm L n : ℂ)‖ < r →
            ∃ Eig : Submodule ℂ (H2 L),
              (∀ f : H2 L, f ∈ Eig ↔ (f, lam • f) ∈ LuGraph L κ (circleRep u) (parity n)) ∧
              Module.finrank ℂ Eig =
                Multiset.count lam {((a u + ‖b u‖ : ℝ) : ℂ), ((a u - ‖b u‖ : ℝ) : ℂ)}) ∧
          ‖((a u + ‖b u‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r ∧ ‖((a u - ‖b u‖ : ℝ) : ℂ) - (pm L n : ℂ)‖ < r ∧
          (∀ lam : ℂ, ‖lam - (pm L n : ℂ)‖ < r → lam ≠ ((a u + ‖b u‖ : ℝ) : ℂ) →
            lam ≠ ((a u - ‖b u‖ : ℝ) : ℂ) →
            ∃ R : H2 L →L[ℂ] H2 L, IsResolvent L κ (circleRep u) (parity n) lam R) ∧
          (((a u + ‖b u‖ : ℝ) : ℂ) = ((a u - ‖b u‖ : ℝ) : ℂ) ↔ b u = 0)) ∧
        AnalyticOnNhd ℝ (fun u : L2T L => ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b u)
          (ball 0 ρ) ∧
        (∀ u ∈ ball (0 : L2T L) ρ,
          ‖((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b u -
              QuantumNLS.Fourier.coeff L (u : AddCircle L → ℂ) n‖ ≤ C * ‖u‖ ^ 3) ∧
        (∀ u ∈ ball (0 : L2T L) ρ,
          DifferentiableAt ℝ (fun w : L2T L =>
            ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b w) u ∧
          ‖fderiv ℝ (fun w : L2T L =>
              ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b w) u -
            fderiv ℝ (fun w : L2T L =>
              ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) * b w) 0‖ ≤ C * ‖u‖ ^ 2) := by
  obtain ⟨ρ, hρ, C, hC, h⟩ := reset_uniform_reduction (κ := κ) hL hκ hr hr2
  refine ⟨ρ, hρ, C, hC, fun n => ?_⟩
  obtain ⟨a, b, ha, hb, hsc, hmat, hspec, hg, hcub, hder⟩ := h n
  set T := toIntervalR L with hT
  set k : ℂ := ((Real.sqrt L : ℝ) : ℂ) / (2 * Complex.I * (Real.sqrt κ : ℂ)) with hk
  have hmem : ∀ v ∈ ball (0 : L2T L) ρ, T v ∈ ball (0 : Lp ℂ 2 (μI L)) ρ := fun v hv => by
    rw [mem_ball_zero_iff] at hv ⊢
    rw [hT, toIntervalR_apply, norm_toInterval]; exact hv
  have he : ∀ v : L2T L, (T v : ℝ → ℂ) =ᵐ[μI L] circleRep v := fun v => toInterval_coe L v
  refine ⟨fun v => a (T v), fun v => b (T v), analytic_comp_T ha, analytic_comp_T hb, ?_, ?_, ?_,
    analytic_comp_T hg, ?_, ?_⟩
  · intro v hv
    exact (smallCompression_congr (he v) n r).mp (hsc (T v) (hmem v hv))
  · intro v hv h w
    have h' : SmallCompression L κ (T v : ℝ → ℂ) n r := (smallCompression_congr (he v) n r).mpr h
    have e := hmat (T v) (hmem v hv) h' w
    rw [reducedMatrix2_eq] at e ⊢
    rw [← QuantumNLS.Local003Odd.Bf_congr (he v) n r]
    exact e
  · intro v hv
    obtain ⟨m1, i1, i2, r1, iff⟩ := hspec (T v) (hmem v hv)
    refine ⟨fun lam hlam => ?_, i1, i2, fun lam hlam h1 h2 => ?_, iff⟩
    · obtain ⟨Eig, hEig, hdim⟩ := m1 lam hlam
      refine ⟨Eig, fun f => ?_, hdim⟩
      rw [hEig f, LuGraph_congr (he v)]
    · obtain ⟨R, hR⟩ := r1 lam hlam h1 h2
      exact ⟨R, (isResolvent_congr (he v) _ _ R).mp hR⟩
  · intro v hv
    have := hcub (T v) (hmem v hv)
    rw [coeff_eq_uCoeff v n]
    have hn : ‖T v‖ = ‖v‖ := by rw [hT, toIntervalR_apply, norm_toInterval]
    rw [hn] at this
    exact this
  · intro v hv
    obtain ⟨hd, hb2⟩ := hder (T v) (hmem v hv)
    have hTd : ∀ w : L2T L, DifferentiableAt ℝ T w := fun w => T.differentiableAt
    have hnorm : ‖T v‖ = ‖v‖ := by rw [hT, toIntervalR_apply, norm_toInterval]
    have hTn : ‖T‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => ?_)
      rw [hT, toIntervalR_apply, norm_toInterval, one_mul]
    have h0mem : (0 : L2T L) ∈ ball (0 : L2T L) ρ := mem_ball_self hρ
    have hd0 : DifferentiableAt ℝ (fun w : Lp ℂ 2 (μI L) => k * b w) (T 0) := by
      have := (hder (T 0) (hmem 0 h0mem)).1
      exact this
    have e1 : fderiv ℝ (fun w : L2T L => k * b (T w)) v =
        (fderiv ℝ (fun w : Lp ℂ 2 (μI L) => k * b w) (T v)).comp (T : L2T L →L[ℝ] Lp ℂ 2 (μI L)) := by
      have := fderiv_comp (𝕜 := ℝ) v hd (hTd v)
      rw [T.fderiv] at this
      exact this
    have e0 : fderiv ℝ (fun w : L2T L => k * b (T w)) 0 =
        (fderiv ℝ (fun w : Lp ℂ 2 (μI L) => k * b w) 0).comp (T : L2T L →L[ℝ] Lp ℂ 2 (μI L)) := by
      have := fderiv_comp (𝕜 := ℝ) (0 : L2T L) hd0 (hTd 0)
      rw [T.fderiv, map_zero] at this
      exact this
    refine ⟨hd.comp v (hTd v), ?_⟩
    rw [e1, e0, ← ContinuousLinearMap.sub_comp]
    calc ‖((fderiv ℝ (fun w : Lp ℂ 2 (μI L) => k * b w) (T v) -
          fderiv ℝ (fun w : Lp ℂ 2 (μI L) => k * b w) 0).comp T)‖
        ≤ ‖fderiv ℝ (fun w : Lp ℂ 2 (μI L) => k * b w) (T v) -
          fderiv ℝ (fun w : Lp ℂ 2 (μI L) => k * b w) 0‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * ‖T v‖ ^ 2) * 1 := by gcongr
      _ = C * ‖v‖ ^ 2 := by rw [hnorm, mul_one]

end Profile

end QuantumNLS.Local003Final
#print axioms QuantumNLS.Local003Final.reset_uniform_reduction
#print axioms QuantumNLS.Local003Final.coeff_eq_uCoeff
#print axioms QuantumNLS.Local003Final.reset_uniform_reduction_profile
