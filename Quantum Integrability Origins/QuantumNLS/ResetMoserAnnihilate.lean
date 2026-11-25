import QuantumNLS.ResetMoserField

/-!
# `thm:reset-moser` (LOCAL-017), stage M1b: `Y_t(z) ∈ 𝒯_z` and `dq_n(z) Y_t(z) = 0` on all of `B_R`

Source: `symplectic_correction.tex`, "The deformation and its invariant ball": "If every coordinate of `z` is nonzero, then `ℋ = 𝒯_z ⊕ i𝒯_z` as a real orthogonal decomposition. Both `ω` and `Ω^t` vanish on `𝒯_z × 𝒯_z`. The map from `i𝒯_z` to `𝒯_z^*` induced by `ω` is an isomorphism with inverse norm `1/2`. The same is true for `Ω^t` by the perturbation bound. It follows that the `Ω^t` symplectic orthogonal of `𝒯_z` is exactly `𝒯_z`. Equation (eq:reset-moser-field) and the annihilation property of `β⁰` imply `Y_t(z) ∈ 𝒯_z`. Hence `dq_n(z)Y_t(z) = 0` for every `n`. Points with no zero coordinates are dense, and this scalar identity is continuous in `z`. It therefore holds at all points, including every zero stratum."

* `decomp`: `Y = Y∥ + Y⊥` with `Y∥_n ∈ i z_n ℝ`, `Y⊥_n ∈ z_n ℝ` (the real orthogonal decomposition `ℋ = 𝒯_z ⊕ i𝒯_z`, coordinatewise, no division by a vanishing coordinate because all `z_n ≠ 0` here);
* `Ycov_mem_Tz`: the symplectic orthogonality argument (`Ω^t(Y⊥, iY⊥) ≥ (2 − ‖D‖)‖Y⊥‖²`, with `ω(v, iv) = 2‖v‖²`);
* `exists_nonzero_near`: the points with no zero coordinate are dense;
* `dq_Ycov_zero`: the conclusion on `B_R`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section

attribute [local instance] InnerProductSpace.complexToReal

open scoped ComplexConjugate Topology ENNReal
open Filter Set Metric

namespace QuantumNLS.ResetMoser

open QuantumNLS.D01LocalPrimitive QuantumNLS.SymplecticBracket

theorem memlp2_of_le (g : K) {f : ℤ → ℂ} (h : ∀ n, ‖f n‖ ≤ ‖g n‖) : Memℓp f 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  have hg := (lp.memℓp g).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  exact Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => Real.rpow_le_rpow (norm_nonneg _) (h n) (by norm_num)) hg

/-! ## 1. The orthogonal decomposition -/

theorem decomp (z Y : K) (hz : ∀ n, z n ≠ 0) :
    ∃ Yp Yq : K, Y = Yp + Yq ∧ Yp ∈ Tz z ∧ (∀ n, ∃ b : ℝ, Yq n = z n * b) := by
  have hp : Memℓp (fun n => Complex.I * z n * (((Y n / z n).im : ℝ) : ℂ)) 2 := by
    refine memlp2_of_le Y fun n => ?_
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖z n‖ * |(Y n / z n).im| ≤ ‖z n‖ * ‖Y n / z n‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (norm_nonneg _)
      _ = ‖Y n‖ := by rw [norm_div]; field_simp [norm_ne_zero_iff.2 (hz n)]
  have hq : Memℓp (fun n => z n * (((Y n / z n).re : ℝ) : ℂ)) 2 := by
    refine memlp2_of_le Y fun n => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖z n‖ * |(Y n / z n).re| ≤ ‖z n‖ * ‖Y n / z n‖ :=
          mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (norm_nonneg _)
      _ = ‖Y n‖ := by rw [norm_div]; field_simp [norm_ne_zero_iff.2 (hz n)]
  refine ⟨⟨_, hp⟩, ⟨_, hq⟩, ?_, ?_, ?_⟩
  · ext n
    show Y n = Complex.I * z n * (((Y n / z n).im : ℝ) : ℂ) + z n * (((Y n / z n).re : ℝ) : ℂ)
    have h := Complex.re_add_im (Y n / z n)
    have e : Y n = z n * (Y n / z n) := by field_simp [hz n]
    conv_lhs => rw [e, ← h]
    push_cast
    ring
  · intro n
    exact ⟨(Y n / z n).im, rfl⟩
  · intro n
    exact ⟨(Y n / z n).re, rfl⟩

/-! ## 2. `Y ∈ 𝒯_z` at points with all coordinates nonzero -/

theorem Ycov_mem_Tz {z : K} (hz : ∀ n, z n ≠ 0) {D : Form} (hD : ‖D‖ < 1)
    (hDiso : ∀ h ∈ Tz z, ∀ h' ∈ Tz z, D h h' = 0) {b : Cov} (hb : ∀ h ∈ Tz z, b h = 0) :
    Ycov D b ∈ Tz z := by
  obtain ⟨Yp, Yq, hY, hYp, hYq⟩ := decomp z (Ycov D b) hz
  have hIYq : Complex.I • Yq ∈ Tz z := by
    intro n
    obtain ⟨c, hc⟩ := hYq n
    refine ⟨c, ?_⟩
    show Complex.I * Yq n = _
    rw [hc]; ring
  have hio := iota_Ycov hD b (Complex.I • Yq)
  rw [hb _ hIYq, hY] at hio
  have e1 : omega (Yp + Yq) (Complex.I • Yq) = omega Yq (Complex.I • Yq) := by
    have : omega Yp (Complex.I • Yq) = 0 := omega_Tz hYp hIYq
    have h2 : omega (Yp + Yq) (Complex.I • Yq) = omega Yp (Complex.I • Yq) + omega Yq (Complex.I • Yq) := by
      unfold omega
      rw [inner_add_left, Complex.add_im]
      ring
    rw [h2, this, zero_add]
  have e2 : D (Yp + Yq) (Complex.I • Yq) = D Yq (Complex.I • Yq) := by
    rw [map_add, ContinuousLinearMap.add_apply, hDiso Yp hYp _ hIYq, zero_add]
  rw [e1, e2, omega_I_smul] at hio
  -- `2‖Yq‖² + D Yq (i Yq) = 0`, `|D Yq (i Yq)| ≤ ‖D‖ ‖Yq‖²`
  have hb1 : |D Yq (Complex.I • Yq)| ≤ ‖D‖ * ‖Yq‖ * ‖Complex.I • Yq‖ := by
    have := D.le_opNorm₂ Yq (Complex.I • Yq)
    rwa [Real.norm_eq_abs] at this
  have hn : ‖Complex.I • Yq‖ = ‖Yq‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hn] at hb1
  have hYq0 : ‖Yq‖ = 0 := by
    have h1 : 2 * ‖Yq‖ ^ 2 ≤ ‖D‖ * ‖Yq‖ * ‖Yq‖ := by
      have := neg_abs_le (D Yq (Complex.I • Yq))
      linarith
    have h2 : 0 ≤ ‖Yq‖ := norm_nonneg _
    nlinarith [sq_nonneg ‖Yq‖, mul_nonneg h2 h2, norm_nonneg D]
  have hYq' : Yq = 0 := norm_eq_zero.1 hYq0
  rw [hY, hYq', add_zero]
  exact hYp

/-! ## 3. Density of the points with no zero coordinate -/

theorem exists_nonzero_near (z : K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ w : K, (∀ n, w n ≠ 0) ∧ ‖w - z‖ < δ := by
  -- a fixed square-summable positive sequence
  have hsum : Summable fun n : ℤ => ((1 / 4 : ℝ) ^ n.natAbs) := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨by simpa using summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num),
      by simpa using summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num)⟩
  have hc : Memℓp (fun n : ℤ => (((1 / 2 : ℝ) ^ n.natAbs : ℝ) : ℂ)) 2 := by
    rw [memℓp_gen_iff (by norm_num)]
    refine hsum.congr fun n => ?_
    simp only [Complex.norm_real, Real.norm_eq_abs, ENNReal.toReal_ofNat, Real.rpow_two]
    rw [sq_abs, ← pow_mul, mul_comm, pow_mul]
    norm_num
  set c : K := ⟨_, hc⟩ with hcdef
  set ε : ℝ := δ / (2 * (‖c‖ + 1)) with hε
  have hε0 : 0 < ε := by positivity
  have he : Memℓp (fun n => if z n = 0 then ((ε * (1 / 2 : ℝ) ^ n.natAbs : ℝ) : ℂ) else 0) 2 := by
    refine memlp2_of_le (ε • c) fun n => ?_
    by_cases h : z n = 0
    · simp [h, hcdef, Complex.norm_real]
    · simp [h]; positivity
  refine ⟨z + ⟨_, he⟩, fun n => ?_, ?_⟩
  · show z n + (if z n = 0 then ((ε * (1 / 2 : ℝ) ^ n.natAbs : ℝ) : ℂ) else 0) ≠ 0
    by_cases h : z n = 0
    · rw [if_pos h, h, zero_add]
      exact Complex.ofReal_ne_zero.2 (by positivity)
    · rw [if_neg h, add_zero]; exact h
  · rw [add_sub_cancel_left]
    have h1 : ‖(⟨_, he⟩ : K)‖ ≤ ‖ε • c‖ := by
      have hs1 := summable_sq_K (⟨_, he⟩ : K)
      have hs2 := summable_sq_K (ε • c)
      have : ‖(⟨_, he⟩ : K)‖ ^ 2 ≤ ‖ε • c‖ ^ 2 := by
        rw [norm_sq_K, norm_sq_K]
        refine hs1.tsum_le_tsum (fun n => ?_) hs2
        by_cases h : z n = 0
        · show ‖(if z n = 0 then ((ε * (1 / 2 : ℝ) ^ n.natAbs : ℝ) : ℂ) else 0)‖ ^ 2 ≤ _
          simp [h, hcdef, Complex.norm_real]
        · show ‖(if z n = 0 then ((ε * (1 / 2 : ℝ) ^ n.natAbs : ℝ) : ℂ) else 0)‖ ^ 2 ≤ _
          rw [if_neg h, norm_zero]
          exact pow_le_pow_left₀ le_rfl (norm_nonneg _) 2
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).1 this
    have h2 : ‖ε • c‖ = ε * ‖c‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
    have h3 : ε * ‖c‖ < δ := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg c]
    linarith

/-! ## 4. The conclusion on `B_R` -/

/-- **`dq_n(z) Y(z) = 0` on `B_R`**, for the Moser field `Y z = Ycov (D z) (β⁰ z)` of any family of perturbation forms `D`
(in the printed proof `D = D_t = t(Ω − ω)`, `0 ≤ t ≤ 1`): `D` continuous on `B_R`, `‖D z‖ < 1`; `D z` isotropic on `𝒯_z`
at points with all coordinates nonzero; `β⁰` continuous and annihilating `𝒯_z`. -/
theorem dq_Ycov_zero {Dfam : K → Form} {β0 : K → Cov} {R : ℝ}
    (hDc : ContinuousOn Dfam (ball (0 : K) R)) (hβc : ContinuousOn β0 (ball (0 : K) R))
    (hsm : ∀ z ∈ ball (0 : K) R, ‖Dfam z‖ < 1)
    (hiso : ∀ z ∈ ball (0 : K) R, (∀ n, z n ≠ 0) → ∀ h ∈ Tz z, ∀ h' ∈ Tz z, Dfam z h h' = 0)
    (hann : ∀ z ∈ ball (0 : K) R, ∀ h ∈ Tz z, β0 z h = 0) :
    (∀ z ∈ ball (0 : K) R, ∀ n : ℤ, fderiv ℝ (q n) z (Ycov (Dfam z) (β0 z)) = 0) ∧
    (∀ z ∈ ball (0 : K) R, (∀ n, z n ≠ 0) → Ycov (Dfam z) (β0 z) ∈ Tz z) := by
  have hmem : ∀ z ∈ ball (0 : K) R, (∀ n, z n ≠ 0) → Ycov (Dfam z) (β0 z) ∈ Tz z := by
    intro z hz hnz
    exact Ycov_mem_Tz hnz (hsm z hz) (hiso z hz hnz) (hann z hz)
  refine ⟨?_, hmem⟩
  intro z hz n
  have hY : ContinuousOn (fun z => Ycov (Dfam z) (β0 z)) (ball (0 : K) R) := by
    have hp : ContinuousOn (fun z => ((Dfam z, β0 z) : Form × Cov)) (ball (0 : K) R) :=
      hDc.prodMk hβc
    have hcomp : ContinuousOn ((fun p : Form × Cov => Ycov p.1 p.2) ∘
        fun z => ((Dfam z, β0 z) : Form × Cov)) (ball (0 : K) R) :=
      ContinuousOn.comp continuousOn_Ycov hp (fun z hz => by
        show ‖Dfam z‖ < 1
        exact hsm z hz)
    exact hcomp
  have hg : ContinuousOn (fun w => fderiv ℝ (q n) w (Ycov (Dfam w) (β0 w))) (ball (0 : K) R) := by
    have e : (fun w => fderiv ℝ (q n) w (Ycov (Dfam w) (β0 w))) =
        fun w => 2 * (conj (w n) * (Ycov (Dfam w) (β0 w)) n).re := by
      funext w; exact fderiv_q_apply n w _
    rw [e]
    have h1 : ContinuousOn (fun w : K => conj (w n)) (ball (0 : K) R) :=
      (Complex.continuous_conj.comp (evalR n).continuous).continuousOn
    have h2 : ContinuousOn (fun w : K => (Ycov (Dfam w) (β0 w)) n) (ball (0 : K) R) :=
      (evalR n).continuous.comp_continuousOn hY
    exact continuousOn_const.mul (Complex.continuous_re.comp_continuousOn (h1.mul h2))
  by_contra hne
  have hcont := (hg.continuousAt (isOpen_ball.mem_nhds hz))
  have hev : ∀ᶠ w in 𝓝 z, fderiv ℝ (q n) w (Ycov (Dfam w) (β0 w)) ≠ 0 :=
    hcont.eventually_ne hne
  obtain ⟨δ, hδ, hδb⟩ := Metric.mem_nhds_iff.1 (hev.and (isOpen_ball.mem_nhds hz))
  obtain ⟨w, hwnz, hwd⟩ := exists_nonzero_near z (half_pos hδ)
  have hw : w ∈ Metric.ball z δ := by
    rw [mem_ball_iff_norm]; linarith
  obtain ⟨hw1, hw2⟩ := hδb hw
  exact hw1 (dq_Tz (hmem w hw2 hwnz) n)

end QuantumNLS.ResetMoser

-- BEGIN AUTHOR AUDITS
#print axioms QuantumNLS.ResetMoser.decomp
#print axioms QuantumNLS.ResetMoser.Ycov_mem_Tz
#print axioms QuantumNLS.ResetMoser.exists_nonzero_near
#print axioms QuantumNLS.ResetMoser.dq_Ycov_zero
