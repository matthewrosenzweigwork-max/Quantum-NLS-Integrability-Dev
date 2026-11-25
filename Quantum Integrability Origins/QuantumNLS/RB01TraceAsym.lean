import Mathlib
import QuantumNLS.RB01TraceLip
import QuantumNLS.Q07StripUniformR16

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-11: trace asymptotics with the required quantifiers
(source eq. GB01-trace-asymptotic, `collective_actions.tex:308-331`) for the actual DEF-014 discriminant.

* `two_cos_shift`: `2cos((p_n + w)L/2) = 2(-1)^n cos(Lw/2)` (`p_n = LocalSpectral.pm L n = 2πn/L`).
* `interaction_eq_gauge`: the frozen Q07 interaction matrix of the `L¹` profile `toProfile u` is the RB01-9 gauge
  transfer `W_u(L)` of the physical profile.
* `disc_sub_free_le`: `|Δ_u(z) − 2cos(zL/2)| ≤ 2e^{h L/2}‖W_u(L) − 1‖` for `|Im z| ≤ h`.
* **`trace_asymptotic`**: for every compact set `K ⊂ L²(𝕋_L)` of fields, every compact `W ⊂ ℂ`, and `ε > 0`, there
  is `N` with `|Δ_u(p_n + w) − 2(−1)^n cos(Lw/2)| < ε` for all `|n| > N`, `u ∈ K`, `w ∈ W`.
* **`trace_asymptotic_ray`** (the printed form): for every `u₀`, compact `W` and `ε > 0` there is `N` with
  `|Δ_{t u₀}(p_n + w) − 2(−1)^n cos(Lw/2)| < ε` for `|n| > N`, `t ∈ [0,1]`, `w ∈ W` (uniform in `t` and `w`).
The Riemann–Lebesgue input is the existing compiled `Q07StripUniformR16.uniform_interaction` (strip-uniform decay of the
interaction transfer on compact `L¹` classes), imported read-only; this stage converts it to the trace at `p_n + w`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Filter Topology Set Metric ComplexConjugate
open scoped Matrix Interval
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer QuantumNLS.LinearFundamental
  QuantumNLS.RootInteractionL1 QuantumNLS.RB01TraceGauge QuantumNLS.RB01TraceLip

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

local instance instPseudoMetrizableMat2RB01TA : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance instENormedAddMonoidMat2RB01TA : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.RB01TraceAsym

variable {L : ℝ} [Fact (0 < L)]

theorem two_cos_shift (n : ℤ) (w : ℂ) :
    2 * Complex.cos ((((QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) + w) * L / 2) =
      2 * (-1 : ℂ) ^ n * Complex.cos (L * w / 2) := by
  have hL : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Fact.out : 0 < L).ne'
  have he : (((QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) + w) * L / 2 = L * w / 2 + (n : ℂ) * Real.pi := by
    unfold QuantumNLS.LocalSpectral.pm
    push_cast
    field_simp
    ring
  have hc : Complex.cos ((n : ℂ) * Real.pi) = (-1 : ℂ) ^ n := by
    have h1 : Complex.cos ((n : ℂ) * Real.pi) = ((Real.cos ((n : ℝ) * Real.pi) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cos]; push_cast; ring_nf
    rw [h1, Real.cos_int_mul_pi]; push_cast; ring
  rw [he, Complex.cos_add, hc, Complex.sin_int_mul_pi]
  ring

theorem interaction_eq_gauge (κ : ℝ) (u : PhysicalTensor.L2T L) (z : ℂ) :
    Q07StripInteractionR16.interaction κ (Q07PhysicalProfilesR15.toProfile u) z = gauge κ u z L := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  have hae : (fun x : ℝ => Q07PhysicalProfilesR15.toProfile u x) =ᵐ[volume.restrict (Icc 0 L)]
      L2SpatialTransfer.profile u := by
    rw [← restrict_Ioc_eq_restrict_Icc]
    exact Q07PhysicalProfilesR15.toProfile_ae u
  have hA : Bc κ (fun x => Q07PhysicalProfilesR15.toProfile u x) z =ᵐ[volume.restrict (Icc 0 L)]
      Bc κ (L2SpatialTransfer.profile u) z := by
    filter_upwards [hae] with x hx
    simp only [Bc, hx]
  unfold Q07StripInteractionR16.interaction RB01TraceGauge.gauge
  exact transfer_eq_of_ae hL hA ⟨hL, le_rfl⟩

theorem disc_sub_free_le (κ : ℝ) (u : PhysicalTensor.L2T L) {z : ℂ} {h : ℝ} (hz : |z.im| ≤ h) :
    ‖L2SpatialTransfer.discriminant κ u z - 2 * Complex.cos (z * L / 2)‖ ≤
      2 * Real.exp (h * L / 2) * ‖gauge κ u z L - 1‖ := by
  have hL : 0 ≤ L := (Fact.out : 0 < L).le
  rw [← disc_zero (L := L) κ z, disc_sub_eq, RB01TraceLip.gauge_zero]
  refine (abs_trace_le _).trans ?_
  have hE : ‖freeE z L‖ ≤ Real.exp (h * L / 2) := by
    refine (norm_freeE_le z (L := L) ⟨hL, le_rfl⟩).trans (Real.exp_le_exp.2 ?_)
    have := mul_le_mul_of_nonneg_right hz hL
    linarith
  calc 2 * ‖freeE z L * (gauge κ u z L - 1)‖ ≤ 2 * (‖freeE z L‖ * ‖gauge κ u z L - 1‖) := by
        gcongr; exact norm_mul_le _ _
    _ ≤ 2 * (Real.exp (h * L / 2) * ‖gauge κ u z L - 1‖) := by gcongr
    _ = _ := by ring

/-- **eq. GB01-trace-asymptotic**, uniform on compact field sets and compact `w` sets. -/
theorem trace_asymptotic (κ : ℝ) {K : Set (PhysicalTensor.L2T L)} (hK : IsCompact K) {W : Set ℂ}
    (hW : IsCompact W) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ u ∈ K, ∀ w ∈ W,
      ‖L2SpatialTransfer.discriminant κ u ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w) -
        2 * (-1 : ℂ) ^ n * Complex.cos (L * w / 2)‖ < ε := by
  have hL : 0 < L := Fact.out
  obtain ⟨B, hB⟩ := hW.isBounded.exists_norm_le
  set B' := max B 0 with hB'
  have hB0 : 0 ≤ B' := le_max_right _ _
  set C := 2 * Real.exp (B' * L / 2) with hC
  have hCpos : 0 < C := by positivity
  have hε' : 0 < ε / C := div_pos hε hCpos
  have hev := Q07StripUniformR16.uniform_interaction (κ := κ) hL.le
    (hK.image Q07PhysicalProfilesR15.toProfile.continuous) B' hε'
  rw [cocompact_eq_atBot_atTop, ← comap_abs_atTop, eventually_comap, eventually_atTop] at hev
  obtain ⟨T, hT⟩ := hev
  obtain ⟨N, hN⟩ := exists_nat_ge ((T + B') * L / (2 * Real.pi))
  refine ⟨N, fun n hn u hu w hw => ?_⟩
  set z : ℂ := (QuantumNLS.LocalSpectral.pm L n : ℂ) + w with hz
  have hwn : ‖w‖ ≤ B' := (hB w hw).trans (le_max_left _ _)
  have him : |z.im| ≤ B' := by
    have : z.im = w.im := by simp [hz]
    rw [this]; exact (Complex.abs_im_le_norm w).trans hwn
  have hre : T ≤ |z.re| := by
    have hzre : z.re = QuantumNLS.LocalSpectral.pm L n + w.re := by simp [hz]
    have hpm : |QuantumNLS.LocalSpectral.pm L n| = 2 * Real.pi * |(n : ℝ)| / L := by
      unfold QuantumNLS.LocalSpectral.pm
      rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h1 : (T + B') * L / (2 * Real.pi) < |(n : ℝ)| := lt_of_le_of_lt hN hn
    have h2 : T + B' < 2 * Real.pi * |(n : ℝ)| / L := by
      rw [lt_div_iff₀ hL]
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)] at h1
      linarith
    have h3 : |w.re| ≤ B' := (Complex.abs_re_le_norm w).trans hwn
    have h4 := abs_add_le (QuantumNLS.LocalSpectral.pm L n + w.re) (-w.re)
    simp only [add_neg_cancel_right, abs_neg] at h4
    rw [hzre]
    linarith
  have hspec : Q07StripInteractionR16.spectral z.re z.im = z := by
    unfold Q07StripInteractionR16.spectral; rw [mul_comm]; exact Complex.re_add_im z
  have hi := hT |z.re| hre z.re rfl (Q07PhysicalProfilesR15.toProfile u) (mem_image_of_mem _ hu) z.im him
  rw [hspec, interaction_eq_gauge] at hi
  have hd := disc_sub_free_le κ u him
  rw [show z * (L : ℂ) / 2 = (((QuantumNLS.LocalSpectral.pm L n : ℝ) : ℂ) + w) * L / 2 by rw [hz],
    two_cos_shift] at hd
  calc _ ≤ C * ‖gauge κ u z L - 1‖ := hd
    _ < C * (ε / C) := mul_lt_mul_of_pos_left hi hCpos
    _ = ε := mul_div_cancel₀ ε hCpos.ne'

/-- The printed form: along the ray `t u₀`, `t ∈ [0,1]`, uniformly in `t` and `w`. -/
theorem trace_asymptotic_ray (κ : ℝ) (u₀ : PhysicalTensor.L2T L) {W : Set ℂ} (hW : IsCompact W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℤ, (N : ℝ) < |(n : ℝ)| → ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ W,
      ‖L2SpatialTransfer.discriminant κ (t • u₀) ((QuantumNLS.LocalSpectral.pm L n : ℂ) + w) -
        2 * (-1 : ℂ) ^ n * Complex.cos (L * w / 2)‖ < ε := by
  have hK : IsCompact ((fun t : ℝ => t • u₀) '' Icc 0 1) :=
    isCompact_Icc.image (continuous_id.smul continuous_const)
  obtain ⟨N, hN⟩ := trace_asymptotic κ hK hW hε
  exact ⟨N, fun n hn t ht w hw => hN n hn _ (mem_image_of_mem _ ht) w hw⟩

end QuantumNLS.RB01TraceAsym

#print axioms QuantumNLS.RB01TraceAsym.two_cos_shift
#print axioms QuantumNLS.RB01TraceAsym.interaction_eq_gauge
#print axioms QuantumNLS.RB01TraceAsym.disc_sub_free_le
#print axioms QuantumNLS.RB01TraceAsym.trace_asymptotic
#print axioms QuantumNLS.RB01TraceAsym.trace_asymptotic_ray
