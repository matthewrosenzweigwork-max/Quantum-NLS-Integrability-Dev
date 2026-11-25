import QuantumNLS.L1TraceGeometry
import QuantumNLS.RootInteractionL1
import QuantumNLS.RootSpectralInputsDischarge

/-! R-B90ACAE9, real-cut checkpoint. These are the actual L1 Volterra
transfers, uniformly over compact profile sets, with no supplied asymptotic
or differential estimate. The full strip and contour-Hessian clauses are
separate obligations. The profile topology here is the interval L1 norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set Filter Topology MeasureTheory Metric
open QuantumNLS.SpatialTransfer QuantumNLS.L1SpatialTransfer
  QuantumNLS.RootInteractionL1 QuantumNLS.RootDiscriminantBound
attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
local instance : TopologicalSpace.PseudoMetrizableSpace Mat2 :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))
local instance : ENormedAddMonoid Mat2 := NormedAddGroup.toENormedAddMonoid

namespace QuantumNLS.Q07RealCutsR15

abbrev Profile (L : ℝ) := Lp ℂ 1 (volume.restrict (Ioc (0 : ℝ) L))

variable {L κ : ℝ}

theorem integrable_profile (hL : 0 ≤ L) (u : Profile L) :
    IntervalIntegrable (fun x : ℝ => u x) volume 0 L :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hL).mpr (L1.integrable_coeFn u)

theorem integral_norm_profile (hL : 0 ≤ L) (u : Profile L) :
    (∫ x in (0 : ℝ)..L, ‖u x‖) = ‖u‖ := by
  rw [intervalIntegral.integral_of_le hL]
  exact (L1.norm_eq_integral_norm u).symm

theorem integral_norm_sub_profile (hL : 0 ≤ L) (u v : Profile L) :
    (∫ x in (0 : ℝ)..L, ‖u x - v x‖) = ‖u - v‖ := by
  rw [intervalIntegral.integral_of_le hL, L1.norm_eq_integral_norm]
  exact integral_congr_ae ((Lp.coeFn_sub u v).fun_comp norm).symm

/-- Real interaction transfer. Its spectral parameter has no effect on the
stability constant. -/
def interaction (κ : ℝ) (u : Profile L) (t : ℝ) : Mat2 :=
  transfer (Bc κ (fun x => u x) (t : ℂ)) L

theorem interaction_sub_le (hL : 0 ≤ L) (u v : Profile L) (t : ℝ) :
    ‖interaction κ u t - interaction κ v t‖ ≤
      Real.sqrt κ * ‖u - v‖ *
        (Real.exp (Real.sqrt κ * ‖u‖) * Real.exp (Real.sqrt κ * ‖v‖)) := by
  have hh := norm_transfer_Bc_sub_le hL (integrable_profile hL u)
    (integrable_profile hL v) κ (t : ℂ) (x := L) ⟨hL, le_rfl⟩
  simpa only [interaction, Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero,
    mul_one, integral_norm_profile hL, integral_norm_sub_profile hL] using hh

theorem Bc_real (κ : ℝ) (u : ℝ → ℂ) (t : ℝ) :
    Bc κ u (t : ℂ) = RootDiscriminantBound.Bm κ u t := by
  rfl

theorem interaction_tendsto (hL : 0 ≤ L) (u : Profile L) :
    Tendsto (interaction κ u) (cocompact ℝ) (𝓝 1) := by
  change Tendsto (fun t : ℝ => transfer (Bm κ (fun x => u x) t) L) _ _
  exact L1TraceGeometry.transfer_tendsto (κ := κ) (integrable_profile hL u) hL

/-- The finite-net argument is applied to a proved stability bound for the
actual transfer, rather than assumed uniform decay. -/
theorem uniform_interaction (hL : 0 ≤ L) {K : Set (Profile L)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∀ u ∈ K, ‖interaction κ u t - 1‖ < ε := by
  classical
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (f := fun u : Profile L => u) continuousOn_id
  let C := Real.sqrt κ * (Real.exp (Real.sqrt κ * B) * Real.exp (Real.sqrt κ * B))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let η := ε / (2 * (C + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨S, hSK, hS, hcover⟩ := hK.finite_cover_balls hη
  have hlim : ∀ v ∈ S, ∀ᶠ t : ℝ in cocompact ℝ, ‖interaction κ v t - 1‖ < ε / 2 := by
    intro v _
    have hh := (interaction_tendsto (κ := κ) hL v).eventually
      (Metric.ball_mem_nhds (1 : Mat2) (half_pos hε))
    simpa only [mem_ball, dist_eq_norm] using hh
  have hfin := hS.eventually_all.2 hlim
  filter_upwards [hfin] with t ht u hu
  obtain ⟨v, hv, huv⟩ := Set.mem_iUnion₂.mp (hcover hu)
  have hvK := hSK hv
  have hst : ‖interaction κ u t - interaction κ v t‖ ≤ C * ‖u - v‖ := by
    refine (interaction_sub_le hL u v t).trans ?_
    have huB := hB u hu
    have hvB := hB v hvK
    have he1 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huB (Real.sqrt_nonneg κ))
    have he2 := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hvB (Real.sqrt_nonneg κ))
    calc
      _ ≤ Real.sqrt κ * ‖u - v‖ *
          (Real.exp (Real.sqrt κ * B) * Real.exp (Real.sqrt κ * B)) := by gcongr
      _ = C * ‖u - v‖ := by dsimp [C]; ring
  have hdist : ‖u - v‖ < η := by simpa only [mem_ball, dist_eq_norm] using huv
  have hsmall : C * ‖u - v‖ < ε / 2 := by
    have h1 : C * ‖u - v‖ ≤ C * η := mul_le_mul_of_nonneg_left hdist.le hC
    have h2 : C * η < ε / 2 := by
      dsimp [η]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2 * (C + 1))]
      nlinarith
    exact h1.trans_lt h2
  have htri := norm_add_le (interaction κ u t - interaction κ v t) (interaction κ v t - 1)
  rw [sub_add_sub_cancel] at htri
  exact htri.trans_lt (by linarith [ht v hv])

/-- Actual real discriminant; no continuous representative is needed. -/
def discriminant (κ : ℝ) (u : Profile L) (t : ℝ) : ℝ :=
  (RootDiscriminantL1.discL1 L κ (fun x => u x) (t : ℂ)).re

/-- Quantitative passage from interaction transfer to discriminant error. -/
theorem discriminant_error_le (hL : 0 < L) (u : Profile L) (t : ℝ) :
    |discriminant κ u t - 2 * Real.cos (t * L / 2)| ≤
      2 * ‖interaction κ u t - 1‖ := by
  have hc : (2 * Real.cos (t * L / 2) : ℂ) = E2c (t : ℂ) L + E1c (t : ℂ) L := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, E1c, E2c, a1c, RootDiscriminantBound.E1, RootDiscriminantBound.E2,
      RootDiscriminantBound.a1] using (RootTraceAsymptotics.two_cos_eq t L).trans (add_comm _ _)
  have hNc := Nc_eq_transfer hL (integrable_profile hL.le u) κ (t : ℂ)
    (x := L) ⟨hL.le, le_rfl⟩
  have hn00 : interaction κ u t 0 0 = E1c (t : ℂ) L *
      RootDiscriminantL1.TT κ (fun x => u x) (t : ℂ) L 0 0 := by
    change transfer (Bc κ (fun x => u x) (t : ℂ)) L 0 0 = _
    rw [← hNc]
    simp [Dc, P1, P2, Matrix.mul_apply, Fin.sum_univ_two]
  have hn11 : interaction κ u t 1 1 = E2c (t : ℂ) L *
      RootDiscriminantL1.TT κ (fun x => u x) (t : ℂ) L 1 1 := by
    change transfer (Bc κ (fun x => u x) (t : ℂ)) L 1 1 = _
    rw [← hNc]
    simp [Dc, P1, P2, Matrix.mul_apply, Fin.sum_univ_two]
  have hE := E1c_mul_E2c (t : ℂ) L
  have hm00 : E2c (t : ℂ) L * interaction κ u t 0 0 =
      RootDiscriminantL1.TT κ (fun x => u x) (t : ℂ) L 0 0 := by
    rw [hn00, ← mul_assoc, mul_comm (E2c (t : ℂ) L), hE, one_mul]
  have hm11 : E1c (t : ℂ) L * interaction κ u t 1 1 =
      RootDiscriminantL1.TT κ (fun x => u x) (t : ℂ) L 1 1 := by
    rw [hn11, ← mul_assoc, hE, one_mul]
  have he : RootDiscriminantL1.discL1 L κ (fun x => u x) (t : ℂ) -
      (2 * Real.cos (t * L / 2) : ℂ) =
      E2c (t : ℂ) L * (interaction κ u t 0 0 - 1) +
        E1c (t : ℂ) L * (interaction κ u t 1 1 - 1) := by
    unfold RootDiscriminantL1.discL1
    rw [Matrix.trace_fin_two, hc, ← hm00, ← hm11]
    ring
  have h00 : ‖interaction κ u t 0 0 - 1‖ ≤ ‖interaction κ u t - 1‖ := by
    have hh := row_sum_le_norm (interaction κ u t - 1) 0
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1), sub_zero] at hh
    linarith [norm_nonneg (interaction κ u t 0 1)]
  have h11 : ‖interaction κ u t 1 1 - 1‖ ≤ ‖interaction κ u t - 1‖ := by
    have hh := row_sum_le_norm (interaction κ u t - 1) 1
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hh
    linarith [norm_nonneg (interaction κ u t 1 0)]
  have hn1 : ‖E1c (t : ℂ) L‖ = 1 := by simp [norm_E1c]
  have hn2 : ‖E2c (t : ℂ) L‖ = 1 := by simp [norm_E2c]
  have hr := Complex.abs_re_le_norm
    (RootDiscriminantL1.discL1 L κ (fun x => u x) (t : ℂ) - (2 * Real.cos (t * L / 2) : ℂ))
  have hr : |discriminant κ u t - 2 * Real.cos (t * L / 2)| ≤
      ‖RootDiscriminantL1.discL1 L κ (fun x => u x) (t : ℂ) - (2 * Real.cos (t * L / 2) : ℂ)‖ := by
    simpa only [discriminant, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, show (2:ℂ).re = (2:ℝ) from rfl, show (2:ℂ).im = (0:ℝ) from rfl, mul_zero, sub_zero] using hr
  refine hr.trans ?_
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hn1, hn2, one_mul, one_mul]
  linarith

/-- Uniform real-axis high-energy asymptotic on a compact L1 class. -/
theorem uniform_real_asymptotic (hL : 0 < L) {K : Set (Profile L)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in cocompact ℝ, ∀ u ∈ K,
      |discriminant κ u t - 2 * Real.cos (t * L / 2)| < ε := by
  filter_upwards [uniform_interaction (κ := κ) hL.le hK (half_pos hε)] with t ht u hu
  exact (discriminant_error_le hL u t).trans_lt (by linarith [ht u hu])


open PROP017UniformN (cutSeq)
open RootSpectralInputsDischarge (cos_cut_bound)

/-- One threshold works for every profile in the compact class and both
signed cut sequences. Each entire interval has |Delta| < 3/2 < 2. -/
theorem uniform_real_cuts (hL : 0 < L) {K : Set (Profile L)} (hK : IsCompact K) :
    ∃ l0 : ℕ, ∀ l : ℕ, l0 ≤ l → ∀ u ∈ K, ∀ a : ℝ,
      (a = cutSeq L l ∨ a = -cutSeq L l) →
      (∀ s : ℝ, |s| < 1 / L → |discriminant κ u (a + s)| < 3 / 2) ∧
        |discriminant κ u a| ≤ 1 / 2 := by
  let : Fact (0 < L) := ⟨hL⟩
  have h1 := uniform_real_asymptotic (κ := κ) hL hK (ε := 1 / 2) (by norm_num)
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup, Filter.eventually_atBot, Filter.eventually_atTop] at h1
  obtain ⟨⟨T2, hT2⟩, ⟨T1, hT1⟩⟩ := h1
  have hT : ∀ t : ℝ, max T1 (-T2) ≤ |t| → ∀ u ∈ K, |discriminant κ u t - 2 * Real.cos (t * L / 2)| < 1 / 2 := by
    intro t ht u hu
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h] at ht
      have := hT1 t (le_trans (le_max_left _ _) ht)
      simpa [Real.dist_eq] using this u hu
    · rw [abs_of_nonpos h] at ht
      have : t ≤ T2 := by have := le_trans (le_max_right _ _) ht; linarith
      have := hT2 t this
      simpa [Real.dist_eq] using this u hu
  obtain ⟨l0, hl0⟩ := exists_nat_gt ((max T1 (-T2) + 1 / L) * L)
  refine ⟨l0, fun l hl u hu a ha => ?_⟩
  have hapos : max T1 (-T2) + 1 / L < |a| := by
    have habs : |a| = cutSeq L l := by
      rcases ha with ha | ha
      · rw [ha]; unfold cutSeq; exact abs_of_nonneg (by positivity)
      · rw [ha, abs_neg]; unfold cutSeq; exact abs_of_nonneg (by positivity)
    rw [habs]
    unfold cutSeq
    rw [lt_div_iff₀ hL]
    have hlle : (l0 : ℝ) ≤ l := by exact_mod_cast hl
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hl0' : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    nlinarith
  have key : ∀ s : ℝ, |s| < 1 / L → |discriminant κ u (a + s)| < 3 / 2 := by
    intro s hs
    have hsL : |s| * L < 1 := by
      have := (lt_div_iff₀ hL).1 hs
      exact this
    have habs : max T1 (-T2) ≤ |a + s| := by
      have := abs_sub_abs_le_abs_sub a (a + s)
      rw [show a - (a + s) = -s by ring, abs_neg] at this
      linarith
    have hd := hT (a + s) habs u hu
    obtain ⟨-, hc⟩ := cos_cut_bound hL l ha s
    have hc2 : |2 * Real.cos ((a + s) * L / 2)| ≤ |s| * L := by
      rw [abs_mul]; norm_num; linarith
    have := abs_sub_abs_le_abs_sub (discriminant κ u (a + s)) (2 * Real.cos ((a + s) * L / 2))
    linarith
  refine ⟨key, ?_⟩
  have hd := hT (a + 0) (by
    rw [add_zero]
    exact le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (by positivity)) hapos))
  have hd := hd u hu
  obtain ⟨hc0, -⟩ := cos_cut_bound hL l ha 0
  rw [add_zero, hc0] at hd
  simp at hd
  linarith [hd]

end QuantumNLS.Q07RealCutsR15
