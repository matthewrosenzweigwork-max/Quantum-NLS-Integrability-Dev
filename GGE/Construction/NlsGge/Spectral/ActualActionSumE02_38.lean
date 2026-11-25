import NlsGge.Spectral.ActualGapActionContinuityE02_38
import NlsGge.Spectral.ActualTraceFormulaQ024E02_38
import NlsGge.Hierarchy.PlaneCoverIdentification38
import NlsGge.Hierarchy.GaussianTailCovarianceBernstein38
import NlsGge.Hierarchy.FullEnergyPlaneConvergence38
import NlsGge.Measure.CountableSupport
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Interval
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis NlsGge.HierarchyRiccati.Core

/-! # E01.06a: `Σ I_n = ‖u‖²_{L²}` for H¹ fields (campaign 38)

Route: Fourier truncations `u_N` are smooth, so the smooth trace formulas give `(2/π)∫v_N = ‖u_N‖²` and a bound
on `(2/π)∫(2t)² v_N = Q₂(u_N)` that is uniform in `N`. Locally uniform convergence `v_N → v` plus uniform
`1/(1+4L²)` tails give `(2/π)∫v = ‖u‖²`. Finally `∫v = Σ_n ∫_{g_n} v` (disjoint level sets, `v = 0` off them). -/

/-- Fourier truncation coordinates. -/
def truncPlaneE02_38 (u : PhysicalL2) (N : ℕ) : FourierPlane N :=
  fun i => physicalFourier u (modeIndex N i)

/-- Fourier truncation as an L² field. -/
def truncL2E02_38 (u : PhysicalL2) (N : ℕ) : PhysicalL2 := planeL2 N (truncPlaneE02_38 u N)

theorem physicalFourier_sub_E02_38 (a b : PhysicalL2) (n : ℤ) :
    physicalFourier (((a - b : PhysicalL2)) : PhysicalCircle → ℂ) n =
      physicalFourier a n - physicalFourier b n := by
  rw [← physicalFourierL2_apply, ← physicalFourierL2_apply, ← physicalFourierL2_apply, map_sub]
  rfl

theorem physicalFourier_truncL2_in_E02_38 (u : PhysicalL2) (N : ℕ) (n : ℤ)
    (hlo : -(N:ℤ) ≤ n) (hhi : n ≤ N) :
    physicalFourier (truncL2E02_38 u N) n = physicalFourier u n := by
  obtain ⟨i, rfl⟩ := modeIndex_covers N n hlo hhi
  unfold truncL2E02_38
  rw [physicalFourier_planeL2, physicalFourier_planeField]
  rfl

theorem physicalFourier_truncL2_out_E02_38 (u : PhysicalL2) (N : ℕ) (n : ℤ)
    (hn : n < -(N:ℤ) ∨ (N:ℤ) < n) :
    physicalFourier (truncL2E02_38 u N) n = 0 := by
  unfold truncL2E02_38
  rw [physicalFourier_planeL2, physicalFourier_planeField_outside N _ n hn]

theorem tendsto_truncL2_E02_38 (u : PhysicalL2) :
    Tendsto (fun N : ℕ => ‖truncL2E02_38 u N - u‖) atTop (𝓝 0) := by
  have hsq : Tendsto (fun N : ℕ => ‖truncL2E02_38 u N - u‖ ^ 2) atTop (𝓝 0) := by
    have heq : ∀ N : ℕ, ‖truncL2E02_38 u N - u‖ ^ 2 =
        ∑' n : ℤ, ‖physicalFourier (((truncL2E02_38 u N - u : PhysicalL2)) : PhysicalCircle → ℂ) n‖ ^ 2 :=
      fun N => (hasSum_physicalFourier_sq _).tsum_eq.symm
    simp_rw [heq]
    have h0 : (0:ℝ) = ∑' n : ℤ, (0:ℝ) := by simp
    rw [h0]
    refine tendsto_tsum_of_dominated_convergence (summable_physicalFourier_sq u) ?_ ?_
    · intro n
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop n.natAbs] with N hN
      have hlo : -(N:ℤ) ≤ n := by omega
      have hhi : n ≤ (N:ℤ) := by omega
      rw [physicalFourier_sub_E02_38, physicalFourier_truncL2_in_E02_38 u N n hlo hhi]
      simp
    · refine Eventually.of_forall fun N n => ?_
      rw [physicalFourier_sub_E02_38, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      by_cases h : -(N:ℤ) ≤ n ∧ n ≤ N
      · rw [physicalFourier_truncL2_in_E02_38 u N n h.1 h.2]; simp
      · have h' : n < -(N:ℤ) ∨ (N:ℤ) < n := by omega
        rw [physicalFourier_truncL2_out_E02_38 u N n h']; simp
  have := hsq.sqrt
  simp only [Real.sqrt_zero] at this
  refine this.congr fun N => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-- Sums over the plane indices are bounded by the full series. -/
theorem plane_sum_le_tsum_E02_38 (N : ℕ) (g : ℤ → ℝ) (hg : ∀ n, 0 ≤ g n) (hs : Summable g) :
    ∑ i : Fin (2 * N + 1), g (modeIndex N i) ≤ ∑' n : ℤ, g n := by
  classical
  rw [← Finset.sum_image (f := g) (fun a _ b _ h => modeIndex_injective N h)]
  exact hs.sum_le_tsum _ (fun n _ => hg n)

theorem truncL2_sobolev_E02_38 (u : PhysicalL2) (N : ℕ) :
    SobolevSquareSummable 1 (physicalFourier (truncL2E02_38 u N)) := by
  have h := sobolevSquareSummable_planeField N (truncPlaneE02_38 u N) 1
  unfold truncL2E02_38
  have he : physicalFourier (planeL2 N (truncPlaneE02_38 u N)) =
      physicalFourier (planeField N (truncPlaneE02_38 u N)) :=
    funext fun n => physicalFourier_planeL2 N _ n
  rw [he]; exact h

theorem truncL2_norm_sq_E02_38 (u : PhysicalL2) (N : ℕ) :
    ‖truncL2E02_38 u N‖ ^ 2 = ∑ i : Fin (2 * N + 1), ‖physicalFourier u (modeIndex N i)‖ ^ 2 :=
  planeL2_norm_sq N _

theorem truncL2_norm_sq_le_E02_38 (u : PhysicalL2) (N : ℕ) :
    ‖truncL2E02_38 u N‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [truncL2_norm_sq_E02_38, ← (hasSum_physicalFourier_sq u).tsum_eq]
  exact plane_sum_le_tsum_E02_38 N (fun n => ‖physicalFourier u n‖ ^ 2) (fun n => by positivity)
    (summable_physicalFourier_sq u)

theorem truncL2_trace_E02_38 (u : PhysicalL2) (N : ℕ) (j : ℕ) :
    Integrable (fun t : ℝ => (2*t)^(2*j) * actualGapHeightE02_38 (truncL2E02_38 u N) t) ∧
    (∫ x in (0:ℝ)..1, riccatiJetEvaluation (planeReal N (truncPlaneE02_38 u N)) x
        (formalChargeIntegrand j)).re =
      (2/Real.pi) * ∫ t : ℝ, (2*t)^(2*j) * actualGapHeightE02_38 (truncL2E02_38 u N) t :=
  actualTraceFormula_E02_38 (truncL2E02_38 u N) (truncL2_sobolev_E02_38 u N) _
    (planeReal_smooth38 N _) (planeReal_periodic N _) (planeReal_cover_ae38 N _) j

theorem truncL2_trace0_E02_38 (u : PhysicalL2) (N : ℕ) :
    (2/Real.pi) * ∫ t : ℝ, actualGapHeightE02_38 (truncL2E02_38 u N) t = ‖truncL2E02_38 u N‖ ^ 2 := by
  have h := actualTraceFormula_Q0_complex_E02_38 (truncL2E02_38 u N) (truncL2_sobolev_E02_38 u N) _
    (planeReal_smooth38 N _) (planeReal_periodic N _) (planeReal_cover_ae38 N _)
  rw [h, planeReal_integral_norm_sq38]
  exact (planeL2_norm_sq N _).symm

/-- `S = Σ ⟨n⟩² |û_n|²` (the squared H¹ norm). -/
def h1SumE02_38 (u : PhysicalL2) : ℝ :=
  ∑' n : ℤ, Real.rpow (japaneseBracket n) (2 * 1) * ‖physicalFourier u n‖ ^ 2

/-- `K = Σ ⟨n⟩⁻²`. -/
def bracketSumE02_38 : ℝ := ∑' n : ℤ, Real.rpow (japaneseBracket n) (-2)

theorem rpow_bracket_two_E02_38 (n : ℤ) :
    Real.rpow (japaneseBracket n) (2 * 1) = 1 + (n:ℝ)^2 := by
  show japaneseBracket n ^ (2 * 1 : ℝ) = _
  have h : (2 * 1 : ℝ) = ((2:ℕ) : ℝ) := by norm_num
  rw [h, Real.rpow_natCast, japaneseBracket, Real.sq_sqrt (by positivity)]

theorem rpow_bracket_neg_two_E02_38 (n : ℤ) :
    Real.rpow (japaneseBracket n) (-2) = 1 / (1 + (n:ℝ)^2) := by
  have hb := japaneseBracket_pos n
  show japaneseBracket n ^ (-2 : ℝ) = _
  have h : (-2 : ℝ) = -((2:ℕ) : ℝ) := by norm_num
  rw [h, Real.rpow_neg hb.le, Real.rpow_natCast, japaneseBracket, Real.sq_sqrt (by positivity),
    one_div]

theorem truncL2_trace2_le_E02_38 (u : PhysicalL2) (hu : SobolevSquareSummable 1 (physicalFourier u))
    (N : ℕ) :
    (2/Real.pi) * ∫ t : ℝ, (2*t)^2 * actualGapHeightE02_38 (truncL2E02_38 u N) t ≤
      4 * Real.pi^2 * h1SumE02_38 u + bracketSumE02_38 * h1SumE02_38 u * ‖u‖^2 := by
  set z := truncPlaneE02_38 u N
  have h := actualTraceFormula_Q2_complex_E02_38 (truncL2E02_38 u N) (truncL2_sobolev_E02_38 u N) _
    (planeReal_smooth38 N z) (planeReal_periodic N z) (planeReal_cover_ae38 N z)
  rw [h, deriv_planeReal]
  have hc1 : Continuous (fun x => ‖planeReal N (derivativePlane N z) x‖ ^ 2) :=
    ((planeReal_smooth38 N _).continuous.norm).pow 2
  have hc2 : Continuous (fun x => ‖planeReal N z x‖ ^ 4) :=
    ((planeReal_smooth38 N _).continuous.norm).pow 4
  have hc3 : Continuous (fun x => ‖planeReal N z x‖ ^ 2) :=
    ((planeReal_smooth38 N _).continuous.norm).pow 2
  rw [intervalIntegral.integral_add (hc1.intervalIntegrable (μ := volume) _ _) (hc2.intervalIntegrable (μ := volume) _ _)]
  set S := h1SumE02_38 u
  set K := bracketSumE02_38
  set A := ∑ i, ‖z i‖
  have hS : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (2 * 1) * ‖physicalFourier u n‖ ^ 2) :=
    hu
  have hKs : Summable (fun n : ℤ => Real.rpow (japaneseBracket n) (-2)) :=
    NlsGge.Measure.summable_japaneseBracket_rpow_neg 2 (by norm_num)
  -- derivative term
  have hD : ∫ x in (0:ℝ)..1, ‖planeReal N (derivativePlane N z) x‖ ^ 2 ≤ 4 * Real.pi^2 * S := by
    rw [planeReal_integral_norm_sq38]
    have hterm : ∀ i : Fin (2 * N + 1), ‖derivativePlane N z i‖ ^ 2 ≤
        4 * Real.pi^2 * (Real.rpow (japaneseBracket (modeIndex N i)) (2 * 1) *
          ‖physicalFourier u (modeIndex N i)‖ ^ 2) := by
      intro i
      rw [rpow_bracket_two_E02_38]
      simp only [derivativePlane, z, truncPlaneE02_38, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.norm_intCast]
      rw [mul_pow, mul_pow, mul_pow, sq_abs]
      nlinarith [sq_nonneg ‖physicalFourier u (modeIndex N i)‖, Real.pi_pos,
        sq_nonneg (Real.pi * ‖physicalFourier u (modeIndex N i)‖)]
    calc ∑ i, ‖derivativePlane N z i‖ ^ 2
        ≤ ∑ i, 4 * Real.pi^2 * (Real.rpow (japaneseBracket (modeIndex N i)) (2 * 1) *
          ‖physicalFourier u (modeIndex N i)‖ ^ 2) := Finset.sum_le_sum fun i _ => hterm i
      _ = 4 * Real.pi^2 * ∑ i, (Real.rpow (japaneseBracket (modeIndex N i)) (2 * 1) *
          ‖physicalFourier u (modeIndex N i)‖ ^ 2) := by rw [Finset.mul_sum]
      _ ≤ 4 * Real.pi^2 * S := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact plane_sum_le_tsum_E02_38 N _ (fun n => mul_nonneg
            (Real.rpow_nonneg (japaneseBracket_pos n).le _) (by positivity)) hS
  -- quartic term
  have hA2 : A ^ 2 ≤ K * S := by
    set c : Fin (2 * N + 1) → ℝ := fun i => 1 + ((modeIndex N i : ℤ) : ℝ) ^ 2
    have hc : ∀ i, 0 < c i := fun i => by positivity
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i : Fin (2 * N + 1) => 1 / Real.sqrt (c i)) (fun i => Real.sqrt (c i) * ‖z i‖)
    have hprod : ∀ i : Fin (2 * N + 1),
        1 / Real.sqrt (c i) * (Real.sqrt (c i) * ‖z i‖) = ‖z i‖ := by
      intro i
      have : 0 < Real.sqrt (c i) := Real.sqrt_pos.mpr (hc i)
      field_simp
    have hsq1 : ∀ i : Fin (2 * N + 1), (1 / Real.sqrt (c i)) ^ 2 =
        Real.rpow (japaneseBracket (modeIndex N i)) (-2) := by
      intro i
      rw [rpow_bracket_neg_two_E02_38, div_pow, Real.sq_sqrt (hc i).le, one_pow]
    have hsq2 : ∀ i : Fin (2 * N + 1), (Real.sqrt (c i) * ‖z i‖) ^ 2 =
        Real.rpow (japaneseBracket (modeIndex N i)) (2 * 1) *
          ‖physicalFourier u (modeIndex N i)‖ ^ 2 := by
      intro i
      rw [mul_pow, Real.sq_sqrt (hc i).le, rpow_bracket_two_E02_38]
      rfl
    simp only [hprod, hsq1, hsq2] at hcs
    have hK1 := plane_sum_le_tsum_E02_38 N _
      (fun n => Real.rpow_nonneg (japaneseBracket_pos n).le _) hKs
    have hS1 := plane_sum_le_tsum_E02_38 N _ (fun n => mul_nonneg
      (Real.rpow_nonneg (japaneseBracket_pos n).le _) (by positivity)) hS
    have hS0 : 0 ≤ ∑ i : Fin (2 * N + 1), Real.rpow (japaneseBracket (modeIndex N i)) (2 * 1) *
        ‖physicalFourier u (modeIndex N i)‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (japaneseBracket_pos _).le _)
        (by positivity)
    have hK0 : 0 ≤ K := tsum_nonneg fun n => Real.rpow_nonneg (japaneseBracket_pos n).le _
    calc A ^ 2 ≤ _ := hcs
      _ ≤ K * S := mul_le_mul hK1 hS1 hS0 hK0
  have hQ : ∫ x in (0:ℝ)..1, ‖planeReal N z x‖ ^ 4 ≤ K * S * ‖u‖ ^ 2 := by
    have hpt : ∀ x ∈ Icc (0:ℝ) 1, ‖planeReal N z x‖ ^ 4 ≤ A ^ 2 * ‖planeReal N z x‖ ^ 2 := by
      intro x _
      have h1 := norm_planeReal_le38 N z x
      have h0 := norm_nonneg (planeReal N z x)
      have : ‖planeReal N z x‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ h0 h1 2
      nlinarith [sq_nonneg ‖planeReal N z x‖]
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      (hc2.intervalIntegrable (μ := volume) _ _) ((hc3.const_mul (A ^ 2)).intervalIntegrable (μ := volume) _ _) hpt
    rw [intervalIntegral.integral_const_mul, planeReal_integral_norm_sq38] at hmono
    have hB : ∑ i, ‖z i‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have := truncL2_norm_sq_le_E02_38 u N
      rw [truncL2_norm_sq_E02_38] at this; exact this
    have hA0 : 0 ≤ A ^ 2 := sq_nonneg _
    calc _ ≤ A ^ 2 * ∑ i, ‖z i‖ ^ 2 := hmono
      _ ≤ (K * S) * ‖u‖ ^ 2 := mul_le_mul hA2 hB (Finset.sum_nonneg fun _ _ => by positivity)
          (le_trans hA0 hA2)
  linarith

/-- Tail bound: the mass of `Φ` outside `[-L, L]` is at most `∫(1+(2t)²)Φ / (1+4L²)`. -/
theorem tail_le_E02_38 (Φ : ℝ → ℝ) (h0 : ∀ t, 0 ≤ Φ t) (hΦ : Integrable Φ)
    (hH : Integrable (fun t => (1 + (2*t)^2) * Φ t)) (L : ℝ) (hL : 0 ≤ L) :
    (∫ t, Φ t) - (∫ t in Icc (-L) L, Φ t) ≤ (∫ t, (1 + (2*t)^2) * Φ t) / (1 + 4*L^2) := by
  have hpos : 0 < 1 + 4*L^2 := by positivity
  have hsplit := integral_add_compl (s := Icc (-L) L) measurableSet_Icc hΦ
  rw [← hsplit, add_sub_cancel_left, le_div_iff₀ hpos]
  have h1 : ∫ t in (Icc (-L) L)ᶜ, (1 + 4*L^2) * Φ t ≤ ∫ t in (Icc (-L) L)ᶜ, (1 + (2*t)^2) * Φ t := by
    refine setIntegral_mono_on (hΦ.integrableOn.const_mul _) hH.integrableOn
      measurableSet_Icc.compl ?_
    intro t ht
    have ht' : L < |t| := by
      by_contra hc; push Not at hc
      exact ht ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have : L^2 ≤ t^2 := by
      have := mul_le_mul ht'.le ht'.le hL (abs_nonneg t)
      nlinarith [sq_abs t]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (h0 t)
  have h2 : ∫ t in (Icc (-L) L)ᶜ, (1 + (2*t)^2) * Φ t ≤ ∫ t, (1 + (2*t)^2) * Φ t :=
    setIntegral_le_integral hH (Eventually.of_forall fun t => mul_nonneg (by positivity) (h0 t))
  rw [integral_const_mul] at h1
  linarith

/-- **TF₀ on H¹.** `(2/π)∫ v = ‖u‖²_{L²}` for every H¹ field (Q₀ trace formula beyond C^∞). -/
theorem actualGapHeight_integral_eq_normSq_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    Integrable (actualGapHeightE02_38 u) ∧
      (2/Real.pi) * ∫ t, actualGapHeightE02_38 u t = ‖u‖ ^ 2 := by
  have hpi := Real.pi_pos
  set F : ℕ → ℝ → ℝ := fun N => actualGapHeightE02_38 (truncL2E02_38 u N)
  set G : ℝ → ℝ := actualGapHeightE02_38 u
  set H : ℝ → ℝ := fun t => 1 + (2*t)^2
  set B2 := 4 * Real.pi^2 * h1SumE02_38 u + bracketSumE02_38 * h1SumE02_38 u * ‖u‖^2
  set C0 := (Real.pi / 2) * (‖u‖^2 + B2)
  have hF0 : ∀ N t, 0 ≤ F N t := fun N t => actualGapHeightE02_38_nonneg _ t
  have hG0 : ∀ t, 0 ≤ G t := fun t => actualGapHeightE02_38_nonneg _ t
  have hGc : Continuous G := continuous_actualGapHeightE02_38 u
  have hHc : Continuous H := by fun_prop
  have hFint : ∀ N, Integrable (F N) := by
    intro N
    have := (truncL2_trace_E02_38 u N 0).1
    simpa using this
  have hF2int : ∀ N, Integrable (fun t => (2*t)^2 * F N t) := by
    intro N
    have := (truncL2_trace_E02_38 u N 1).1
    simpa using this
  have hHFint : ∀ N, Integrable (fun t => H t * F N t) := by
    intro N
    refine ((hFint N).add (hF2int N)).congr (Eventually.of_forall fun t => ?_)
    simp only [H, Pi.add_apply]; ring
  have hHFle : ∀ N, ∫ t, H t * F N t ≤ C0 := by
    intro N
    have e : ∫ t, H t * F N t = (∫ t, F N t) + (∫ t, (2*t)^2 * F N t) := by
      refine Eq.trans ?_ (integral_add (hFint N) (hF2int N))
      congr 1; funext t; simp only [H]; ring
    have h0 := truncL2_trace0_E02_38 u N
    have h2 := truncL2_trace2_le_E02_38 u hu N
    have hb := truncL2_norm_sq_le_E02_38 u N
    rw [e]
    have : (2/Real.pi) * ((∫ t, F N t) + (∫ t, (2*t)^2 * F N t)) ≤ ‖u‖^2 + B2 := by
      rw [mul_add]; simp only [F] at h0 h2 ⊢; linarith
    have hC : C0 = (Real.pi/2) * (‖u‖^2 + B2) := rfl
    rw [hC]
    have e2 : (∫ t, F N t) + (∫ t, (2*t)^2 * F N t) =
        (Real.pi/2) * ((2/Real.pi) * ((∫ t, F N t) + (∫ t, (2*t)^2 * F N t))) := by
      field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hC0 : 0 ≤ C0 := le_trans (integral_nonneg fun t => mul_nonneg (by positivity) (hF0 0 t))
    (hHFle 0)
  -- locally uniform convergence
  have hconv := tendsto_truncL2_E02_38 u
  have hunif : ∀ L ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ t ∈ Icc (-L) L, |F N t - G t| < ε := by
    intro L ε hε
    obtain ⟨τ, hτ, hclose⟩ := gapHeight_uniform_close_E02_38 u (-L) L ε hε
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hconv) τ hτ
    refine ⟨N₀, fun N hN t ht => hclose _ ?_ t ht⟩
    have := hN₀ N hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact this.le
  -- Step A
  have hA : ∀ L, 0 ≤ L → ∫ t in Icc (-L) L, H t * G t ≤ C0 := by
    intro L hL
    have hIcc : volume (Icc (-L) L) < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε' : 0 < ε / ((1 + 4*L^2) * (2*L + 1)) := by positivity
    obtain ⟨N₀, hN₀⟩ := hunif L _ hε'
    have hint1 : IntegrableOn (fun t => H t * G t) (Icc (-L) L) :=
      (hHc.mul hGc).continuousOn.integrableOn_Icc
    have hint2 : IntegrableOn (fun t => H t * F N₀ t) (Icc (-L) L) := (hHFint N₀).integrableOn
    have hdiff : ‖∫ t in Icc (-L) L, (H t * G t - H t * F N₀ t)‖ ≤
        ((1 + 4*L^2) * (ε / ((1 + 4*L^2) * (2*L + 1)))) * volume.real (Icc (-L) L) := by
      refine norm_setIntegral_le_of_norm_le_const hIcc fun t ht => ?_
      rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < H t)]
      have hHt : H t ≤ 1 + 4*L^2 := by
        simp only [H]
        have : t^2 ≤ L^2 := by nlinarith [ht.1, ht.2]
        nlinarith
      have hd := (hN₀ N₀ le_rfl t ht)
      rw [abs_sub_comm] at hd
      exact mul_le_mul hHt hd.le (abs_nonneg _) (by positivity)
    have hvol : volume.real (Icc (-L) L) = 2 * L := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
    rw [hvol, integral_sub hint1 hint2] at hdiff
    have hle : ∫ t in Icc (-L) L, H t * F N₀ t ≤ C0 :=
      le_trans (setIntegral_le_integral (hHFint N₀)
        (Eventually.of_forall fun t => mul_nonneg (by positivity) (hF0 N₀ t))) (hHFle N₀)
    have hbound : (1 + 4*L^2) * (ε / ((1 + 4*L^2) * (2*L + 1))) * (2*L) ≤ ε := by
      have e : (1 + 4*L^2) * (ε / ((1 + 4*L^2) * (2*L + 1))) * (2*L) =
          ε * (2*L / (2*L + 1)) := by field_simp
      rw [e]
      have : 2*L / (2*L + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    have := (abs_le.mp (le_trans (Real.norm_eq_abs _ ▸ hdiff) hbound)).2
    linarith
  -- Step B
  have hnat : Tendsto (fun i : ℕ => (i:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hnatneg : Tendsto (fun i : ℕ => -(i:ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp hnat
  have hHG : Integrable (fun t => H t * G t) := by
    refine integrable_of_intervalIntegral_norm_bounded (l := atTop) (a := fun i : ℕ => -(i:ℝ))
      (b := fun i : ℕ => (i:ℝ)) C0 (fun i => ?_) hnatneg hnat (Eventually.of_forall fun i => ?_)
    · exact (hHc.mul hGc).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
      rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
      have e : ∫ x in Icc (-(i:ℝ)) i, ‖H x * G x‖ = ∫ x in Icc (-(i:ℝ)) i, H x * G x := by
        congr 1; funext x
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (hG0 x))]
      rw [e]; exact hA i hi
  have hGint : Integrable G := by
    refine hHG.mono' hGc.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hG0 t)]
    have : 1 ≤ H t := by simp only [H]; nlinarith [sq_nonneg (2*t)]
    nlinarith [hG0 t]
  have hHGle : ∫ t, H t * G t ≤ C0 := by
    have ht := intervalIntegral_tendsto_integral hHG hnatneg hnat
    refine le_of_tendsto' ht fun i => ?_
    have hi : (0:ℝ) ≤ i := Nat.cast_nonneg i
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    exact hA i hi
  -- Step C
  have hlim : Tendsto (fun N => ∫ t, F N t) atTop (𝓝 (∫ t, G t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    set L := 2 * C0 / ε + 1
    have hL : 1 ≤ L := by
      have : 0 ≤ 2 * C0 / ε := by positivity
      simp only [L]; linarith
    have hLpos : 0 < 1 + 4*L^2 := by positivity
    have htailbd : C0 / (1 + 4*L^2) ≤ ε / 8 := by
      rw [div_le_iff₀ hLpos]
      have h1 : 2 * C0 / ε * ε = 2 * C0 := by field_simp
      have : 8 * C0 ≤ ε * (1 + 4*L^2) := by
        have hL2 : 4 * L ≤ 4 * L^2 := by nlinarith
        have : ε * (4 * L) = 8 * C0 + 4 * ε := by simp only [L]; rw [mul_add]; field_simp; ring
        nlinarith
      linarith
    have hε2 : 0 < ε / (4 * (2*L + 1)) := by positivity
    obtain ⟨N₀, hN₀⟩ := hunif L _ hε2
    refine ⟨N₀, fun N hN => ?_⟩
    have hIcc : volume (Icc (-L) L) < ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    have hd : ‖∫ t in Icc (-L) L, (F N t - G t)‖ ≤ (ε / (4 * (2*L + 1))) * volume.real (Icc (-L) L) :=
      norm_setIntegral_le_of_norm_le_const hIcc fun t ht => (hN₀ N hN t ht).le
    have hvol : volume.real (Icc (-L) L) = 2 * L := by
      rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]; ring
    rw [hvol, integral_sub (hFint N).integrableOn hGint.integrableOn, Real.norm_eq_abs] at hd
    have hdb : ε / (4 * (2*L + 1)) * (2 * L) ≤ ε / 4 := by
      have e : ε / (4 * (2*L + 1)) * (2 * L) = ε / 4 * (2*L / (2*L+1)) := by field_simp
      rw [e]
      have : 2*L / (2*L + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    have tN := tail_le_E02_38 (F N) (hF0 N) (hFint N) (hHFint N) L (by linarith)
    have tG := tail_le_E02_38 G hG0 hGint hHG L (by linarith)
    have tN' : (∫ t, H t * F N t) / (1 + 4*L^2) ≤ ε / 8 :=
      le_trans (div_le_div_of_nonneg_right (hHFle N) hLpos.le) htailbd
    have tG' : (∫ t, H t * G t) / (1 + 4*L^2) ≤ ε / 8 :=
      le_trans (div_le_div_of_nonneg_right hHGle hLpos.le) htailbd
    have pN : ∫ t in Icc (-L) L, F N t ≤ ∫ t, F N t :=
      setIntegral_le_integral (hFint N) (Eventually.of_forall (hF0 N))
    have pG : ∫ t in Icc (-L) L, G t ≤ ∫ t, G t :=
      setIntegral_le_integral hGint (Eventually.of_forall hG0)
    rw [Real.dist_eq, abs_lt]
    have ha := abs_le.mp (le_trans hd hdb)
    simp only [H] at tN tG tN' tG'
    constructor <;> linarith [ha.1, ha.2]
  -- Step D
  refine ⟨hGint, ?_⟩
  have h1 : Tendsto (fun N => (2/Real.pi) * ∫ t, F N t) atTop (𝓝 ((2/Real.pi) * ∫ t, G t)) :=
    hlim.const_mul _
  have h2 : Tendsto (fun N => (2/Real.pi) * ∫ t, F N t) atTop (𝓝 (‖u‖ ^ 2)) := by
    have hu' : Tendsto (fun N => truncL2E02_38 u N) atTop (𝓝 u) :=
      tendsto_iff_norm_sub_tendsto_zero.mpr hconv
    have := (hu'.norm).pow 2
    refine this.congr fun N => ?_
    exact (truncL2_trace0_E02_38 u N).symm
  exact tendsto_nhds_unique h1 h2

/-- **E01.06a** (v2 A:eq:action, last identity): `Σ_n I_n = ‖u‖²_{L²}` for every H¹ field, with
`I_n = actualGapActionAllE02_38 u n = (2/π)∫_{g_n} v`. -/
theorem actualGapAction_hasSum_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    HasSum (fun n : ℤ => actualGapActionAllE02_38 u n) (‖u‖ ^ 2) := by
  obtain ⟨hint, heq⟩ := actualGapHeight_integral_eq_normSq_E02_38 u hu
  set s : ℤ → Set ℝ := fun n => actualGapLevelSetE02_38 u n
  have hs : ∀ n, s n = Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) :=
    fun n => (actualGapLevelSet_eq_Icc_E02_38 u n).2
  have hm : ∀ n, MeasurableSet (s n) := fun n => by rw [hs n]; exact measurableSet_Icc
  have hd : Pairwise (Function.onFun Disjoint s) := by
    intro n m hnm
    refine Set.disjoint_left.mpr fun x hxn hxm => hnm ?_
    have e1 : actualQuasimomentumRealPartE02_38 u x = (n:ℝ) * Real.pi := hxn
    have e2 : actualQuasimomentumRealPartE02_38 u x = (m:ℝ) * Real.pi := hxm
    have : (n:ℝ) = m := by
      have := e1.symm.trans e2
      exact mul_right_cancel₀ Real.pi_pos.ne' this
    exact_mod_cast this
  have hU := hasSum_integral_iUnion hm hd hint.integrableOn
  have hfull : ∫ x in ⋃ n, s n, actualGapHeightE02_38 u x = ∫ x, actualGapHeightE02_38 u x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    by_contra hv
    obtain ⟨m, hm'⟩ := realPart_int_mul_pi_of_gapHeight_ne_zero_E02_38 u x hv
    exact hx (Set.mem_iUnion.mpr ⟨m, hm'⟩)
  rw [hfull] at hU
  have hterm : ∀ n, (2/Real.pi) * ∫ x in s n, actualGapHeightE02_38 u x = actualGapActionAllE02_38 u n := by
    intro n
    have hab : actualGapLowerAllE02_38 u n ≤ actualGapUpperAllE02_38 u n := by
      obtain ⟨y, hy⟩ := (actualGapLevelSet_eq_Icc_E02_38 u n).1
      have hy' : y ∈ s n := hy
      rw [hs n] at hy'; exact le_trans hy'.1 hy'.2
    rw [hs n, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    rfl
  have := hU.mul_left (2/Real.pi)
  rw [heq] at this
  exact this.congr_fun (fun n => (hterm n).symm) |>.congr_fun (fun _ => rfl)

theorem actualGapAction_tsum_E02_38 (u : PhysicalL2)
    (hu : SobolevSquareSummable 1 (physicalFourier u)) :
    ∑' n : ℤ, actualGapActionAllE02_38 u n = ‖u‖ ^ 2 :=
  (actualGapAction_hasSum_E02_38 u hu).tsum_eq

end NlsGge.SpectralFoundations
end
