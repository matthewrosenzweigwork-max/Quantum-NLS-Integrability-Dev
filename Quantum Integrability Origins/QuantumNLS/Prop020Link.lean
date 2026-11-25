import QuantumNLS.Prop019Discharge
import QuantumNLS.Prop020Contour
import QuantumNLS.Prop020Vector

/-!
# PROP-020 (`Q7A:thm:main`), Z3b part 1: the links between PROP-017/018/019 on one event

Source: `window_reconstruction.tex:254` (`Q7A:thm:main`) and its proof. This module provides the pieces of the final
assembly `Prop020Main` (Z3b part 3; part 2 is `Prop020Chain`):

* `linearization_of_bundle`: PROP-019 (`eq:lincompare`) for an arbitrary event family on which the PROP-018 bundle holds
  (W2's `prop019_linearization` proof body verbatim, with the R2 bundle as hypotheses), so that PROP-017/018/019 share one
  event `𝓔_N` and one packet radius `ρ` (as `phase_of_bundle`, `scalar_of_bundle`, `deviation_of_bundle`);
* `fz`, `fz_eq_lam`: the chart agreement: sonnet_fourier's extension `gfun r (iκG, D, s, A)` equals `λ = Prop018Phase.lam`
  within `r/2` of `s(z)` (`cutoff_eq_one`; `(1/2 : ℂ)` versus `(2 : ℂ)⁻¹` by `one_div`); `gθ_eq_pt`, `dθ_eq`;
* `ae_good`: the real-axis parameters of the window contour have measure zero;
* `int_cfc_gen`, `C0_eig`: integrability of `θ ↦ u_θ f_θ(S_N(z_θ))` (copied from the `mp_linearization` / `C0N_eq_C0op`
  proofs) and the action of `C0op` on an actual transfer eigenvector;
* `C0_identify`: on `𝓔_N`, the `C0op` eigenvalue (from `Prop020Diag.C0op_eigen`) is `Prop018Phase.C0ev` with `f = fz`
  (`eigen_eq_sNf`, `ae_good`, `theta_integral_rect`, `pw d 1 p = poly p d`);
* `Lwin` (the printed `L_{N,p}` of `Q7A:eq:linear` along `Γ_N`) and its linearity in the weight (`Lwin_lin`), so that
  `Σ_r t_r L_{N,x^r} = L_{N,p_t}`; `Lwin_eq_Lop`;
* the phase step, the trace-norm chain and the rate exponents are in `Prop020Chain`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop020Link

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN sNsrc sLimsrc)
open QuantumNLS.PROP018Probability (cutN regime_eventually cut_bounds)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs)
open QuantumNLS.PeriodReconstructionCore QuantumNLS.PeriodTwoTerm
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.LabelExactPeriod (rectIntegral)
open QuantumNLS.Prop018Period (poly)
open QuantumNLS.Prop018Phase (lam ach dch qch C0ev logaNf_eq_lam sNsrc_eq sLimsrc_eq gam_sub_nbhd)
open QuantumNLS.Prop018Scalar (A_eq_half norm_sf_le)
open QuantumNLS.Prop019Deviation (eigen_eq_sNf deviation_of_bundle)
open QuantumNLS.Prop019Linearization (MPLinearizationStatement pw continuous_pw rect_mem rect_im_ne gammaN_abs rect_ω
  rect_wlen_le)
open QuantumNLS.Prop020Contour (theta_integral_rect rect_mem_Gam)
open QuantumNLS.Prop020Vector (norm_exp_sub_le diag_apply_le traceNorm_gamma_sub_le)
open QuantumNLS.Prop020Diag (evol_eigen evol_isometry reducedDensityPower_phase)
open QuantumNLS.HaarSummableReconstruction (contAt_gen)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces continuous_zθ continuous_uθ)
open QuantumNLS.MPFamily (BgFam gθ dθ good)
open QuantumNLS.MPChartSmooth (gfun cutoff cutoff_eq_one rad)
open QuantumNLS.MixedTraceNorm (chartLambda chartA chartD)
open QuantumNLS.MixedQuadratures (reOp)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.TraceClass (traceNorm traceNorm_add_le)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis transfer_physicalBasis)

/-! ## 1. PROP-019 on an arbitrary bundle event (W2's proof body verbatim) -/

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- **`linearization_of_bundle`**: W2's `prop019_linearization`, with the PROP-018 moving-contour bundle as hypotheses on an
arbitrary event family `E` (the same hypotheses as `Prop018Phase.phase_of_bundle`). The proof body is W2's, verbatim. -/
theorem linearization_of_bundle (hκ : 0 < κ) (μ : Measure ℝ) {h ρ C0 M η r K Kd θ γ : ℝ} {b : ℕ} (hh : 0 < h)
    (hρ0 : 0 < ρ) (hM1 : 1 ≤ M) (hη : 0 < η) (hr0 : 0 < r) (hK0 : 0 ≤ K) (hθ : 0 < θ) (hγ : 0 < γ)
    (E : (N : ℕ) → Set (MArr N))
    (hev : ∀ᶠ N : ℕ in atTop, ∀ m ∈ E N, ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8),
          ((∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖) ∧
          ‖Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ 1 / 2 ∧
          1 / (2 * M) ≤ ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          3 * η / 4 ≤ ‖DNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z - Af κ (Gfull μ) z‖ ≤ 1 / (2 * M) ∧
          ‖ellf (κ / N) (qAct L κ N m) z - logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
              Complex.I * κ / (N : ℂ) * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ C0 / (N : ℝ) ^ 2) ∧
          (∀ j, |qAct L κ N m j| ≤ (N : ℝ) ^ θ) ∧
          ‖Gfull μ z - GN (qAct L κ N m) z‖ ≤ K * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b) ∧
          (∀ j, r ≤ ‖z - (qAct L κ N m j : ℂ)‖) ∧
          DifferentiableAt ℂ (Gfull μ) z ∧
          η ≤ ‖Df L κ (Gfull μ) z‖ ∧
          ‖Af κ (Gfull μ) z‖ ≤ M ∧ ‖(Af κ (Gfull μ) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
          ∀ n : ℕ, ‖iteratedDeriv n (fun w => sNsrc κ L (qAct L κ N m) w - sLimsrc κ L μ w) z‖ ≤
            n.factorial * (Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n)
    (d k : ℕ)
    (hMP : ∀ d₀ s₁ a₀ c₁ : ℝ, 0 < d₀ → 0 ≤ s₁ → 0 < a₀ → 0 ≤ c₁ →
      MPLinearizationStatement L κ h k d₀ s₁ a₀ c₁) :
      ∃ d₀ s₁ a₀ c₁ C : ℝ, 0 < d₀ ∧ 0 ≤ s₁ ∧ 0 < a₀ ∧ 0 ≤ c₁ ∧ 0 ≤ C ∧
        ∀ᶠ q : ℕ in atTop, ∀ (hN : 1 ≤ k + q) (φ : SymSector ℂ (L2T L) (k + q)), ‖φ‖ = 1 →
          (∀ m ∉ E (k + q), ⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ = 0) →
          ∃ B : BgFam (NbhdN (cutN L θ (k + q)) h (ρ / 8)) d₀ s₁ a₀ c₁,
            B.c0 = (fun z => Complex.I * κ * Gfull μ z) ∧ B.D = Df L κ (Gfull μ) ∧
            B.s = sf L κ (Gfull μ) ∧ B.A = Af κ (Gfull μ) ∧
            ∀ (t : ℝ) (p : ℕ → ℝ),
              traceNorm
                (reducedDensityPower k q
                    ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
                      C0op (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
                        (zθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) θ'))
                        (uθ κ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)))
                        (gθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) B)) 1 φ :
                      SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
                  reducedDensityPower k q
                    ((evol (((((k + q : ℕ) : ℝ) : ℂ)) •
                      Lop (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
                        (zθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) θ'))
                        (uθ κ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)))
                        (dθ (rectPieces (cutN L θ (k + q)) h (pw d t p) (continuous_pw d t p)) B)) 1 φ :
                      SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))) ≤
                ENNReal.ofReal (C * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) *
                  (1 + cutN L θ (k + q)) ^ (d + 1) *
                  ((((k + q : ℕ) : ℝ)) ^ (-γ) + 1 / ((((k + q : ℕ) : ℝ)) ^ θ) ^ b + 1 / ((k + q : ℕ) : ℝ))) := by
  have hL : 0 < L := Fact.out
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM0 : 0 < M := by linarith
  obtain ⟨C, hC0, hCb⟩ := hMP η (M + M * M) (1 / M) (κ * (2 * K + 1 / r)) hη (by positivity) (by positivity)
    (by positivity)
  refine ⟨η, M + M * M, 1 / M, κ * (2 * K + 1 / r),
    C * (2 * Real.pi * κ)⁻¹ * max Kd 0 * (12 * (1 + h) ^ (d + 1)), hη, by positivity, by positivity,
    by positivity, by positivity, ?_⟩
  have hdev := deviation_of_bundle hκ μ (h := h) (ρ := ρ) (Kd := Kd) (θ := θ) (γ := γ) (b := b) E
    (hev.mono fun N hN m hm z hz => ⟨(hN m hm z hz).1.1, (hN m hm z hz).2.2.2.2.2.2.2.2.2 0⟩)
  have hkq : Tendsto (fun q : ℕ => k + q) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat k
  filter_upwards [hkq.eventually (hev.and (hdev.and (regime_eventually hL hθ hγ 1 0)))]
    with q ⟨hevN, hdevN, hreg⟩
  intro hN φ hφ hsupp
  have hNr : (0 : ℝ) < ((k + q : ℕ) : ℝ) := by exact_mod_cast hN
  set a := cutN L θ (k + q) with ha
  have ha2 : 2 ≤ a := by linarith [hreg.1, hreg.2.2.1]
  -- a label of the event (the event is nonempty since `Φ ≠ 0`)
  obtain ⟨m0, hm0⟩ : ∃ m, m ∈ E (k + q) := by
    by_contra hne
    push Not at hne
    have hs := QuantumNLS.RootMeasureTransfer.hasSum_norm_sq (meanField_physicalBasis L (k + q) hN hκ) φ
    have h0 : (fun m => ‖⟪meanField_physicalBasis L (k + q) hN hκ m, φ⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext m; rw [hsupp m (hne m), norm_zero]; ring
    rw [h0] at hs
    have := hs.unique hasSum_zero
    rw [hφ] at this; norm_num at this
  -- the background family
  have hP := fun z (hz : z ∈ NbhdN a h (ρ / 8)) => hevN m0 hm0 z hz
  have hGc : ∀ z ∈ NbhdN a h (ρ / 8), ContinuousAt (Gfull μ) z := fun z hz =>
    (hP z hz).2.2.2.2.1.continuousAt
  have hAc : ∀ z ∈ NbhdN a h (ρ / 8), ContinuousAt (Af κ (Gfull μ)) z := fun z hz =>
    ((hGc z hz).const_mul (Complex.I * κ)).cexp
  have hec : ∀ z, ContinuousAt (ef L) z := fun z => (hasDerivAt_ef L z).continuousAt
  have hAlow : ∀ z ∈ NbhdN a h (ρ / 8), 1 / M ≤ ‖Af κ (Gfull μ) z‖ := fun z hz => by
    have hAi := (hP z hz).2.2.2.2.2.2.2.1
    have hAn : 0 < ‖Af κ (Gfull μ) z‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
    rw [norm_inv] at hAi
    exact (one_div_le hM0 hAn).2 (by rw [one_div]; exact hAi)
  have hGle : ∀ z ∈ NbhdN a h (ρ / 8), ‖Gfull μ z‖ ≤ 2 * K + 1 / r := fun z hz => by
    have hPz := hP z hz
    have hG1 := hPz.2.2.1
    have hN1 : 1 ≤ ((k + q : ℕ) : ℝ) ^ θ := hreg.1
    have hRb : 1 / (((k + q : ℕ) : ℝ) ^ θ) ^ b ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ hN1
    have hGN : ‖GN (qAct L κ (k + q) m0) z‖ ≤ 1 / r := by
      unfold GN
      rw [norm_mul]
      have hs : ‖∑ j, 1 / (z - (qAct L κ (k + q) m0 j : ℂ))‖ ≤ ∑ _j : Fin (k + q), 1 / r := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_div, norm_one]
        exact one_div_le_one_div_of_le hr0 (hPz.2.2.2.1 j)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
      calc ‖1 / ((k + q : ℕ) : ℂ)‖ * ‖∑ j, 1 / (z - (qAct L κ (k + q) m0 j : ℂ))‖ ≤ (1 / ((k + q : ℕ) : ℝ)) * (((k + q : ℕ) : ℝ) * (1 / r)) := by
            refine mul_le_mul (le_of_eq ?_) hs (norm_nonneg _) (by positivity)
            rw [norm_div, norm_one, Complex.norm_natCast]
        _ = 1 / r := by field_simp
    have := norm_sub_le (Gfull μ z - GN (qAct L κ (k + q) m0) z) (-GN (qAct L κ (k + q) m0) z)
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
    have hKb : K * (((k + q : ℕ) : ℝ) ^ (-γ) + 1 / (((k + q : ℕ) : ℝ) ^ θ) ^ b) ≤ K * 2 :=
      mul_le_mul_of_nonneg_left (by linarith [hreg.2.2.2.2]) hK0
    linarith
  let B : BgFam (NbhdN a h (ρ / 8)) η (M + M * M) (1 / M) (κ * (2 * K + 1 / r)) :=
    { c0 := fun z => Complex.I * κ * Gfull μ z
      D := Df L κ (Gfull μ)
      s := sf L κ (Gfull μ)
      A := Af κ (Gfull μ)
      hc0 := fun z hz => (continuousAt_const.mul (hGc z hz.1)).continuousWithinAt
      hD := fun z hz => ((hAc z hz.1).sub ((hec z).div (hAc z hz.1) (Complex.exp_ne_zero _))).continuousWithinAt
      hs := fun z hz => ((hAc z hz.1).add ((hec z).div (hAc z hz.1) (Complex.exp_ne_zero _))).continuousWithinAt
      hA := fun z hz => (hAc z hz.1).continuousWithinAt
      bg := fun z hz _ => ⟨hη, by positivity, by positivity, (hP z hz).2.2.2.2.2.1,
        norm_sf_le (hP z hz).2.2.2.2.2.2.1 (hP z hz).2.2.2.2.2.2.2.1 (hP z hz).2.2.2.2.2.2.2.2.1, hAlow z hz,
        A_eq_half L κ _ z⟩
      c0le := fun z hz _ => by
        rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hκ.le]
        exact mul_le_mul_of_nonneg_left (hGle z hz) hκ.le
      s_le := fun z hz =>
        norm_sf_le (hP z hz).2.2.2.2.2.2.1 (hP z hz).2.2.2.2.2.2.2.1 (hP z hz).2.2.2.2.2.2.2.2.1 }
  refine ⟨B, rfl, rfl, rfl, rfl, fun t p => ?_⟩
  -- apply the PROP-026 actual-contour statement on `Γ_N`
  set δN : ℝ := ((k + q : ℕ) : ℝ) ^ (-γ) + 1 / (((k + q : ℕ) : ℝ) ^ θ) ^ b + 1 / ((k + q : ℕ) : ℝ) with hδNdef
  have hδN0 : 0 ≤ δN := by
    have : 0 < ((k + q : ℕ) : ℝ) ^ θ := Real.rpow_pos_of_pos hNr θ
    have : 0 < ((k + q : ℕ) : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hNr _
    rw [hδNdef]; positivity
  have hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1,
      (rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ ∈ NbhdN a h (ρ / 8) := fun i τ hτ =>
    ⟨_, rect_mem (by linarith) hh.le _ _ i hτ, by rw [sub_self, norm_zero]; positivity⟩
  have hmain := hCb q hN (NbhdN a h (ρ / 8)) (rectPieces a h (pw d t p) (continuous_pw d t p)) hZ
    (fun i τ hτ => (gammaN_abs (by linarith) hh.le (rect_mem (by linarith) hh.le _ _ i hτ)).2)
    (fun i τ hτ => rect_im_ne hh _ _ i hτ) B φ hφ (fun _ => max Kd 0 * δN)
    (fun _ => mul_nonneg (le_max_right _ _) hδN0)
    (fun i τ hτ => by
      have := hdevN hN φ hsupp _ (hZ i τ hτ)
      rw [hφ, mul_one] at this
      exact this)
  refine hmain.trans (ENNReal.ofReal_le_ofReal ?_)
  have hw := rect_wlen_le (by linarith : (0 : ℝ) ≤ a) hh.le d t p
  rw [← Finset.mul_sum]
  have hk0 : 0 ≤ C * (2 * Real.pi * κ)⁻¹ * max Kd 0 := by positivity
  calc C * ((2 * Real.pi * κ)⁻¹ * (max Kd 0 * δN * ∑ i : Fin 6, ∫ τ : unitInterval,
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).ω
          ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ)‖ *
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).γ' τ‖))
      = C * (2 * Real.pi * κ)⁻¹ * max Kd 0 * δN * ∑ i : Fin 6, ∫ τ : unitInterval,
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).ω
          ((rectPieces a h (pw d t p) (continuous_pw d t p) i).γ τ)‖ *
        ‖(rectPieces a h (pw d t p) (continuous_pw d t p) i).γ' τ‖ := by ring
    _ ≤ C * (2 * Real.pi * κ)⁻¹ * max Kd 0 * δN *
        (12 * (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) * ((1 + a) * (1 + h)) ^ (d + 1)) :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg hk0 hδN0)
    _ = C * (2 * Real.pi * κ)⁻¹ * max Kd 0 * (12 * (1 + h) ^ (d + 1)) *
        (|t| * ∑ r ∈ Finset.range (d + 1), |p r|) * (1 + a) ^ (d + 1) * δN := by
        rw [mul_pow]; ring

/-! ## 2. The chart agreement -/

/-- sonnet_fourier's bounded smooth extension `f_z = gfun r (iκG(z), D(z), s(z), A(z))` (`MPChartSmooth.gfun`), as a function
of `(z, w)`. -/
def fz (L κ : ℝ) (G : ℂ → ℂ) (rr : ℝ) (z w : ℂ) : ℂ :=
  gfun rr (Complex.I * κ * G z) (Df L κ G z) (sf L κ G z) (Af κ G z) w

/-- **Chart agreement**: within `r/2` of `s(z)`, `f_z(w) = λ(z,w)` (`Prop018Phase.lam`). -/
theorem fz_eq_lam {L κ : ℝ} {G : ℂ → ℂ} {rr : ℝ} (hrr : 0 < rr) {z w : ℂ} (hw : ‖w - sf L κ G z‖ ≤ rr / 2) :
    fz L κ G rr z w = lam L κ G z w := by
  unfold fz gfun
  rw [cutoff_eq_one hrr hw, Complex.ofReal_one, one_mul]
  unfold chartLambda chartA chartD lam ach dch
  rw [one_div]

open Classical in
/-- `g_θ` of the background family with the pinned fields `c₀ = iκG`, `D`, `s`, `A` is `f_{z_θ}` at good parameters. -/
theorem gθ_eq_pt {m : ℕ} {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁) {G : ℂ → ℂ}
    (hc0 : B.c0 = fun z => Complex.I * κ * G z) (hD : B.D = Df L κ G) (hs : B.s = sf L κ G) (hA : B.A = Af κ G)
    (θ' : ThetaSpace m) (w : ℂ) :
    gθ P B θ' w = if good P θ' then fz L κ G (rad d₀ s₁ a₀) (zθ P θ') w else 0 := by
  unfold gθ
  split_ifs with hg
  · unfold fz
    rw [hc0, hD, hs, hA]
  · rfl

open Classical in
theorem dθ_eq {m : ℕ} {Z : Set ℂ} {d₀ s₁ a₀ c₁ : ℝ} (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁) {G : ℂ → ℂ}
    (hD : B.D = Df L κ G) :
    dθ P B = fun θ' => if good P θ' then (Df L κ G (zθ P θ'))⁻¹ else 0 := by
  funext θ'
  unfold dθ
  rw [hD]

/-! ## 3. Real-axis parameters have measure zero -/

theorem vol01 : (volume : Measure unitInterval) {τ | (τ : ℝ) = 0 ∨ (τ : ℝ) = 1} = 0 := by
  have hE : MeasurableEmbedding (Subtype.val : unitInterval → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  have hv : (volume : Measure unitInterval) = Measure.comap Subtype.val volume := by
    rfl
  rw [hv, hE.comap_apply]
  refine measure_mono_null ?_ ((Set.toFinite ({0, 1} : Set ℝ)).measure_zero volume)
  rintro x ⟨τ, hτ, rfl⟩
  rcases hτ with h0 | h1
  · exact Or.inl h0
  · exact Or.inr h1

/-- **The real-axis parameters of the window contour have measure zero**: `ν`-a.e. `θ` is good. -/
theorem ae_good {a h : ℝ} (hh : 0 < h) (ω : ℂ → ℂ) (hω : Continuous ω) :
    ∀ᵐ θ' ∂(nu 6), good (rectPieces a h ω hω) θ' := by
  rw [ae_iff]
  refine measure_mono_null
    (t := (Set.univ : Set (Fin 6)) ×ˢ {τ : unitInterval | (τ : ℝ) = 0 ∨ (τ : ℝ) = 1}) ?_ ?_
  · intro θ' hθ'
    refine Set.mem_prod.2 ⟨Set.mem_univ _, ?_⟩
    show ((θ'.2 : ℝ) = 0 ∨ (θ'.2 : ℝ) = 1)
    by_contra hne
    rw [not_or] at hne
    exact absurd (rect_im_ne (a := a) hh ω hω θ'.1
      ⟨lt_of_le_of_ne θ'.2.2.1 (Ne.symm hne.1), lt_of_le_of_ne θ'.2.2.2 hne.2⟩) hθ'
  · unfold nu
    rw [Measure.prod_prod, vol01, mul_zero]

/-! ## 4. The window contour does not depend on its weight -/

theorem rect_γ_indep (a h : ℝ) (ω ω' : ℂ → ℂ) (hω : Continuous ω) (hω' : Continuous ω') (i : Fin 6) :
    (rectPieces a h ω hω i).γ = (rectPieces a h ω' hω' i).γ := by
  fin_cases i <;> rfl

theorem rect_γ'_indep (a h : ℝ) (ω ω' : ℂ → ℂ) (hω : Continuous ω) (hω' : Continuous ω') (i : Fin 6) :
    (rectPieces a h ω hω i).γ' = (rectPieces a h ω' hω' i).γ' := by
  fin_cases i <;> rfl

theorem zθ_rect (a h : ℝ) (ω ω' : ℂ → ℂ) (hω : Continuous ω) (hω' : Continuous ω') (θ' : ThetaSpace 6) :
    zθ (rectPieces a h ω hω) θ' = zθ (rectPieces a h ω' hω') θ' := by
  unfold zθ
  rw [rect_γ_indep a h ω ω' hω hω']

theorem uθ_rect (κ a h : ℝ) (ω : ℂ → ℂ) (hω : Continuous ω) (θ' : ThetaSpace 6) :
    uθ κ (rectPieces a h ω hω) θ' =
      ω (zθ (rectPieces a h (fun _ => (1 : ℂ)) continuous_const) θ') *
        uθ κ (rectPieces a h (fun _ => (1 : ℂ)) continuous_const) θ' := by
  unfold uθ
  rw [rect_ω, rect_ω, zθ_rect a h ω (fun _ => (1 : ℂ)) hω continuous_const θ',
    rect_γ'_indep a h ω (fun _ => (1 : ℂ)) hω continuous_const]
  ring

theorem rect_nbhd {a h ρ' : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hρ' : 0 ≤ ρ') (ω : ℂ → ℂ) (hω : Continuous ω) :
    ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (rectPieces a h ω hω i).γ τ ∈ NbhdN a h ρ' := fun i _ hτ =>
  ⟨_, rect_mem ha hh ω hω i hτ, by rw [sub_self, norm_zero]; exact hρ'⟩

theorem rect_im_le {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (ω : ℂ → ℂ) (hω : Continuous ω) :
    ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, |((rectPieces a h ω hω i).γ τ).im| ≤ h := fun i _ hτ =>
  (gammaN_abs ha hh (rect_mem ha hh ω hω i hτ)).2

/-! ## 5. The linear-transfer operator `L_{N,p}` and its linearity in `p` -/

/-- **`L_{N,p} = −(2πκ)^{−1} Re ∮_{Γ_N} p(z) S_N(z) D(z)^{−1} dz`** (`Q7A:eq:linear`), with the weight `p = ω`, along the
window contour `Γ_N = rectPieces a_N h ω` (`MPOps.Lop`, `u_θ = −(2πκ)^{−1} ω(z_θ) γ'`, `d_θ = D(z_θ)^{−1}`). -/
def Lwin (L : ℝ) [Fact (0 < L)] (κ : ℝ) (μ : Measure ℝ) (θ h : ℝ) (N : ℕ) (ω : ℂ → ℂ) (hω : Continuous ω) :
    SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  Lop (nu 6) (fun θ' => normalizedTransfer L κ N (zθ (rectPieces (cutN L θ N) h ω hω) θ'))
    (uθ κ (rectPieces (cutN L θ N) h ω hω))
    (fun θ' => (Df L κ (Gfull μ) (zθ (rectPieces (cutN L θ N) h ω hω) θ'))⁻¹)

theorem Lwin_congr {μ : Measure ℝ} {θ h : ℝ} {N : ℕ} {ω ω' : ℂ → ℂ} (hω : Continuous ω) (hω' : Continuous ω')
    (he : ω = ω') : Lwin L κ μ θ h N ω hω = Lwin L κ μ θ h N ω' hω' := by
  subst he; rfl

theorem Lwin_eq (μ : Measure ℝ) (θ h : ℝ) (N : ℕ) (ω : ℂ → ℂ) (hω : Continuous ω) :
    Lwin L κ μ θ h N ω hω = reOp (∫ θ', (ω (zθ (rectPieces (cutN L θ N) h (fun _ => (1 : ℂ)) continuous_const) θ') *
      (uθ κ (rectPieces (cutN L θ N) h (fun _ => (1 : ℂ)) continuous_const) θ' *
        (Df L κ (Gfull μ) (zθ (rectPieces (cutN L θ N) h (fun _ => (1 : ℂ)) continuous_const) θ'))⁻¹)) •
      normalizedTransfer L κ N (zθ (rectPieces (cutN L θ N) h (fun _ => (1 : ℂ)) continuous_const) θ') ∂(nu 6)) := by
  unfold Lwin Lop
  refine congrArg reOp (integral_congr_ae (Filter.Eventually.of_forall fun θ' => ?_))
  beta_reduce
  rw [uθ_rect, zθ_rect (cutN L θ N) h ω (fun _ => (1 : ℂ)) hω continuous_const θ', mul_assoc]

open Classical in
theorem Lwin_eq_Lop {μ : Measure ℝ} {θ h : ℝ} (hh : 0 < h) (N : ℕ) (ω : ℂ → ℂ) (hω : Continuous ω) :
    Lwin L κ μ θ h N ω hω = Lop (nu 6) (fun θ' => normalizedTransfer L κ N (zθ (rectPieces (cutN L θ N) h ω hω) θ'))
      (uθ κ (rectPieces (cutN L θ N) h ω hω))
      (fun θ' => if good (rectPieces (cutN L θ N) h ω hω) θ' then
        (Df L κ (Gfull μ) (zθ (rectPieces (cutN L θ N) h ω hω) θ'))⁻¹ else 0) := by
  unfold Lwin Lop
  refine congrArg reOp (integral_congr_ae ?_)
  filter_upwards [ae_good hh ω hω (a := cutN L θ N)] with θ' hg
  simp only [hg, ↓reduceIte]

section Generic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem reOp_sum (s : Finset ℕ) (t : ℕ → ℝ) (X : ℕ → H →L[ℂ] H) :
    reOp (∑ r ∈ s, ((t r : ℝ) : ℂ) • X r) = ∑ r ∈ s, ((t r : ℝ) : ℂ) • reOp (X r) := by
  unfold reOp
  rw [map_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_smulₛₗ, Complex.conj_ofReal, ← smul_add, smul_comm]

theorem isSA_reOp (A : H →L[ℂ] H) : IsSelfAdjoint (reOp A) := by
  rw [isSelfAdjoint_iff, ContinuousLinearMap.star_eq_adjoint]
  unfold reOp
  rw [map_smulₛₗ, map_add, ContinuousLinearMap.adjoint_adjoint, add_comm]
  congr 1
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

theorem isSA_real_smul (r : ℝ) {X : H →L[ℂ] H} (hX : IsSelfAdjoint X) : IsSelfAdjoint ((r : ℂ) • X) :=
  IsSelfAdjoint.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]) hX

theorem lin_generic {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) (s : Finset ℕ) (t : ℕ → ℝ) (z k : Θ → ℂ)
    (S : Θ → H →L[ℂ] H) (hint : ∀ r ∈ s, Integrable (fun θ => (z θ ^ r * k θ) • S θ) ν) :
    ∑ r ∈ s, ((t r : ℝ) : ℂ) • reOp (∫ θ, (z θ ^ r * k θ) • S θ ∂ν) =
      reOp (∫ θ, ((∑ r ∈ s, ((t r : ℝ) : ℂ) * z θ ^ r) * k θ) • S θ ∂ν) := by
  rw [← reOp_sum]
  congr 1
  have e : (fun θ => ((∑ r ∈ s, ((t r : ℝ) : ℂ) * z θ ^ r) * k θ) • S θ) =
      fun θ => ∑ r ∈ s, ((t r : ℝ) : ℂ) • ((z θ ^ r * k θ) • S θ) := by
    funext θ
    rw [Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_smul, mul_assoc]
  rw [e, integral_finsetSum s (f := fun r θ => ((t r : ℝ) : ℂ) • ((z θ ^ r * k θ) • S θ))
    (fun r hr => (hint r hr).smul (((t r : ℝ) : ℂ)))]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_smul]

theorem int_cont {S : ThetaSpace 6 → H →L[ℂ] H} (hS : Continuous S) {c : ThetaSpace 6 → ℂ} (hc : Continuous c) :
    Integrable (fun θ => c θ • S θ) (nu 6) :=
  (hc.smul hS).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem lin_cont (s : Finset ℕ) (t : ℕ → ℝ) {z k : ThetaSpace 6 → ℂ} (hz : Continuous z) (hk : Continuous k)
    {S : ThetaSpace 6 → H →L[ℂ] H} (hS : Continuous S) :
    ∑ r ∈ s, ((t r : ℝ) : ℂ) • reOp (∫ θ, (z θ ^ r * k θ) • S θ ∂(nu 6)) =
      reOp (∫ θ, ((∑ r ∈ s, ((t r : ℝ) : ℂ) * z θ ^ r) * k θ) • S θ ∂(nu 6)) :=
  lin_generic (nu 6) s t z k S (fun r _ => int_cont hS ((hz.pow r).mul hk))

end Generic

/-- **Linearity of `L_{N,p}` in the weight**: `Σ_r t_r L_{N,x^r} = L_{N,Σ_r t_r x^r}`, given continuity of `D(z)^{−1}` along
`Γ_N`. -/
theorem Lwin_lin {μ : Measure ℝ} {θ h : ℝ} (N : ℕ) (ords : Finset ℕ) (t : ℕ → ℝ)
    (hd : Continuous fun θ' =>
      (Df L κ (Gfull μ) (zθ (rectPieces (cutN L θ N) h (fun _ => (1 : ℂ)) continuous_const) θ'))⁻¹) :
    ∑ r ∈ ords, ((t r : ℝ) : ℂ) • Lwin L κ μ θ h N (fun z => z ^ r) (continuous_pow r) =
      Lwin L κ μ θ h N (fun z => ∑ r ∈ ords, ((t r : ℝ) : ℂ) * z ^ r)
        (continuous_finsetSum _ fun r _ => continuous_const.mul (continuous_pow r)) := by
  have hS : Continuous fun θ' => normalizedTransfer L κ N
      (zθ (rectPieces (cutN L θ N) h (fun _ => (1 : ℂ)) continuous_const) θ') :=
    ((QuantumNLS.NormalityBridge.differentiable_normalizedTransfer (L := L) (κ := κ) (N := N)).continuous).comp
      (continuous_zθ _)
  simp only [Lwin_eq]
  exact lin_cont ords t (continuous_zθ _) ((continuous_uθ κ _).mul hd) hS

/-! ## 6. Integrability of the `C₀` operator family (copied from the `mp_linearization` / `C0N_eq_C0op` proofs) -/

section IntCfc

open QuantumNLS.MPChartBounds QuantumNLS.MPChartDeriv QuantumNLS.MPFamily QuantumNLS.MPFamilyMeas QuantumNLS.MPOps
  QuantumNLS.MixedQuadratures QuantumNLS.FunctionalLinearization QuantumNLS.MPLinearization

/-- The integrability step of `MPOps.C0N_eq_C0op` (its proof, verbatim), generic Hilbert space. -/
theorem int_cfc_gen {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Θ : Type*} [MeasurableSpace Θ] (ν : Measure Θ) [IsFiniteMeasure ν] (R : ℝ) (S : Θ → H →L[ℂ] H)
    (hS : ∀ θ, IsStarNormal (S θ)) (hR : ∀ θ, ‖S θ‖ ≤ R) (u : Θ → ℂ) (g : Θ → ℂ → ℂ) (hg : ∀ θ, Continuous (g θ))
    (hB : ∀ j, AEStronglyMeasurable
      (fun θ => quadHom (S θ) (hS θ) R (hR θ) (coordC (d := 2) (K := Kdisc R) j)) ν)
    (hF1 : AEStronglyMeasurable (fun θ => resKd (Kdisc R) (quadF (u θ) (g θ))) ν)
    (hF2 : AEStronglyMeasurable (fun θ => resKd (Kdisc R) (quadF ((-Complex.I) * u θ) (g θ))) ν)
    {C : ℝ} (hC1 : ∀ θ, ‖resKd (Kdisc R) (quadF (u θ) (g θ))‖ ≤ C)
    (hC2 : ∀ θ, ‖resKd (Kdisc R) (quadF ((-Complex.I) * u θ) (g θ))‖ ≤ C) :
    Integrable (fun θ => u θ • cfc (g θ) (S θ)) ν := by
  have i1 := integrable_apply_comp ν (fun θ => quadHom (S θ) (hS θ) R (hR θ)) hB _ hF1 hC1
  have i2 := integrable_apply_comp ν (fun θ => quadHom (S θ) (hS θ) R (hR θ)) hB _ hF2 hC2
  refine (Integrable.add i1 (Integrable.smul Complex.I i2)).congr (Eventually.of_forall fun θ => ?_)
  have e1 : quadHom (S θ) (hS θ) R (hR θ) (resKd (Kdisc R) (quadF (u θ) (g θ))) =
      reOp (u θ • cfc (g θ) (S θ)) := quadHom_quadF _ _ _ _ (u θ) (hg θ)
  have e2 : quadHom (S θ) (hS θ) R (hR θ) (resKd (Kdisc R) (quadF ((-Complex.I) * u θ) (g θ))) =
      reOp (((-Complex.I) * u θ) • cfc (g θ) (S θ)) := quadHom_quadF _ _ _ _ ((-Complex.I) * u θ) (hg θ)
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [e1, e2, ← smul_smul]
  exact (eq_reOp_add (u θ • cfc (g θ) (S θ))).symm

/-- **`C₀` on an actual transfer eigenvector**: `C0op` of the window family acts on a joint eigenvector `v` of all
`S_N(z_θ)` (eigenvalues `λ_θ`) by `∫ Re(u_θ g_θ(λ_θ)) dν`. The operator-family integrability is the `mp_linearization` /
`C0N_eq_C0op` argument (copied). -/
theorem C0_eig (L : ℝ) [Fact (0 < L)] {κ : ℝ} (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) {m : ℕ} {Z : Set ℂ}
    {d₀ s₁ a₀ c₁ h : ℝ} (hc1 : 0 ≤ c₁) (P : Fin m → Piece) (B : BgFam Z d₀ s₁ a₀ c₁)
    (hZ : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (P i).γ τ ∈ Z) (hIm : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, |((P i).γ τ).im| ≤ h)
    {v : SymSector ℂ (L2T L) N} (hv0 : v ≠ 0) (lam : ThetaSpace m → ℂ)
    (hv : ∀ θ, normalizedTransfer L κ N (zθ P θ) v = lam θ • v) :
    C0op (nu m) (fun θ => normalizedTransfer L κ N (zθ P θ)) (uθ κ P) (gθ P B) v =
      (((∫ θ, (uθ κ P θ * gθ P B θ (lam θ)).re ∂(nu m) : ℝ)) : ℂ) • v := by
  classical
  have hz : Continuous (zθ P) := continuous_zθ P
  have hzh : ∀ θ : ThetaSpace m, |(zθ P θ).im| ≤ h := fun θ => hIm θ.1 θ.2 θ.2.2
  have hS : ∀ θ : ThetaSpace m, IsStarNormal (normalizedTransfer L κ N (zθ P θ)) :=
    fun θ => SN_isStarNormal L κ hκ N hN (zθ P θ)
  have hR : ∀ θ : ThetaSpace m, ‖normalizedTransfer L κ N (zθ P θ)‖ ≤ Rbd L κ h :=
    fun θ => norm_normalizedTransfer_le L κ N (zθ P θ) h (hzh θ)
  obtain ⟨U₁, hU₁⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_uθ κ P).continuousOn
  set U₀ : ℝ := max U₁ 0 with hU₀def
  have hU₀' : ∀ θ, ‖uθ κ P θ‖ ≤ U₀ := fun θ => (hU₁ θ (mem_univ _)).trans (le_max_left _ _)
  have hgc : ∀ θ, Continuous (gθ P B θ) := fun θ => (contDiff_gθ P B hZ θ).continuous
  have hgb : ∀ θ w, ‖gθ P B θ w‖ ≤ c₁ + 1 := norm_gθ_le P B hZ hc1
  have hBm : ∀ j, AEStronglyMeasurable (fun θ => quadHom (normalizedTransfer L κ N (zθ P θ)) (hS θ)
      (Rbd L κ h) (hR θ) (coordC (d := 2) (K := Kdisc (Rbd L κ h)) j)) (nu m) :=
    fun j => PhiFam_hB hκ hN (nu m) (zθ P) hz (Rbd L κ h) hR j
  have hF1 : AEStronglyMeasurable
      (fun θ => resKd (Kdisc (Rbd L κ h)) (quadF (uθ κ P θ) (gθ P B θ))) (nu m) :=
    aesm_resKd κ P B hZ (Rbd L κ h)
  have hF2 : AEStronglyMeasurable
      (fun θ => resKd (Kdisc (Rbd L κ h)) (quadF ((-Complex.I) * uθ κ P θ) (gθ P B θ))) (nu m) := by
    have := aesm_resKd κ (twist P) B (fun i τ hτ => hZ i τ hτ) (Rbd L κ h)
    have e : (fun θ => resKd (Kdisc (Rbd L κ h)) (quadF ((-Complex.I) * uθ κ P θ) (gθ P B θ))) =
        fun θ => resKd (Kdisc (Rbd L κ h)) (Fθ κ (twist P) B θ) := by
      funext θ; unfold Fθ; rw [uθ_twist, gθ_twist]
    rw [e]; exact this
  have hC1' : ∀ θ, ‖resKd (Kdisc (Rbd L κ h)) (quadF (uθ κ P θ) (gθ P B θ))‖ ≤ U₀ * (c₁ + 1) := fun θ =>
    (norm_resKd_Fθ_le hc1 (uθ κ P θ) (Rbd L κ h) (gθ P B θ) (hgc θ) (hgb θ)).trans
      (mul_le_mul_of_nonneg_right (hU₀' θ) (by linarith))
  have hC2' : ∀ θ, ‖resKd (Kdisc (Rbd L κ h)) (quadF ((-Complex.I) * uθ κ P θ) (gθ P B θ))‖ ≤ U₀ * (c₁ + 1) :=
    fun θ => (norm_resKd_Fθ_le hc1 ((-Complex.I) * uθ κ P θ) (Rbd L κ h) (gθ P B θ) (hgc θ) (hgb θ)).trans
      (by rw [norm_mul, norm_neg, Complex.norm_I, one_mul]; exact mul_le_mul_of_nonneg_right (hU₀' θ) (by linarith))
  exact QuantumNLS.Prop020Diag.C0op_eigen (nu m) _ hS _ _ hgc
    (int_cfc_gen (nu m) (Rbd L κ h) _ hS hR _ _ hgc hBm hF1 hF2 hC1' hC2') hv0 lam hv

end IntCfc

/-! ## 7. Identification of the `C₀` eigenvalue with `Prop018Phase.C0ev` on `𝓔_N` -/

theorem pw_one (d : ℕ) (p : ℕ → ℝ) : pw d 1 p = poly p d := by
  funext z
  unfold pw poly
  simp only [one_mul]

open Classical in
/-- **`C0_identify`**: eventually in `N`, for every polynomial `p` and every label `m ∈ 𝓔_N`, the eigenvalue
`∫ Re(u_θ f_{z_θ}(λ_θ)) dν` of `C0op` on `Ψ_{N,m}` (`Prop020Diag.C0op_eigen`, `λ_θ` the actual transfer eigenvalue) equals
`Prop018Phase.C0ev` with `f = fz` (`eigen_eq_sNf`, `ae_good`, `theta_integral_rect`, `pw d 1 p = poly p d`). -/
theorem C0_identify (hκ : 0 < κ) (μ : Measure ℝ) {h ρ C M η r K Kd θ γ : ℝ} {b : ℕ} (hh : 0 < h)
    (hρ0 : 0 < ρ) (hM1 : 1 ≤ M) (hη : 0 < η) (hθ : 0 < θ) (hγ : 0 < γ) (hb : 1 ≤ b)
    (E : (N : ℕ) → Set (MArr N))
    (hev : ∀ᶠ N : ℕ in atTop, ∀ m ∈ E N, ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8),
          ((∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖) ∧
          ‖Wf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ 1 / 2 ∧
          1 / (2 * M) ≤ ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          3 * η / 4 ≤ ‖DNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ∧
          ‖aNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z - Af κ (Gfull μ) z‖ ≤ 1 / (2 * M) ∧
          ‖ellf (κ / N) (qAct L κ N m) z - logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) z +
              Complex.I * κ / (N : ℂ) * corrf L κ (κ / N) (Gfull μ) (qAct L κ N m) z‖ ≤ C / (N : ℝ) ^ 2) ∧
          (∀ j, |qAct L κ N m j| ≤ (N : ℝ) ^ θ) ∧
          ‖Gfull μ z - GN (qAct L κ N m) z‖ ≤ K * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b) ∧
          (∀ j, r ≤ ‖z - (qAct L κ N m j : ℂ)‖) ∧
          DifferentiableAt ℂ (Gfull μ) z ∧
          η ≤ ‖Df L κ (Gfull μ) z‖ ∧
          ‖Af κ (Gfull μ) z‖ ≤ M ∧ ‖(Af κ (Gfull μ) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧
          ∀ n : ℕ, ‖iteratedDeriv n (fun w => sNsrc κ L (qAct L κ N m) w - sLimsrc κ L μ w) z‖ ≤
            n.factorial * (Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ n)
    (d : ℕ) (rr : ℝ) (hrr : 0 < rr) :
    ∀ᶠ N : ℕ in atTop, ∀ (hN : 1 ≤ N) (p : ℕ → ℝ), ∀ m ∈ E N,
      ∫ θ', (uθ κ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ' *
        (if good (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ' then
            fz L κ (Gfull μ) rr (zθ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ')
              (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m
                (zθ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ'))
          else 0)).re ∂(nu 6) =
        C0ev L κ (fz L κ (Gfull μ) rr) θ h p d N m := by
  have hL : 0 < L := Fact.out
  have hδN : Tendsto (fun N : ℕ => Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-γ)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hγ).comp tendsto_natCast_atTop_atTop
    have hR' : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
      (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => 1 / ((N : ℝ) ^ θ) ^ b) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega)).comp hR')
    have h3 : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa using ((h1.add h2).add h3).const_mul Kd
  filter_upwards [hev, hδN.eventually (gt_mem_nhds (half_pos hrr)), regime_eventually hL hθ hγ 1 0,
    eventually_ge_atTop 1] with N hevN hsmN hreg hN1
  intro hN p m hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha2 : 2 ≤ cutN L θ N := by linarith [hreg.1, hreg.2.2.1]
  have hρ8 : 0 < ρ / 8 := by positivity
  have hzN : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, z ∈ NbhdN (cutN L θ N) h (ρ / 8) := fun z hz =>
    gam_sub_nbhd hz (by rw [sub_self, norm_zero]; exact hρ8.le)
  have hball : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, ∀ᶠ w in 𝓝 z, w ∈ NbhdN (cutN L θ N) h (ρ / 8) :=
    fun z hz => by
      filter_upwards [Metric.ball_mem_nhds z hρ8] with w hw
      exact gam_sub_nbhd hz (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw.le)
  have hsN : ∀ w ∈ NbhdN (cutN L θ N) h (ρ / 8),
      ‖sNf L (κ / N) (qAct L κ N m) w - sf L κ (Gfull μ) w‖ ≤ rr / 2 := fun w hw => by
    have h0 := (hevN m hm w hw).2.2.2.2.2.2.2.2.2 0
    rw [sNsrc_eq, sLimsrc_eq] at h0
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul] at h0
    exact h0.trans hsmN.le
  obtain ⟨F, hF⟩ : ∃ F : ℂ → ℂ, F = fun z => fz L κ (Gfull μ) rr z (sNf L (κ / N) (qAct L κ N m) z) := ⟨_, rfl⟩
  have hFl : ∀ w ∈ NbhdN (cutN L θ N) h (ρ / 8), F w = logaNf L κ (κ / N) (Gfull μ) (qAct L κ N m) w :=
    fun w hw => by
      rw [hF]
      exact (fz_eq_lam hrr (hsN w hw)).trans (logaNf_eq_lam L κ (κ / N) (Gfull μ) (qAct L κ N m) w).symm
  have hFc : ∀ z ∈ Gam (-(cutN L θ N)) (cutN L θ N) h, ContinuousAt F z := fun z hz => by
    have hP := hevN m hm z (hzN z hz)
    have hGnear : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ (Gfull μ) w := by
      filter_upwards [hball z hz] with w hw
      exact (hevN m hm w hw).2.2.2.2.1
    have hDz : Df L κ (Gfull μ) z ≠ 0 := fun h0 => by
      have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
    have hc := contAt_gen (by linarith : (0 : ℝ) < M) hη hGnear hP.1.1 hDz hP.1.2.1 hP.1.2.2.1 hP.1.2.2.2.1
      hP.1.2.2.2.2.1 hP.2.2.2.2.2.2.2.1
    refine hc.1.congr ?_
    filter_upwards [hball z hz] with w hw
    exact (hFl w hw).symm
  have hmem : ∀ θ' : ThetaSpace 6, zθ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ' ∈
      Gam (-(cutN L θ N)) (cutN L θ N) h := fun θ' =>
    rect_mem_Gam (by linarith) hh.le _ _ θ'.1 ⟨θ'.2.2.1, θ'.2.2.2⟩
  have hne : ∀ θ' : ThetaSpace 6, ∀ j,
      zθ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ' ≠ (qAct L κ N m j : ℂ) := by
    intro θ' j h0
    have h1 := (hevN m hm _ (hzN _ (hmem θ'))).1.1 j
    rw [h0, sub_self, norm_zero] at h1
    have : 0 ≤ 2 * |κ / (N : ℝ)| := by positivity
    linarith
  have hint : Integrable (fun θ' => uθ κ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ' *
      F (zθ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ')) (nu 6) := by
    have hcont : Continuous fun θ' : ThetaSpace 6 =>
        uθ κ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ' *
          F (zθ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ') :=
      (continuous_uθ κ _).mul (continuous_iff_continuousAt.2 fun θ' =>
        (hFc _ (hmem θ')).comp (continuous_zθ _).continuousAt)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpw : (fun z => pw d 1 p z * F z) =
      fun z => poly p d z * fz L κ (Gfull μ) rr z (sNf L (κ / N) (qAct L κ N m) z) := by
    funext z; rw [pw_one, hF]
  calc _ = ∫ θ', (uθ κ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ' *
        F (zθ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ')).re ∂(nu 6) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_good hh (pw d 1 p) (continuous_pw d 1 p) (a := cutN L θ N)] with θ' hg
        simp only [hg, ↓reduceIte]
        rw [eigen_eq_sNf hκ hN m _ (hne θ'), hF]
    _ = (∫ θ', uθ κ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ' *
        F (zθ (rectPieces (cutN L θ N) h (pw d 1 p) (continuous_pw d 1 p)) θ') ∂(nu 6)).re := by
        have := Complex.reCLM.integral_comp_comm hint
        simpa only [Complex.reCLM_apply] using this
    _ = C0ev L κ (fz L κ (Gfull μ) rr) θ h p d N m := by
        rw [theta_integral_rect (by linarith) hh κ (pw d 1 p) (continuous_pw d 1 p) F hFc, hpw]
        unfold C0ev
        rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul, one_div]
        ring

end QuantumNLS.Prop020Link

#print axioms QuantumNLS.Prop020Link.linearization_of_bundle
#print axioms QuantumNLS.Prop020Link.fz_eq_lam
#print axioms QuantumNLS.Prop020Link.ae_good
#print axioms QuantumNLS.Prop020Link.Lwin_lin
#print axioms QuantumNLS.Prop020Link.Lwin_eq_Lop
#print axioms QuantumNLS.Prop020Link.int_cfc_gen
#print axioms QuantumNLS.Prop020Link.C0_eig
#print axioms QuantumNLS.Prop020Link.C0_identify
