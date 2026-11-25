import QuantumNLS.Prop020Explicit
import QuantumNLS.Prop025OEigen
import QuantumNLS.Prop025OCorr
import QuantumNLS.Prop025OFinal
import QuantumNLS.MPLinearizationContours

/-! PROP-025 (thm:MP-mixed, mixed_propagation.tex sha256 24ab083b...), stage O3f:
the joint quantum-to-quantum comparison eq:MP-quantum-comparison (mixed_propagation.tex:300-420).

Source chain: one common projection `P_N = P^I_N P^g_N` (eq:MP-common-projection), the summed eigenvalue inequalities
eq:MP-reconstruction and eq:MP-correction-scalar, the phase comparison eq:MP-phase-comparison, PROP-026
(lem:MP-linearization) and the trace-norm chain:
`‖γ^{(k)}_{U_N(t)V_N(θ)u^{⊗N}} − γ^{(k)}_{e^{−iNL_N(t,θ)}u^{⊗N}}‖₁ ≤ C(√(η^I + η^g) + W_a/N + W_aΔ_N + ρ^I)`.

Lean objects:
* `U_N(t)V_N(θ) = e^{−iH_N(t,θ)}` is the joint spectral unitary on the actual Bethe basis with eigenvalue
  `mixedEv = Σ_r t_r Q_{N,r}(m) + Σ_i θ_i m_{n_i}` (`Q_{N,r}` = `BetheSpectralCharges.eigenvalue`, `m_n` = the occupation of the
  Bethe label, the corrected count eigenvalue of the frozen O3c `count_event`);
* `L_N(t,θ)` (eq:MP-L) is `LmixOp`: `MPOps.Lop` over the PROP-026 family `Fin.append (rectPieces a h p_t) (rectFamily …)` with
  the weights `u_θ = −(2πκ)⁻¹ ω(z_θ) γ'` and `D(z_θ)⁻¹`, `D = Df L κ (Gfull μ)` frozen at the profile;
* `Γ_a`: the window rectangle at the designated cut `a = cutN L α N`, `α = 1/(56(d+1))` (eq:MP-parameters), `R = N^α`,
  `ε = N^{-1/8}`, `b = d+2`, `p = 28(d+1)+1`; `Γ_{n_i}`: `∂([b_{n_i−1}, b_{n_i}]×[−h,h])` at the physical separators;
* `η^g_N = Prop025OFinal.etaG` (eq:MP-growing-mass, explicit), `W_a`, `Δ_N` as in `Prop025OFinal`; `η^I_N = P(E_derᶜ) + P(E_cntᶜ)`,
  `ρ^I_N` = the O3a fixed-contour deviation; both `0` for empty `I`.

The projection is the event projection of `𝓔_N ∩ E_der ∩ E_cnt` (PROP-017 window event at the bundle radius, O3a, O3c);
PROP-026 is re-derived on that event from `MPLinearizationContours.mp_linearization_contours` with ONE background
`MPFixedContour.bgfamOfG_union` built from the bundle facts and `Prop026Mixed.gam_family_background` (so one packet radius carries
the explicit mass bound, PROP-017/018 bundle, and the PROP-026 deviations).
-/

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop025OPhase

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.PROP018Probability (cutN regime_eventually propBound cut_bounds)
open QuantumNLS.Prop017Quantum (qAct eta0 Gfull_eq)
open QuantumNLS.Prop017Physical (RootSpectralInputs event_projection)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.PeriodReconstruction (Gam)
open QuantumNLS.Prop018Phase (qch C0ev C1ev phase_of_bundle)
open QuantumNLS.Prop018Scalar (cscal scalar_of_bundle Lbd Lbd_nonneg)
open QuantumNLS.Prop018BundleFull (moving_contour_bundle_full)
open QuantumNLS.Prop019Linearization (pw continuous_pw rect_mem)
open QuantumNLS.Prop019Deviation (deviation_of_bundle transfer_deviation)
open QuantumNLS.Prop020Vector (normalize_proj)
open QuantumNLS.Prop020Diag (evol_isometry)
open QuantumNLS.Prop020Link (fz fz_eq_lam gθ_eq_pt dθ_eq C0_identify isSA_reOp isSA_real_smul rect_nbhd rect_im_le)
open QuantumNLS.Prop020Chain (phase_step chain evolution_basis pco pw_pco sum_pco sum_abs_pco)
open QuantumNLS.MPContour (Piece ThetaSpace nu zθ uθ rectPieces polyT continuous_polyT wlen)
open QuantumNLS.MPFamily (BgFam gθ dθ good)
open QuantumNLS.MPChartSmooth (rad)
open QuantumNLS.MPChartBounds (rho_pos)
open QuantumNLS.MPOps (C0op Lop)
open QuantumNLS.FunctionalLinearization (evol)
open QuantumNLS.TensorCarrier (SymSector HilbertTensorPower reducedDensityPower)
open QuantumNLS.TraceClass (traceNorm)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis transfer_physicalBasis)
open QuantumNLS.BetheSpectralCharges (evolution eigenvalue)
open QuantumNLS.HighMomentsOps (wvec)
open QuantumNLS.MPFixedContour (bgfamOfG_union)
open QuantumNLS.MPLinearizationContours (mp_linearization_contours)
open QuantumNLS.Prop009ProbeDev (Gam_im_le exists_pos_le_all gam_supp_dist)
open QuantumNLS.Prop026Mixed (gam_family_background)
open QuantumNLS.Prop026Uniform (rectFamily rectFamily_props)
open QuantumNLS.Prop010ContourBindingR11 (Extension localLog c0 c1)
open QuantumNLS.Prop025OFinal (etaG W Delta)
open QuantumNLS.Prop025OParams (alpha alpha_pos)
open QuantumNLS.RootEvent (prop017Cb)
open QuantumNLS.Prop017Quantum (Ctail Dtail)
open QuantumNLS.RootMeasureConcentrationSharp (Csharp)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### 1. The printed objects -/

/-- The joint eigenvalue of `H_N(t,θ) = Σ_r t_r Q_{N,r} + Σ_i θ_i M_{N,n_i}` on the Bethe vector `Ψ_m`. -/
def mixedEv (L κ : ℝ) (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ} (n : Fin nI → ℤ) (θf : Fin nI → ℝ) (N : ℕ) :
    MArr N → ℝ :=
  fun m => ∑ r ∈ ords, t r * eigenvalue L N (κ / (N : ℝ)) r m + ∑ i, θf i * ((m.1 (n i) : ℕ) : ℝ)

/-- The left fixed-contour abscissae `b_{n_i − 1}` (physical separators). -/
def xmS (hκ : 0 < κ) (u : L2T L) {nI : ℕ} (n : Fin nI → ℤ) : Fin nI → ℝ :=
  fun i => RootScalarPeriodR8.cut hκ u (n i - 1)

/-- The right fixed-contour abscissae `b_{n_i}`. -/
def xpS (hκ : 0 < κ) (u : L2T L) {nI : ℕ} (n : Fin nI → ℤ) : Fin nI → ℝ :=
  fun i => RootScalarPeriodR8.cut hκ u (n i)

/-- The combined PROP-026 piece family: window rectangle with weight `p_t`, then the fixed rectangles with weights `θ_i`. -/
def mixedPieces (hκ : 0 < κ) (u : L2T L) (h a : ℝ) (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ} (n : Fin nI → ℤ)
    (θf : Fin nI → ℝ) : Fin (6 + nI * 6) → Piece :=
  Fin.append (rectPieces a h (polyT ords t) (continuous_polyT ords t))
    (rectFamily (xmS hκ u n) (xpS hκ u n) (fun _ => h) θf)

open Classical in
/-- **`L_N(t,θ)` (eq:MP-L)**: `−(2πκ)⁻¹ Re(∮_{Γ_a} p_t S_N/D dz + Σ_i θ_i ∮_{Γ_{n_i}} S_N/D dz)`, `D` frozen at `u`. -/
def LmixOp (hκ : 0 < κ) (u : L2T L) (μ : Measure ℝ) (h a : ℝ) (ords : Finset ℕ) (t : ℕ → ℝ) {nI : ℕ}
    (n : Fin nI → ℤ) (θf : Fin nI → ℝ) (N : ℕ) : SymSector ℂ (L2T L) N →L[ℂ] SymSector ℂ (L2T L) N :=
  Lop (nu (6 + nI * 6)) (fun θ => normalizedTransfer L κ N (zθ (mixedPieces hκ u h a ords t n θf) θ))
    (uθ κ (mixedPieces hκ u h a ords t n θf))
    (fun θ => if good (mixedPieces hκ u h a ords t n θf) θ then
      (Df L κ (Gfull μ) (zθ (mixedPieces hκ u h a ords t n θf) θ))⁻¹ else 0)

/-! ### 2. Auxiliary facts -/

theorem norm_GN_le_inv {N : ℕ} (q : Fin N → ℝ) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hq : ∀ j, r ≤ ‖z - (q j : ℂ)‖) : ‖GN q z‖ ≤ 1 / r := by
  unfold GN
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp; positivity
  have hN : (0 : ℝ) < N := by exact_mod_cast hpos
  rw [norm_mul]
  have h1 : ‖∑ j, 1 / (z - (q j : ℂ))‖ ≤ ∑ _j : Fin N, 1 / r := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hr (hq j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  have h2 : ‖(1 / (N : ℂ))‖ = 1 / (N : ℝ) := by
    rw [norm_div, norm_one, Complex.norm_natCast]
  rw [h2]
  calc 1 / (N : ℝ) * ‖∑ j, 1 / (z - (q j : ℂ))‖ ≤ 1 / (N : ℝ) * ((N : ℝ) * (1 / r)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / r := by field_simp

theorem rectPieces_congr (a h : ℝ) {ω ω' : ℂ → ℂ} (hω : Continuous ω) (hω' : Continuous ω') (he : ω = ω') :
    rectPieces a h ω hω = rectPieces a h ω' hω' := by
  subst he; rfl

theorem polyT_eq_pw (d : ℕ) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (t : ℕ → ℝ) :
    polyT ords t = pw d 1 (pco ords t) := by
  rw [pw_pco d ords hords t]
  rfl

theorem etaG_mono (d : ℕ) {Cp Dp Cb Cp' Dp' : ℝ} (hCp : Cp ≤ Cp') (hDp : Dp ≤ Dp') {N a : ℝ} (hN : 0 < N) :
    etaG d Cp Dp Cb N a ≤ etaG d Cp' Dp' Cb N a := by
  unfold etaG
  have h1 : 0 ≤ ((N ^ alpha d) ^ (2 * (28 * (d + 1) + 1)))⁻¹ := by
    have := Real.rpow_pos_of_pos hN (alpha d); positivity
  have h2 : 0 ≤ (N ^ alpha d)⁻¹ := by
    have := Real.rpow_pos_of_pos hN (alpha d); positivity
  have h3 : Cp * N * ((N ^ alpha d) ^ (2 * (28 * (d + 1) + 1)))⁻¹ ≤
      Cp' * N * ((N ^ alpha d) ^ (2 * (28 * (d + 1) + 1)))⁻¹ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCp hN.le) h1
  have h4 : Dp * (N ^ alpha d)⁻¹ ≤ Dp' * (N ^ alpha d)⁻¹ := mul_le_mul_of_nonneg_right hDp h2
  linarith

theorem measureReal_compl_inter3_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A B C : Set Ω) : P.real (A ∩ (B ∩ C))ᶜ ≤ P.real Aᶜ + P.real Bᶜ + P.real Cᶜ := by
  rw [Set.compl_inter, Set.compl_inter]
  calc P.real (Aᶜ ∪ (Bᶜ ∪ Cᶜ)) ≤ P.real Aᶜ + P.real (Bᶜ ∪ Cᶜ) := measureReal_union_le _ _
    _ ≤ P.real Aᶜ + (P.real Bᶜ + P.real Cᶜ) := by gcongr; exact measureReal_union_le _ _
    _ = _ := by ring

/-! ### 3. eq:MP-quantum-comparison -/

open Classical in
/-- **eq:MP-quantum-comparison** (with the preparation `Ψ`; the chain adds `2‖Ψ − u^{⊗N}‖`). For the printed parameters,
fixed charge orders `ords ⊆ {0,…,d}`, time box `|t_r| ≤ T_r`, fixed labels `n_i` and angle box `|θ_i| ≤ Θ_i`, there are
`η^I_N, ρ^I_N → 0` (both `0` when no label is tested), packet constants `C_p, D_p, C_b` and ONE constant `C` such that, for
all large `N = k + q`, every normalized `Ψ` and all `t, θ` in the boxes,
`‖γ^{(k)}_{U_N(t)V_N(θ)Ψ} − γ^{(k)}_{e^{−iNL_N(t,θ)}u^{⊗N}}‖₁ ≤ 2‖Ψ − u^{⊗N}‖ + C(√(η^I + η^g) + ρ^I + W_a/N + W_aΔ_N)`. -/
theorem quantum_comparison (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d k : ℕ) (hd : 2 ≤ d) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    {nI : ℕ} (n : Fin nI → ℤ) (Θ : Fin nI → ℝ) (hΘ : ∀ i, 0 ≤ Θ i) :
    ∃ ηI ρI : ℕ → ℝ, (∀ N, 0 ≤ ηI N) ∧ (∀ N, 0 ≤ ρI N) ∧ Tendsto ηI atTop (𝓝 0) ∧
      Tendsto ρI atTop (𝓝 0) ∧ (nI = 0 → ∀ N, ηI N = 0 ∧ ρI N = 0) ∧
      ∃ Cp Dp Cb C : ℝ, 0 ≤ Cp ∧ 0 ≤ Dp ∧ 0 ≤ Cb ∧ 0 ≤ C ∧
      ∀ᶠ q : ℕ in atTop, ∀ Ψ : SymSector ℂ (L2T L) (k + q), ‖Ψ‖ = 1 →
        ∀ t : ℕ → ℝ, (∀ r ∈ ords, |t r| ≤ T r) → ∀ θf : Fin nI → ℝ, (∀ i, |θf i| ≤ Θ i) →
          traceNorm (reducedDensityPower k q
              ((evolution (physBasis L hκ (k + q)) (mixedEv L κ ords t n θf (k + q)) 1 Ψ :
                SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
            reducedDensityPower k q
              ((evol ((((k + q : ℕ) : ℝ) : ℂ) •
                  LmixOp hκ u (μ : Measure ℝ) h (cutN L (alpha d) (k + q)) ords t n θf (k + q)) 1
                (wvec (k + q) u) : SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))) ≤
          ENNReal.ofReal (2 * ‖Ψ - wvec (k + q) u‖ +
            C * (Real.sqrt (ηI (k + q) + etaG d Cp Dp Cb ((k + q : ℕ) : ℝ) (cutN L (alpha d) (k + q))) +
              ρI (k + q) + W d (cutN L (alpha d) (k + q)) / ((k + q : ℕ) : ℝ) +
              W d (cutN L (alpha d) (k + q)) * Delta d ((k + q : ℕ) : ℝ))) := by
  have hL : 0 < L := Fact.out
  have hpi : 0 < Real.pi := Real.pi_pos
  -- the printed parameters (eq:MP-parameters)
  set α : ℝ := alpha d with hαdef
  have hα : 0 < α := alpha_pos d
  have hα56 : α ≤ 1 / 56 := by
    rw [hαdef]; unfold alpha
    have : (56 : ℝ) ≤ 56 * ((d : ℝ) + 1) := by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); nlinarith
    exact one_div_le_one_div_of_le (by norm_num) this
  have hsum : 3 * (1 / 8 : ℝ) + α < 1 := by linarith
  have hγ0 : (0 : ℝ) < 1 / 8 := by norm_num
  set b : ℕ := d + 2 with hbdef
  have hb1 : 1 ≤ b := by omega
  set p0 : ℕ := 28 * (d + 1) + 1 with hp0def
  have hp0 : 1 < 2 * (p0 : ℝ) * α := by
    rw [hαdef, hp0def]; unfold alpha
    have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
    have e : 2 * (((28 * (d + 1) + 1 : ℕ)) : ℝ) * (1 / (56 * ((d : ℝ) + 1))) = 1 + 1 / (28 * ((d : ℝ) + 1)) := by
      push_cast; field_simp; ring
    rw [e]
    have : 0 < 1 / (28 * ((d : ℝ) + 1)) := by positivity
    linarith
  -- the growing-window packet: ONE radius for the mass bound and the PROP-017/018 bundle
  obtain ⟨ρ, hρ0, h2ρ, -, hbadAll, C0, M, η, rd, K, Kd, hM1, hη, hrd, hK0, hev⟩ :=
    moving_contour_bundle_full hκ u hu hμ hηh hδ hd0 hin b b hb1 (by omega) α (1 / 8) hα hγ0 hsum p0 hp0
  have hh : 0 < h := by linarith
  have hM0 : 0 < M := by linarith
  -- the scalar datum and the fixed contours
  set S := QuantumNLS.Prop026Bound.scalarCuts hκ u hu with hSdef
  have hS : (μ : Measure ℝ) = S.μ := (QuantumNLS.Prop026Bound.physical_eq_limit hκ u hu hμ).symm
  have hGeq : Gfull (μ : Measure ℝ) = EmpiricalRapidity.cauchyTransform S.μ := by
    funext z; rw [Gfull_eq, hS]; rfl
  set xm : Fin nI → ℝ := xmS hκ u n with hxmdef
  set xp : Fin nI → ℝ := xpS hκ u n with hxpdef
  have hsep := fun i => QuantumNLS.Prop025OCount.separator_brackets L hκ u hu (n i)
  have hxm : ∀ i, xm i ∈ S.cuts := fun i => (hsep i).1
  have hxp : ∀ i, xp i ∈ S.cuts := fun i => (hsep i).2.1
  have hlt : ∀ i, xm i < xp i := fun i => (hsep i).2.2.1
  have h1 : ∀ i, 2 * Real.pi * (n i - 1) < IndexedScalarMeasure.exteriorForce L κ S.μ (xm i) :=
    fun i => (hsep i).2.2.2.1
  have h2 : ∀ i, IndexedScalarMeasure.exteriorForce L κ S.μ (xm i) < 2 * Real.pi * n i :=
    fun i => (hsep i).2.2.2.2.1
  have h3 : ∀ i, 2 * Real.pi * n i < IndexedScalarMeasure.exteriorForce L κ S.μ (xp i) :=
    fun i => (hsep i).2.2.2.2.2.1
  have h4 : ∀ i, IndexedScalarMeasure.exteriorForce L κ S.μ (xp i) < 2 * Real.pi * (n i + 1) :=
    fun i => (hsep i).2.2.2.2.2.2
  -- O3a: the fixed-contour event with transfer AND derivative deviations
  obtain ⟨Ed, ρd, hρd0, hρdlim, hEdm, hEd⟩ :=
    QuantumNLS.Prop025ODer.der_projection hκ u hu hμ S hS (h := fun _ => h) hxm hxp hlt (fun _ => hh) h1 h2 h3 h4
  -- the fixed background bounds and support distances
  obtain ⟨ηf, Mf, Gbf, hηf, hMf, hGbf, hbf⟩ :=
    gam_family_background S (h := fun _ => h) hxm hxp hlt (fun _ => hh) h1 h2 h3 h4
  choose dS hdS hsuppS using fun i => gam_supp_dist S (hxm i) (hxp i) hh
  -- the accepted PROP-010 extensions on the fixed contours
  have hex := fun i => QuantumNLS.Prop010SingleContourR17.condensate_reconstruction hκ u hu (n i) hh
  choose F H hF hFc hH hHc rf hR using hex
  set f : Fin nI → Extension (ℂ × ℂ) := fun i => Extension.ofSmooth (F i) (hF i) (hFc i) with hfdef
  set g : Fin nI → Extension (ℂ × (ℂ × ℂ)) := fun i => Extension.ofSmooth (H i) (hH i) (hHc i) with hgdef
  obtain ⟨r0, hr0, hr0le⟩ := exists_pos_le_all rf (fun i => (hR i).1)
  -- O3c: the count reconstruction event
  obtain ⟨Ec, Cc, hCc0, hEcm, hEc⟩ := QuantumNLS.Prop025OCount.count_event L hκ u hu hμ n hh hr0 f g
    (fun i z hz w hw => (hR i).2.1 z hz w (lt_of_lt_of_le hw (hr0le i)))
    (fun i z hz w v hw hv => (hR i).2.2.1 z hz w v (lt_of_lt_of_le hw (hr0le i)) hv)
  -- the printed `η^I`, `ρ^I` (zero for empty `I`)
  set Ed' : ∀ N : ℕ, Set (MArr N) := fun N => if nI = 0 then univ else Ed N with hEd'def
  set Ec' : ∀ N : ℕ, Set (MArr N) := fun N => if nI = 0 then univ else Ec N with hEc'def
  set ρI : ℕ → ℝ := fun N => if nI = 0 then 0 else ρd N with hρIdef
  set ηI : ℕ → ℝ := fun N => (bornMeasure (physBasis L hκ N) u hu).real (Ed' N)ᶜ +
    (bornMeasure (physBasis L hκ N) u hu).real (Ec' N)ᶜ with hηIdef
  have hne0 : ∀ i : Fin nI, nI ≠ 0 := fun i => (Fin.pos i).ne'
  have hEd' : ∀ᶠ N : ℕ in atTop, ∀ m ∈ Ed' N, ∀ i, ∀ w ∈ Gam (xm i) (xp i) h,
      (∀ j, 2 * |κ / (N : ℝ)| < ‖w - ((qAct L κ N m j : ℝ) : ℂ)‖) ∧
      ‖sNf L (κ / N) (qAct L κ N m) w - sf L κ (EmpiricalRapidity.cauchyTransform S.μ) w‖ ≤ ρI N ∧
      ‖deriv (sNf L (κ / N) (qAct L κ N m)) w -
        deriv (sf L κ (EmpiricalRapidity.cauchyTransform S.μ)) w‖ ≤ ρI N := by
    filter_upwards [hEd] with N hN m hm i w hw
    have hn := hne0 i
    simp only [hEd'def, hn, ite_false] at hm
    simp only [hρIdef, hn, ite_false]
    exact hN m hm i w hw
  have hEc' : ∀ᶠ N : ℕ in atTop, ∀ (hN : 0 < N), ∀ m ∈ Ec' N, ∀ i,
      |((m.1 (n i) : ℕ) : ℝ) - (N : ℝ) * c0 L hκ hN (f i) (xm i) (xp i) h m -
        c1 L hκ hN (g i) (xm i) (xp i) h m| ≤ Cc / N := by
    filter_upwards [hEc] with N hN hN0 m hm i
    have hn := hne0 i
    simp only [hEc'def, hn, ite_false] at hm
    exact hN hN0 m hm i
  have hηI0 : ∀ N, 0 ≤ ηI N := fun N => by positivity
  have hρI0 : ∀ N, 0 ≤ ρI N := fun N => by
    simp only [hρIdef]; split_ifs
    · exact le_rfl
    · exact hρd0 N
  have hηIlim : Tendsto ηI atTop (𝓝 0) := by
    by_cases hn : nI = 0
    · have : ηI = fun _ => 0 := by
        funext N; simp only [hηIdef, hEd'def, hEc'def, hn, ite_true, Set.compl_univ, measureReal_empty, add_zero]
      rw [this]; exact tendsto_const_nhds
    · have : ηI = fun N => (bornMeasure (physBasis L hκ N) u hu).real (Ed N)ᶜ +
          (bornMeasure (physBasis L hκ N) u hu).real (Ec N)ᶜ := by
        funext N; simp only [hηIdef, hEd'def, hEc'def, hn, ite_false]
      rw [this]; simpa using hEdm.add hEcm
  have hρIlim : Tendsto ρI atTop (𝓝 0) := by
    by_cases hn : nI = 0
    · have : ρI = fun _ => 0 := by funext N; simp only [hρIdef, hn, ite_true]
      rw [this]; exact tendsto_const_nhds
    · have : ρI = ρd := by funext N; simp only [hρIdef, hn, ite_false]
      rw [this]; exact hρdlim
  have hempty : nI = 0 → ∀ N, ηI N = 0 ∧ ρI N = 0 := fun hn N => by
    simp only [hηIdef, hρIdef, hEd'def, hEc'def, hn, ite_true, Set.compl_univ, measureReal_empty, add_zero,
      and_self]
  -- the combined event `𝓔_N ∩ E_der ∩ E_cnt`
  set E : ∀ N : ℕ, Set (MArr N) := fun N =>
    EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ) ((N : ℝ) ^ (-(1 / 8 : ℝ))) b ∩
      (Ed' N ∩ Ec' N) with hEdef
  have hevE := hev.mono fun N hN m (hm : m ∈ E N) => hN m hm.1
  -- the background family constants (window: bundle; fixed: `gam_family_background`)
  set Gb1 : ℝ := 1 / rd + 2 * K with hGb1def
  have hGb1 : 0 ≤ Gb1 := by rw [hGb1def]; positivity
  set d₀ : ℝ := min η ηf with hd₀def
  set s₁ : ℝ := max M Mf + max M Mf * max M Mf with hs₁def
  set a₀ : ℝ := 1 / max M Mf with ha₀def
  set c₁ : ℝ := κ * max Gb1 Gbf with hc₁def
  have hMm1 : 1 ≤ max M Mf := hM1.trans (le_max_left _ _)
  have hd₀ : 0 < d₀ := lt_min hη hηf
  have hs₁ : 0 ≤ s₁ := by rw [hs₁def]; nlinarith
  have ha₀ : 0 < a₀ := by rw [ha₀def]; exact one_div_pos.2 (by linarith)
  have hc₁ : 0 ≤ c₁ := mul_nonneg hκ.le (hGb1.trans (le_max_left _ _))
  have hrr : 0 < rad d₀ s₁ a₀ := by
    unfold rad; have := rho_pos hd₀ hs₁ ha₀; positivity
  -- PROP-018 (phase, scalar), the `C₀` identification and the window deviation on `E`
  have hph := phase_of_bundle hκ (μ : Measure ℝ) hh hρ0 hM1 hη hα hγ0 hb1 E hevE d (rad d₀ s₁ a₀ / 2)
    (half_pos hrr) (fz L κ (Gfull (μ : Measure ℝ)) (rad d₀ s₁ a₀)) (qch L κ (Gfull (μ : Measure ℝ)))
    (fun z w hw => fz_eq_lam hrr hw.le) (fun z w v _ _ => rfl)
  have hsc := scalar_of_bundle (μ : Measure ℝ) hh hρ0 hM1 hη hα hγ0 hb1 E hevE d (rad d₀ s₁ a₀ / 2)
    (half_pos hrr) (qch L κ (Gfull (μ : Measure ℝ))) (fun z w v _ _ => rfl)
  have hC0i := C0_identify hκ (μ : Measure ℝ) hh hρ0 hM1 hη hα hγ0 hb1 E hevE d (rad d₀ s₁ a₀) hrr
  have hdevb := deviation_of_bundle hκ (μ : Measure ℝ) E
    (hevE.mono fun N hN m hm z hz => ⟨(hN m hm z hz).1.1, (hN m hm z hz).2.2.2.2.2.2.2.2.2 0⟩)
  -- PROP-026 for the combined family
  set Λ : ℝ := ∑ i, Θ i * (2 * (xp i - xm i) + 4 * h) with hΛdef
  have hΛ0 : 0 ≤ Λ := Finset.sum_nonneg fun i _ => mul_nonneg (hΘ i) (by linarith [hlt i])
  have hRd : ∀ r ∈ ords, r ≤ d := fun r hr => Nat.lt_succ_iff.1 (Finset.mem_range.1 (hords hr))
  obtain ⟨Clin, hClin0, hlin⟩ := mp_linearization_contours L κ hκ h hh k d₀ s₁ a₀ c₁ hd₀ hs₁ ha₀ hc₁ d ords hRd T Λ
  -- constants
  obtain ⟨Cpp, hCpp⟩ : ∃ c : ℝ, c = κ ^ 2 + 4 * max C0 0 * (1 + h) ^ (d + 1) / (2 * Real.pi * κ) := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ c : ℝ,
      c = 4 * Lbd M η L ((M + M * M) / (ρ / 16)) (max Kd 0) (max Kd 0 / (ρ / 2)) * (1 + h) ^ (d + 1) /
        (2 * Real.pi) := ⟨_, rfl⟩
  rw [← hCpp] at hph
  rw [← hCs] at hsc
  have hCpp0 : 0 ≤ Cpp := by rw [hCpp]; positivity
  have hCs0 : 0 ≤ Cs := by
    have hVs0 : 0 ≤ (M + M * M) / (ρ / 16) := by positivity
    have hLq0 := Lbd_nonneg (L := L) hM1 hη hVs0 (le_max_right Kd 0) hρ0
    rw [hCs]; positivity
  set Lc : ℝ := ∑ i, Θ i * ((2 * Real.pi)⁻¹ * ((2 * (xp i - xm i) + 4 * h) * ((g i).constant : ℝ))) with hLcdef
  have hLc0 : 0 ≤ Lc := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hΘ i) (mul_nonneg (by positivity) (mul_nonneg (by linarith [hlt i]) (NNReal.coe_nonneg _)))
  set Ccs : ℝ := ∑ i, Θ i * Cc with hCcsdef
  have hCcs0 : 0 ≤ Ccs := Finset.sum_nonneg fun i _ => mul_nonneg (hΘ i) hCc0
  obtain ⟨Tm, hTm⟩ : ∃ s : ℝ, s = max (∑ r ∈ ords, T r) 0 := ⟨_, rfl⟩
  have hTm0 : 0 ≤ Tm := by rw [hTm]; exact le_max_right _ _
  have hpow : 0 ≤ (1 + h) ^ (d + 1) := by positivity
  set Ctot : ℝ := 8 + 2 * Cpp * Tm + 2 * Cs * Tm + 2 * Ccs + 2 * Lc +
    Clin * (2 * Real.pi * κ)⁻¹ * (max Kd 0 * (4 * Tm * (1 + h) ^ (d + 1))) + Clin * (2 * Real.pi * κ)⁻¹ * Λ
    with hCtotdef
  have hinv : 0 ≤ (2 * Real.pi * κ)⁻¹ := by positivity
  have hCtot0 : 0 ≤ Ctot := by
    rw [hCtotdef]
    have := mul_nonneg (mul_nonneg hClin0 hinv) (mul_nonneg (le_max_right Kd 0)
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hTm0) hpow))
    have := mul_nonneg (mul_nonneg hClin0 hinv) hΛ0
    positivity
  -- the packet mass constants (eq:MP-growing-mass)
  have hCms : 0 ≤ Csharp := by
    unfold Csharp; have := QuantumNLS.RootMeasureConcentrationSharp.Kc_nonneg; linarith
  have hCbn : 0 ≤ prop017Cb (eta0 L κ) h ρ Csharp b := QuantumNLS.PROP017UniformN.prop017Cb_nonneg hρ0 hCms
  refine ⟨ηI, ρI, hηI0, hρI0, hηIlim, hρIlim, hempty, max (Ctail (μ : Measure ℝ) p0) 0, max (Dtail κ p0) 0,
    prop017Cb (eta0 L κ) h ρ Csharp b, Ctot, le_max_right _ _, le_max_right _ _, hCbn, hCtot0, ?_⟩
  -- eventually in `N = k + q`
  have hkq : Tendsto (fun q : ℕ => k + q) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat k
  have hp01 : 1 ≤ p0 := by omega
  have hmass : ∀ᶠ N : ℕ in atTop, (bornMeasure (physBasis L hκ N) u hu).real (E N)ᶜ ≤
      etaG d (max (Ctail (μ : Measure ℝ) p0) 0) (max (Dtail κ p0) 0) (prop017Cb (eta0 L κ) h ρ Csharp b)
        (N : ℝ) (cutN L α N) + ηI N := by
    filter_upwards [hbadAll p0 hp01, eventually_ge_atTop 1] with N hN hN1
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
    have e : propBound (Ctail (μ : Measure ℝ) p0) (Dtail κ p0) (prop017Cb (eta0 L κ) h ρ Csharp b) p0 (N : ℝ)
        ((N : ℝ) ^ α) (cutN L α N) ((N : ℝ) ^ (-(1 / 8 : ℝ))) =
        etaG d (Ctail (μ : Measure ℝ) p0) (Dtail κ p0) (prop017Cb (eta0 L κ) h ρ Csharp b) (N : ℝ) (cutN L α N) := by
      unfold propBound etaG
      rw [hp0def, hαdef]
      simp only [one_div]
      ring
    have hm := measureReal_compl_inter3_le (bornMeasure (physBasis L hκ N) u hu)
      (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ) ((N : ℝ) ^ (-(1 / 8 : ℝ))) b)
      (Ed' N) (Ec' N)
    have hmono := etaG_mono d (Cb := prop017Cb (eta0 L κ) h ρ Csharp b) (a := cutN L α N)
      (le_max_left (Ctail (μ : Measure ℝ) p0) 0) (le_max_left (Dtail κ p0) 0) hNr
    rw [e] at hN
    show (bornMeasure (physBasis L hκ N) u hu).real (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N)
      ρ h (eta0 L κ) ((N : ℝ) ^ (-(1 / 8 : ℝ))) b ∩ (Ed' N ∩ Ec' N))ᶜ ≤ _
    rw [hηIdef]
    linarith
  have hmassT : Tendsto (fun N : ℕ => etaG d (max (Ctail (μ : Measure ℝ) p0) 0) (max (Dtail κ p0) 0)
      (prop017Cb (eta0 L κ) h ρ Csharp b) (N : ℝ) (cutN L α N) + ηI N) atTop (𝓝 0) := by
    obtain ⟨Cr, hCr0, hrate⟩ := QuantumNLS.Prop025OParams.total_rate d hd (3 * Real.pi / L)
      (max (Ctail (μ : Measure ℝ) p0) 0) (max (Dtail κ p0) 0) (prop017Cb (eta0 L κ) h ρ Csharp b) (by positivity)
      (le_max_right _ _) (le_max_right _ _) hCbn
    have hG0 : ∀ᶠ N : ℕ in atTop, 0 ≤ etaG d (max (Ctail (μ : Measure ℝ) p0) 0) (max (Dtail κ p0) 0)
        (prop017Cb (eta0 L κ) h ρ Csharp b) (N : ℝ) (cutN L α N) := by
      filter_upwards [eventually_ge_atTop 1] with N hN1
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN1
      have hc1 := (cut_bounds (θ := α) hL N).1
      have hRp : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr α
      have hep : 0 < (N : ℝ) ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hNr _
      have ha0 : 0 ≤ 1 + cutN L α N := by linarith
      have hCb' := hCbn
      have hC1 := le_max_right (Ctail (μ : Measure ℝ) p0) 0
      have hD1 := le_max_right (Dtail κ p0) 0
      unfold etaG
      rw [← hαdef]
      positivity
    have hGle : ∀ᶠ N : ℕ in atTop, etaG d (max (Ctail (μ : Measure ℝ) p0) 0) (max (Dtail κ p0) 0)
        (prop017Cb (eta0 L κ) h ρ Csharp b) (N : ℝ) (cutN L α N) ≤ (Cr * (N : ℝ) ^ (-(α / 4))) ^ 2 := by
      filter_upwards [eventually_ge_atTop 1, hG0] with N hN1 hG0N
      have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
      have hN0 : (0 : ℝ) < N := by linarith
      obtain ⟨hc1, hc2, -⟩ := cut_bounds (θ := α) hL N
      have hr := hrate N hNr (cutN L α N) hc1 hc2
      have hRp : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hN0 α
      have ha0 : 0 ≤ cutN L α N := by linarith
      have t1 : 0 ≤ (1 + cutN L α N) ^ (d + 1) / (N : ℝ) := by positivity
      have t2 : 0 ≤ (1 + cutN L α N) ^ (d + 1) * ((N : ℝ) ^ (-(1 / 8 : ℝ)) + (((N : ℝ) ^ alpha d) ^ (d + 2))⁻¹ +
          (N : ℝ)⁻¹) := by
        have : 0 < (N : ℝ) ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hN0 _
        have : 0 < (N : ℝ) ^ alpha d := Real.rpow_pos_of_pos hN0 _
        positivity
      have t3 : 0 ≤ (N : ℝ) ^ (-(1 / 4 : ℝ)) * ((1 + cutN L α N) ^ (d + 1)) ^ 7 := by
        have : 0 < (N : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_pos_of_pos hN0 _
        positivity
      have t4 : 0 ≤ cutN L α N ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg ha0 _
      have hsq : Real.sqrt (etaG d (max (Ctail (μ : Measure ℝ) p0) 0) (max (Dtail κ p0) 0)
          (prop017Cb (eta0 L κ) h ρ Csharp b) (N : ℝ) (cutN L α N)) ≤ Cr * (N : ℝ) ^ (-(α / 4)) := by
        unfold etaG
        rw [hαdef]
        linarith
      calc _ = (Real.sqrt (etaG d (max (Ctail (μ : Measure ℝ) p0) 0) (max (Dtail κ p0) 0)
            (prop017Cb (eta0 L κ) h ρ Csharp b) (N : ℝ) (cutN L α N))) ^ 2 := (Real.sq_sqrt hG0N).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2
    have hT : Tendsto (fun N : ℕ => (Cr * (N : ℝ) ^ (-(α / 4))) ^ 2) atTop (𝓝 0) := by
      have h0 := ((tendsto_rpow_neg_atTop (by positivity : 0 < α / 4)).comp tendsto_natCast_atTop_atTop).const_mul Cr
      have h1 := h0.pow 2
      simpa using h1
    have hGt := tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT hG0 hGle
    simpa using hGt.add hηIlim
  have hP1 : ∀ᶠ N : ℕ in atTop, etaG d (max (Ctail (μ : Measure ℝ) p0) 0) (max (Dtail κ p0) 0)
      (prop017Cb (eta0 L κ) h ρ Csharp b) (N : ℝ) (cutN L α N) + ηI N < 1 :=
    hmassT.eventually (gt_mem_nhds one_pos)
  have hρsmall : ∀ᶠ N : ℕ in atTop, ρI N < r0 ∧ ρI N ≤ rad d₀ s₁ a₀ / 2 :=
    (hρIlim.eventually (gt_mem_nhds hr0)).and (hρIlim.eventually (ge_mem_nhds (half_pos hrr)))
  have hbf' : ∀ z ∈ (⋃ i, Gam (xm i) (xp i) h),
      DifferentiableAt ℂ (Gfull (μ : Measure ℝ)) z ∧ ηf ≤ ‖Df L κ (Gfull (μ : Measure ℝ)) z‖ ∧
      ‖Af κ (Gfull (μ : Measure ℝ)) z‖ ≤ Mf ∧ ‖(Af κ (Gfull (μ : Measure ℝ)) z)⁻¹‖ ≤ Mf ∧ ‖ef L z‖ ≤ Mf ∧
      ‖Gfull (μ : Measure ℝ) z‖ ≤ Gbf := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hz
    rw [hGeq]; exact hbf i z hi
  have : IsProbabilityMeasure S.μ := S.isProb
  filter_upwards [hkq.eventually (hph.and (hsc.and (hC0i.and (hdevb.and (hevE.and (hEd'.and (hEc'.and
    (hmass.and (hP1.and (hρsmall.and ((regime_eventually hL hα hγ0 1 0).and (eventually_ge_atTop 1))))))))))))]
    with q ⟨hphN, hscN, hC0N, hdevN, hevN, hEdN, hEcN, hmassN, hP1N, hρN, hreg, hN1⟩
  intro Ψ hΨ t ht θf hθf
  have hN : 1 ≤ k + q := hN1
  have hNpos : 0 < k + q := hN
  have hNr : (0 : ℝ) < ((k + q : ℕ) : ℝ) := by exact_mod_cast hNpos
  set a : ℝ := cutN L α (k + q) with hadef
  have ha2 : 2 ≤ a := by linarith [hreg.1, hreg.2.2.1]
  have ha0 : 0 ≤ a := by linarith
  have hw1 := QuantumNLS.Prop020Main.norm_wvec (k + q) u hu
  have : Nontrivial (SymSector ℂ (L2T L) (k + q)) :=
    ⟨⟨wvec (k + q) u, 0, fun h0 => by rw [h0, norm_zero] at hw1; norm_num at hw1⟩⟩
  -- the common projection and `Φ_N`
  obtain ⟨PE, hPEb, _hidem, hsa, hnorm⟩ := event_projection hκ hNpos u hu (E (k + q))
  generalize hPr : (bornMeasure (physBasis L hκ (k + q)) u hu).real (E (k + q))ᶜ = Pr at hnorm hmassN
  have hw' : (1 - PE) (wvec (k + q) u) = wvec (k + q) u - PE (wvec (k + q) u) := rfl
  rw [hw'] at hnorm
  have hPr0 : 0 ≤ Pr := by rw [← hnorm]; positivity
  have hwP : ‖wvec (k + q) u - PE (wvec (k + q) u)‖ = Real.sqrt Pr := by
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  have hlt1 : ‖wvec (k + q) u - PE (wvec (k + q) u)‖ < 1 := by
    rw [hwP]
    calc Real.sqrt Pr < Real.sqrt 1 := Real.sqrt_lt_sqrt hPr0 (by linarith)
      _ = 1 := Real.sqrt_one
  obtain ⟨_hne, hΦ1, hΦw⟩ := normalize_proj PE (wvec (k + q) u) hw1 hlt1
  have hsuppΦ : ∀ m ∉ E (k + q), ⟪meanField_physicalBasis L (k + q) hN hκ m,
      ((‖PE (wvec (k + q) u)‖⁻¹ : ℂ) • PE (wvec (k + q) u))⟫_ℂ = 0 := by
    intro m hm
    have h0 : PE (meanField_physicalBasis L (k + q) hN hκ m) = 0 := by
      rw [hPEb m]
      split_ifs
      exact zero_smul _ _
    rw [inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left, hsa, h0, inner_zero_left, mul_zero]
  generalize hΦ : ((‖PE (wvec (k + q) u)‖⁻¹ : ℂ) • PE (wvec (k + q) u)) = Φ at hΦ1 hΦw hsuppΦ
  rw [hwP] at hΦw
  obtain ⟨m0, hm0⟩ : ∃ m, m ∈ E (k + q) := by
    by_contra hne
    push Not at hne
    have hs := QuantumNLS.RootMeasureTransfer.hasSum_norm_sq (meanField_physicalBasis L (k + q) hN hκ) Φ
    have h0 : (fun m => ‖⟪meanField_physicalBasis L (k + q) hN hκ m, Φ⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext m; rw [hsuppΦ m (hne m), norm_zero]; ring
    rw [h0] at hs
    have := hs.unique hasSum_zero
    rw [hΦ1] at this; norm_num at this
  -- the window bound `‖G_μ‖ ≤ 1/r + 2K`
  have hδle1 : ((k + q : ℕ) : ℝ) ^ (-(1 / 8 : ℝ)) + 1 / ((((k + q : ℕ) : ℝ)) ^ α) ^ b ≤ 2 := by
    have e1 : ((k + q : ℕ) : ℝ) ^ (-(1 / 8 : ℝ)) ≤ 1 := hreg.2.2.2.2
    have e2 : 1 ≤ ((((k + q : ℕ) : ℝ)) ^ α) ^ b := one_le_pow₀ hreg.1
    have e3 : 1 / ((((k + q : ℕ) : ℝ)) ^ α) ^ b ≤ 1 := by
      rw [div_le_one (by linarith)]; exact e2
    linarith
  have hGb : ∀ z ∈ NbhdN a h (ρ / 8), ‖Gfull (μ : Measure ℝ) z‖ ≤ Gb1 := by
    intro z hz
    have hP := hevN m0 hm0 z hz
    have e1 := hP.2.2.1
    have e2 := norm_GN_le_inv (qAct L κ (k + q) m0) hrd hP.2.2.2.1
    have e3 := norm_add_le (Gfull (μ : Measure ℝ) z - GN (qAct L κ (k + q) m0) z) (GN (qAct L κ (k + q) m0) z)
    rw [sub_add_cancel] at e3
    have e4 : K * (((k + q : ℕ) : ℝ) ^ (-(1 / 8 : ℝ)) + 1 / ((((k + q : ℕ) : ℝ)) ^ α) ^ b) ≤ K * 2 :=
      mul_le_mul_of_nonneg_left hδle1 hK0
    rw [hGb1def]; linarith
  -- ONE background on `Γ_a`'s neighbourhood ∪ the fixed contours
  let B : BgFam (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) h) d₀ s₁ a₀ c₁ :=
    bgfamOfG_union L κ (Gfull (μ : Measure ℝ)) (NbhdN a h (ρ / 8)) (⋃ i, Gam (xm i) (xp i) h)
      hη hηf hM1 hMf hGb1 hGbf hκ.le
      (fun z hz => hz.elim (fun h' => (hevN m0 hm0 z h').2.2.2.2.1) (fun h' => (hbf' z h').1))
      (fun z hz => (hevN m0 hm0 z hz).2.2.2.2.2.1) (fun z hz => (hbf' z hz).2.1)
      (fun z hz => (hevN m0 hm0 z hz).2.2.2.2.2.2.1) (fun z hz => (hbf' z hz).2.2.1)
      (fun z hz => (hevN m0 hm0 z hz).2.2.2.2.2.2.2.1) (fun z hz => (hbf' z hz).2.2.2.1)
      (fun z hz => (hevN m0 hm0 z hz).2.2.2.2.2.2.2.2.1) (fun z hz => (hbf' z hz).2.2.2.2.1)
      hGb (fun z hz => (hbf' z hz).2.2.2.2.2)
  have hBc0 : B.c0 = fun z => Complex.I * κ * Gfull (μ : Measure ℝ) z := rfl
  have hBD : B.D = Df L κ (Gfull (μ : Measure ℝ)) := rfl
  have hBs : B.s = sf L κ (Gfull (μ : Measure ℝ)) := rfl
  have hBA : B.A = Af κ (Gfull (μ : Measure ℝ)) := rfl
  -- the pieces
  set W := rectPieces a h (polyT ords t) (continuous_polyT ords t) with hWdef
  set Pf := rectFamily xm xp (fun _ => h) θf with hPfdef
  obtain ⟨hlen, hZf, hrealf⟩ := rectFamily_props xm xp (fun _ => h) θf Θ hlt (fun _ => hh) hθf
  have hZr : ∀ i : Fin 6, ∀ τ ∈ Icc (0 : ℝ) 1, (W i).γ τ ∈ (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) h) :=
    fun i τ hτ => Or.inl (rect_nbhd ha0 hh.le (by positivity) _ _ i τ hτ)
  have hZf' : ∀ j, ∀ τ ∈ Icc (0 : ℝ) 1, (Pf j).γ τ ∈ (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) h) := by
    intro j τ hτ
    obtain ⟨i, hi⟩ := hZf j τ hτ
    exact Or.inr (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hImf : ∀ j, ∀ τ ∈ Icc (0 : ℝ) 1, |((Pf j).γ τ).im| ≤ h := by
    intro j τ hτ
    obtain ⟨i, hi⟩ := hZf j τ hτ
    exact Gam_im_le hh.le hi
  have hZP : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, (Fin.append W Pf i).γ τ ∈
      (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) h) := by
    intro i
    refine Fin.addCases (fun i τ hτ => ?_) (fun j τ hτ => ?_) i
    · rw [Fin.append_left]; exact hZr i τ hτ
    · rw [Fin.append_right]; exact hZf' j τ hτ
  have hIP : ∀ i, ∀ τ ∈ Icc (0 : ℝ) 1, |((Fin.append W Pf i).γ τ).im| ≤ h := by
    intro i
    refine Fin.addCases (fun i τ hτ => ?_) (fun j τ hτ => ?_) i
    · rw [Fin.append_left]; exact rect_im_le ha0 hh.le _ _ i τ hτ
    · rw [Fin.append_right]; exact hImf j τ hτ
  -- the fixed-contour event facts in the `G_μ` form
  have hroot : ∀ m ∈ E (k + q), ∀ i, ∀ z ∈ Gam (xm i) (xp i) h, ∀ j, z ≠ ((qAct L κ (k + q) m j : ℝ) : ℂ) := by
    intro m hm i z hz j h0
    have h1 := (hEdN m hm.2.1 i z hz).1 j
    rw [h0, sub_self, norm_zero] at h1
    have : 0 ≤ 2 * |κ / ((k + q : ℕ) : ℝ)| := by positivity
    linarith
  have hdevG : ∀ m ∈ E (k + q), ∀ i, ∀ z ∈ Gam (xm i) (xp i) h,
      ‖sNf L (κ / ((k + q : ℕ) : ℝ)) (qAct L κ (k + q) m) z - sf L κ (Gfull (μ : Measure ℝ)) z‖ ≤ ρI (k + q) := by
    intro m hm i z hz
    rw [hGeq]; exact (hEdN m hm.2.1 i z hz).2.1
  -- PROP-026 on the event (window: bundle deviation; fixed: O3a)
  set δN : ℝ := ((k + q : ℕ) : ℝ) ^ (-(1 / 8 : ℝ)) + 1 / ((((k + q : ℕ) : ℝ)) ^ α) ^ b + 1 / ((k + q : ℕ) : ℝ)
    with hδNdef
  have hδN0 : 0 ≤ δN := by
    have : 0 < ((k + q : ℕ) : ℝ) ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hNr _
    have : 0 < ((k + q : ℕ) : ℝ) ^ α := Real.rpow_pos_of_pos hNr _
    rw [hδNdef]; positivity
  have hW := hlin q hN a ha0 t ht Pf hlen (NbhdN a h (ρ / 8) ∪ ⋃ i, Gam (xm i) (xp i) h) hZr hZf' hImf hrealf
    B Φ hΦ1 (max Kd 0 * δN) (ρI (k + q)) (mul_nonneg (le_max_right _ _) hδN0) (hρI0 _)
    (fun i τ hτ => by
      have := hdevN hN Φ hsuppΦ ((W i).γ τ)
        (rect_nbhd ha0 hh.le (by positivity) (polyT ords t) (continuous_polyT ords t) i τ hτ)
      rw [hΦ1, mul_one] at this
      exact this)
    (fun j τ hτ => by
      obtain ⟨i, hi⟩ := hZf j τ hτ
      have := transfer_deviation hκ hN (E (k + q)) ((Pf j).γ τ) (sf L κ (Gfull (μ : Measure ℝ)) ((Pf j).γ τ))
        (hρI0 _) (fun m hm => hroot m hm i _ hi) (fun m hm => hdevG m hm i _ hi) Φ hsuppΦ
      rw [hΦ1, mul_one] at this
      exact this)
  -- `L_N` is the PROP-026 `Lop`
  have hLeq : LmixOp hκ u (μ : Measure ℝ) h a ords t n θf (k + q) =
      Lop (nu (6 + nI * 6)) (fun θ => normalizedTransfer L κ (k + q) (zθ (Fin.append W Pf) θ))
        (uθ κ (Fin.append W Pf)) (dθ (Fin.append W Pf) B) := by
    rw [dθ_eq _ B hBD]; rfl
  have hpb : physBasis L hκ (k + q) = meanField_physicalBasis L (k + q) hN hκ := by
    unfold physBasis; simp only [hN, ↓reduceDIte]
  rw [hpb, hLeq]
  -- the `C₀` eigenvalue on every Bethe vector
  set xC0 : MArr (k + q) → ℝ := fun m => ∫ θ, (uθ κ (Fin.append W Pf) θ * gθ (Fin.append W Pf) B θ
      (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ (Fin.append W Pf) θ))).re ∂(nu (6 + nI * 6))
    with hxC0
  have hT0 : ∀ m, ((((k + q : ℕ) : ℝ) : ℂ) • C0op (nu (6 + nI * 6))
        (fun θ => normalizedTransfer L κ (k + q) (zθ (Fin.append W Pf) θ))
        (uθ κ (Fin.append W Pf)) (gθ (Fin.append W Pf) B)) (meanField_physicalBasis L (k + q) hN hκ m) =
      (((((k + q : ℕ) : ℝ) * xC0 m : ℝ)) : ℂ) • meanField_physicalBasis L (k + q) hN hκ m := by
    intro m
    rw [smul_apply, QuantumNLS.Prop020Link.C0_eig L hκ hN hc₁ _ B hZP hIP
      ((meanField_physicalBasis L (k + q) hN hκ).orthonormal.ne_zero m)
      (fun θ' => QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ (Fin.append W Pf) θ'))
      (fun θ' => transfer_physicalBasis hκ hN _ m), smul_smul, hxC0]
    congr 1
    simp only [Complex.ofReal_mul]
  -- the fixed-contour extension facts in the `G_μ` form
  have hfa : ∀ i, ∀ z ∈ Gam (xm i) (xp i) ((fun _ => h) i), ∀ w,
      ‖w - sf L κ (Gfull (μ : Measure ℝ)) z‖ < rf i → (f i).value (z, w) = localLog L κ (Gfull (μ : Measure ℝ)) z w := by
    intro i z hz w hw
    rw [hGeq] at hw ⊢
    exact (hR i).2.1 z hz w hw
  -- the summed eigenvalue inequality on the event
  set cs : ℝ := cscal L κ (μ : Measure ℝ) α h (pco ords t) d (k + q) +
    ∑ i, θf i * QuantumNLS.Prop025OCorr.c1bg L (κ := κ) (EmpiricalRapidity.cauchyTransform S.μ) (g i) (xm i) (xp i) h
    with hcsdef
  obtain ⟨Sp, hSp⟩ : ∃ s : ℝ, s = ∑ r ∈ Finset.range (d + 1), |pco ords t r| := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ s : ℝ, s = (1 + a) ^ (d + 1) := ⟨_, rfl⟩
  have hSp0 : 0 ≤ Sp := by rw [hSp]; positivity
  have hA1 : 1 ≤ A := by rw [hA]; exact one_le_pow₀ (by linarith)
  set δ1 : ℝ := Cpp * Sp * A / ((k + q : ℕ) : ℝ) + Cs * Sp * A * δN + Ccs / ((k + q : ℕ) : ℝ) + Lc * ρI (k + q)
    with hδ1def
  have hδ10 : 0 ≤ δ1 := by
    have := hρI0 (k + q)
    rw [hδ1def]; positivity
  have hδ : ∀ m ∈ E (k + q), |1 * mixedEv L κ ords t n θf (k + q) m - cs - ((k + q : ℕ) : ℝ) * xC0 m| ≤ δ1 := by
    intro m hm
    have hv1 : ‖meanField_physicalBasis L (k + q) hN hκ m‖ = 1 :=
      (meanField_physicalBasis L (k + q) hN hκ).orthonormal.1 m
    have hv0 : meanField_physicalBasis L (k + q) hN hκ m ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hv1; norm_num at hv1
    -- the eigenvalue split (O3e)
    have hme := QuantumNLS.Prop025OEigen.mixed_eig hκ hN m hc₁ B hBc0 hBD hBs hBA hrr W xm xp (fun _ => h) θf hlt
      (fun _ => hh) hZP hIP f rf hfa (fun i z hz j => hroot m hm i z hz j)
      (fun i z hz => ⟨lt_of_le_of_lt (hdevG m hm i z hz) (lt_of_lt_of_le hρN.1 (hr0le i)),
        (hdevG m hm i z hz).trans hρN.2⟩)
    have hce := QuantumNLS.Prop020Link.C0_eig L hκ hN hc₁ _ B hZP hIP hv0
      (fun θ' => QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ (Fin.append W Pf) θ'))
      (fun θ' => transfer_physicalBasis hκ hN _ m)
    have hx : xC0 m = (∫ θ, (uθ κ W θ * gθ W B θ
        (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ W θ))).re ∂(nu 6)) +
        ∑ i, θf i * c0 L hκ hN (f i) (xm i) (xp i) h m := by
      have e := hce.symm.trans hme
      have e2 := smul_left_injective ℂ hv0 e
      exact_mod_cast e2
    -- the window part (`C0_identify`)
    have hWW : W = rectPieces a h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t)) :=
      rectPieces_congr a h _ _ (polyT_eq_pw d ords hords t)
    have hwin : (∫ θ, (uθ κ W θ * gθ W B θ
        (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m (zθ W θ))).re ∂(nu 6)) =
        C0ev L κ (fz L κ (Gfull (μ : Measure ℝ)) (rad d₀ s₁ a₀)) α h (pco ords t) d (k + q) m := by
      rw [hWW, ← hC0N hN (pco ords t) m hm]
      congr 1
      funext θ'
      rw [gθ_eq_pt _ B hBc0 hBD hBs hBA]
    -- the four eigenvalue inequalities
    have i1 := hphN (pco ords t) m hm
    have i2 := hscN (pco ords t) m hm
    rw [sum_pco d ords hords t, ← hSp, ← hA] at i1
    rw [← hSp, ← hA] at i2
    have i3 : ∀ i, |((m.1 (n i) : ℕ) : ℝ) - ((k + q : ℕ) : ℝ) * c0 L hκ hN (f i) (xm i) (xp i) h m -
        c1 L hκ hN (g i) (xm i) (xp i) h m| ≤ Cc / ((k + q : ℕ) : ℝ) := fun i => hEcN hN m hm.2.2 i
    have i4 : ∀ i, |c1 L hκ hN (g i) (xm i) (xp i) h m -
        QuantumNLS.Prop025OCorr.c1bg L (κ := κ) (EmpiricalRapidity.cauchyTransform S.μ) (g i) (xm i) (xp i) h| ≤
        (2 * Real.pi)⁻¹ * ((2 * (xp i - xm i) + 4 * h) * ((g i).constant * ρI (k + q))) := fun i =>
      QuantumNLS.Prop025OCorr.c1_conc L hκ hN m S.μ (g i) (hlt i).le hh.le (hdS i) (hsuppS i)
        (fun w hw j => hroot m hm i w hw j) (fun w hw => ⟨(hEdN m hm.2.1 i w hw).2.1, (hEdN m hm.2.1 i w hw).2.2⟩)
    -- sum
    have hsplit : 1 * mixedEv L κ ords t n θf (k + q) m - cs - ((k + q : ℕ) : ℝ) * xC0 m =
        (∑ r ∈ ords, t r * eigenvalue L (k + q) (κ / ((k + q : ℕ) : ℝ)) r m -
          ((k + q : ℕ) : ℝ) * C0ev L κ (fz L κ (Gfull (μ : Measure ℝ)) (rad d₀ s₁ a₀)) α h (pco ords t) d (k + q) m -
          C1ev L κ (qch L κ (Gfull (μ : Measure ℝ))) α h (pco ords t) d (k + q) m) +
        (C1ev L κ (qch L κ (Gfull (μ : Measure ℝ))) α h (pco ords t) d (k + q) m -
          cscal L κ (μ : Measure ℝ) α h (pco ords t) d (k + q)) +
        ∑ i, θf i * (((m.1 (n i) : ℕ) : ℝ) - ((k + q : ℕ) : ℝ) * c0 L hκ hN (f i) (xm i) (xp i) h m -
          c1 L hκ hN (g i) (xm i) (xp i) h m) +
        ∑ i, θf i * (c1 L hκ hN (g i) (xm i) (xp i) h m -
          QuantumNLS.Prop025OCorr.c1bg L (κ := κ) (EmpiricalRapidity.cauchyTransform S.μ) (g i) (xm i) (xp i) h) := by
      rw [hx, hwin, hcsdef]
      unfold mixedEv
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring_nf
      simp only [Finset.mul_sum]
      ring_nf
    have s3 : |∑ i, θf i * (((m.1 (n i) : ℕ) : ℝ) - ((k + q : ℕ) : ℝ) * c0 L hκ hN (f i) (xm i) (xp i) h m -
          c1 L hκ hN (g i) (xm i) (xp i) h m)| ≤ Ccs / ((k + q : ℕ) : ℝ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hCcsdef, Finset.sum_div]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul, mul_div_assoc]
      exact mul_le_mul (hθf i) (i3 i) (abs_nonneg _) (hΘ i)
    have s4 : |∑ i, θf i * (c1 L hκ hN (g i) (xm i) (xp i) h m -
          QuantumNLS.Prop025OCorr.c1bg L (κ := κ) (EmpiricalRapidity.cauchyTransform S.μ) (g i) (xm i) (xp i) h)| ≤
        Lc * ρI (k + q) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [hLcdef, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      have := mul_le_mul (hθf i) (i4 i) (abs_nonneg _) (hΘ i)
      calc _ ≤ _ := this
        _ = _ := by ring
    rw [hsplit, hδ1def]
    refine (abs_add_le _ _).trans ?_
    refine add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add i1 i2)) s3)) s4
  -- the phase step and the chain
  have hstep := phase_step (meanField_physicalBasis L (k + q) hN hκ)
    (evolution (meanField_physicalBasis L (k + q) hN hκ) (mixedEv L κ ords t n θf (k + q)) 1)
    (fun m => 1 * mixedEv L κ ords t n θf (k + q) m)
    (fun m => evolution_basis _ _ 1 m) _ (fun m => ((k + q : ℕ) : ℝ) * xC0 m) hT0 cs (E (k + q)) hδ10 hδ Φ hΦ1
    hsuppΦ
  have hsaC : IsSelfAdjoint ((((k + q : ℕ) : ℝ) : ℂ) • C0op (nu (6 + nI * 6))
        (fun θ => normalizedTransfer L κ (k + q) (zθ (Fin.append W Pf) θ))
        (uθ κ (Fin.append W Pf)) (gθ (Fin.append W Pf) B)) := isSA_real_smul _ (isSA_reOp _)
  have hsaL : IsSelfAdjoint ((((k + q : ℕ) : ℝ) : ℂ) • Lop (nu (6 + nI * 6))
        (fun θ => normalizedTransfer L κ (k + q) (zθ (Fin.append W Pf) θ))
        (uθ κ (Fin.append W Pf)) (dθ (Fin.append W Pf) B)) := isSA_real_smul _ (isSA_reOp _)
  have hc : ‖Complex.exp (-((cs : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [show -((cs : ℝ) : ℂ) * Complex.I = ((-cs : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  set δ4 : ℝ := Clin * ((2 * Real.pi * κ)⁻¹ * ((max Kd 0 * δN) * (4 * (∑ r ∈ ords, T r) * (1 + h) ^ (d + 1) *
    (1 + a) ^ (d + 1)) + ρI (k + q) * Λ)) with hδ4def
  have hTsum0 : 0 ≤ ∑ r ∈ ords, T r := Finset.sum_nonneg fun r hr => (abs_nonneg _).trans (ht r hr)
  have hδ40 : 0 ≤ δ4 := by
    have := hρI0 (k + q)
    rw [hδ4def]; positivity
  have hchain := chain k q _ _ _ (fun x => evol_isometry _ hsaC 1 x) (fun x => evol_isometry _ hsaL 1 x)
    Ψ (wvec (k + q) u) Φ hΨ hw1 hΦ1 _ hc _ _ hstep hδ40 hW
  refine hchain.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the final arithmetic
  have hwΦ : ‖wvec (k + q) u - Φ‖ ≤ 2 * Real.sqrt (ηI (k + q) + etaG d (max (Ctail (μ : Measure ℝ) p0) 0)
      (max (Dtail κ p0) 0) (prop017Cb (eta0 L κ) h ρ Csharp b) ((k + q : ℕ) : ℝ) a) := by
    rw [norm_sub_rev]
    refine hΦw.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by norm_num))
  have hSpT : Sp ≤ Tm := by
    rw [hSp, sum_abs_pco d ords hords t]
    exact (Finset.sum_le_sum ht).trans (by rw [hTm]; exact le_max_left _ _)
  have hTsT : ∑ r ∈ ords, T r ≤ Tm := by rw [hTm]; exact le_max_left _ _
  have hδΔ : δN = Delta d ((k + q : ℕ) : ℝ) := by
    rw [hδNdef]; unfold Delta; rw [← hαdef]; simp only [one_div]; rfl
  have hAW : A = QuantumNLS.Prop025OFinal.W d a := by rw [hA]; rfl
  set sq : ℝ := Real.sqrt (ηI (k + q) + etaG d (max (Ctail (μ : Measure ℝ) p0) 0)
      (max (Dtail κ p0) 0) (prop017Cb (eta0 L κ) h ρ Csharp b) ((k + q : ℕ) : ℝ) a) with hsqdef
  have hsq0 : 0 ≤ sq := Real.sqrt_nonneg _
  have hρ0' := hρI0 (k + q)
  set X : ℝ := sq + ρI (k + q) + A / ((k + q : ℕ) : ℝ) + A * δN with hXdef
  have hAN : 0 ≤ A / ((k + q : ℕ) : ℝ) := by positivity
  have hAδ : 0 ≤ A * δN := by positivity
  have hN1A : 1 / ((k + q : ℕ) : ℝ) ≤ A / ((k + q : ℕ) : ℝ) := div_le_div_of_nonneg_right hA1 hNr.le
  -- term bounds
  have f1 : 2 * (Cpp * Sp * A / ((k + q : ℕ) : ℝ)) ≤ 2 * Cpp * Tm * (A / ((k + q : ℕ) : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hSpT hCpp0
    have h2 : Cpp * Sp * A / ((k + q : ℕ) : ℝ) = (Cpp * Sp) * (A / ((k + q : ℕ) : ℝ)) := by ring
    rw [h2]; nlinarith [mul_le_mul_of_nonneg_right this hAN]
  have f2 : 2 * (Cs * Sp * A * δN) ≤ 2 * Cs * Tm * (A * δN) := by
    have := mul_le_mul_of_nonneg_left hSpT hCs0
    have h2 : Cs * Sp * A * δN = (Cs * Sp) * (A * δN) := by ring
    rw [h2]; nlinarith [mul_le_mul_of_nonneg_right this hAδ]
  have f3 : 2 * (Ccs / ((k + q : ℕ) : ℝ)) ≤ 2 * Ccs * (A / ((k + q : ℕ) : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hN1A hCcs0
    rw [div_eq_mul_one_div Ccs]; nlinarith
  have f4 : δ4 ≤ Clin * (2 * Real.pi * κ)⁻¹ * (max Kd 0 * (4 * Tm * (1 + h) ^ (d + 1))) * (A * δN) +
      Clin * (2 * Real.pi * κ)⁻¹ * Λ * ρI (k + q) := by
    rw [hδ4def, ← hA]
    have hk : 0 ≤ Clin * (2 * Real.pi * κ)⁻¹ * (max Kd 0 * (4 * (1 + h) ^ (d + 1))) * (A * δN) := by
      have := le_max_right Kd 0; positivity
    have := mul_le_mul_of_nonneg_left hTsT hk
    nlinarith
  have f5 : 4 * ‖wvec (k + q) u - Φ‖ ≤ 8 * sq := by rw [hsqdef]; linarith
  -- `Ctot · X` dominates each term
  have g1 : 8 * sq ≤ 8 * X := by rw [hXdef]; linarith
  have g2 : 2 * Cpp * Tm * (A / ((k + q : ℕ) : ℝ)) ≤ 2 * Cpp * Tm * X :=
    mul_le_mul_of_nonneg_left (by rw [hXdef]; linarith) (by positivity)
  have g3 : 2 * Cs * Tm * (A * δN) ≤ 2 * Cs * Tm * X :=
    mul_le_mul_of_nonneg_left (by rw [hXdef]; linarith) (by positivity)
  have g4 : 2 * Ccs * (A / ((k + q : ℕ) : ℝ)) ≤ 2 * Ccs * X :=
    mul_le_mul_of_nonneg_left (by rw [hXdef]; linarith) (by positivity)
  have g5 : 2 * Lc * ρI (k + q) ≤ 2 * Lc * X :=
    mul_le_mul_of_nonneg_left (by rw [hXdef]; linarith) (by positivity)
  have hc6 : 0 ≤ Clin * (2 * Real.pi * κ)⁻¹ * (max Kd 0 * (4 * Tm * (1 + h) ^ (d + 1))) := by
    have := le_max_right Kd 0; positivity
  have g6 : Clin * (2 * Real.pi * κ)⁻¹ * (max Kd 0 * (4 * Tm * (1 + h) ^ (d + 1))) * (A * δN) ≤
      Clin * (2 * Real.pi * κ)⁻¹ * (max Kd 0 * (4 * Tm * (1 + h) ^ (d + 1))) * X :=
    mul_le_mul_of_nonneg_left (by rw [hXdef]; linarith) hc6
  have g7 : Clin * (2 * Real.pi * κ)⁻¹ * Λ * ρI (k + q) ≤ Clin * (2 * Real.pi * κ)⁻¹ * Λ * X :=
    mul_le_mul_of_nonneg_left (by rw [hXdef]; linarith) (by positivity)
  have hCX : Ctot * X = 8 * X + 2 * Cpp * Tm * X + 2 * Cs * Tm * X + 2 * Ccs * X + 2 * Lc * X +
      Clin * (2 * Real.pi * κ)⁻¹ * (max Kd 0 * (4 * Tm * (1 + h) ^ (d + 1))) * X +
      Clin * (2 * Real.pi * κ)⁻¹ * Λ * X := by rw [hCtotdef]; ring
  have hgoalX : sq + ρI (k + q) + QuantumNLS.Prop025OFinal.W d a / ((k + q : ℕ) : ℝ) + QuantumNLS.Prop025OFinal.W d a * Delta d ((k + q : ℕ) : ℝ) = X := by
    rw [hXdef, ← hAW, ← hδΔ]
  rw [hgoalX, hδ1def]
  linarith

end QuantumNLS.Prop025OPhase

#print axioms QuantumNLS.Prop025OPhase.norm_GN_le_inv
#print axioms QuantumNLS.Prop025OPhase.etaG_mono
#print axioms QuantumNLS.Prop025OPhase.measureReal_compl_inter3_le
#print axioms QuantumNLS.Prop025OPhase.quantum_comparison

-- Recursive type/value audit of every own declaration: standard axioms only, and no held
-- identifier (HeldGP14Tonelli, the superseded pre-D1 `RegularCut`) in the transitive closure.
set_option maxHeartbeats 16000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Prop025OPhase." then
      pending := pending.push n
  let own := pending.size
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if (n.toString.splitOn "HeldGP14Tonelli").length > 1 ||
          n.components.any (fun c => c.toString == "RegularCut") then
        throwError "Held dependency: {n}"
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Prop025OPhase aggregate audit PASS: {own} own constants, {seen.size} transitive constants; standard-only, no held identifiers."
