import QuantumNLS.Prop020Link
import QuantumNLS.Prop020Chain

/-!
# PROP-020 `Q7A:thm:main` (`window_reconstruction.tex:254`): full-charge comparison on polynomial windows

Source statement: fix a finite collection of charge orders contained in `{0,…,d}`, a fixed marginal rank `k`, and a compact
joint-time box `|t_r| ≤ T_r`. Choose `0 < α < 1/(3d+4)`, `(d+1)α < γ < (1−α)/3`, `b > d+1`, and put `R = N^α`, `ε = N^{−γ}`.
For every normalized preparation `Ψ_N` with `‖Ψ_N − u^{⊗N}‖ → 0`,
`sup_{|t_r| ≤ T_r} ‖γ^{(k)}_{exp(−i Σ_r t_r Q_{N,r})Ψ_N} − γ^{(k)}_{exp(−iN Σ_r t_r L_{N,x^r}) u^{⊗N}}‖₁ → 0`
(`eq:fullcompare`), and more precisely the left side is at most
`2‖Ψ_N − u^{⊗N}‖ + 8√η_N + C(N^{α(d+1)−γ} + N^{−α(b−d−1)} + N^{α(d+1)−1})` (`eq:finalrate`).

Lean objects (all actual, no new hypotheses besides `RootSpectralInputs`):
* `Q_{N,r}` = the actual full charges `BetheSpectralCharges.charge (physBasis) (κ/N) r` with spectrum `eigenvalue L N (κ/N) r`
  on the actual Bethe basis; `exp(−i Σ_r t_r Q_{N,r})` = their joint spectral unitary
  `BetheSpectralCharges.evolution (physBasis L hκ N) (Σ_r t_r · eigenvalue_r) 1`;
* `L_{N,x^r}` = `Prop020Link.Lwin … (fun z => z ^ r)` (`Q7A:eq:linear` along `Γ_N`), `exp(−iNX) = evol (N X) 1`;
* `u^{⊗N}` = `HighMomentsOps.wvec N u`; `γ^{(k)}` = `reducedDensityPower k q` with `N = k + q`; `‖·‖₁` = `traceNorm`;
* `𝓔_N` = the PROP-017 event `EN` at `R_N = N^α`, `ε_N = N^{−γ}`, the designated cut `a_N = cutN L α N`.

Proof (the printed one): `Φ_N = P_N u^{⊗N}/‖P_N u^{⊗N}‖` (`event_projection`, `normalize_proj`); PROP-018 (`phase_of_bundle`,
`scalar_of_bundle`) on the same event as PROP-019 (`linearization_of_bundle`) via ONE call of `moving_contour_bundle`; the
`C₀` eigenvalue identification (`C0_identify`); the phase step and the trace-norm chain.
-/

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop020Main

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.EmpiricalRapidity (bornMeasure)
open QuantumNLS.BulkResponseActual (physBasis IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (GammaN NbhdN)
open QuantumNLS.PROP018Probability (cutN regime_eventually)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs event_projection)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.Prop018Phase (qch C0ev C1ev phase_of_bundle)
open QuantumNLS.Prop018Scalar (cscal scalar_of_bundle Lbd Lbd_nonneg)
open QuantumNLS.Prop018Bundle (moving_contour_bundle)
open QuantumNLS.Prop019Linearization (pw continuous_pw)
open QuantumNLS.Prop019Discharge (mp_statement)
open QuantumNLS.Prop020Vector (normalize_proj)
open QuantumNLS.Prop020Diag (C0op_eigen evol_isometry)
open QuantumNLS.Prop020Link
open QuantumNLS.Prop020Chain
open QuantumNLS.MPContour (ThetaSpace nu zθ uθ rectPieces continuous_zθ)
open QuantumNLS.MPFamily (BgFam gθ dθ good contDiff_gθ)
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

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

theorem norm_wvec (N : ℕ) (u : L2T L) (hu : ‖u‖ = 1) : ‖wvec N u‖ = 1 := by
  rw [← Submodule.norm_coe]
  show ‖(QuantumNLS.TensorCarrier.htpow N u : HilbertTensorPower ℂ (L2T L) N)‖ = 1
  rw [QuantumNLS.TensorCarrier.norm_htpow, hu, one_pow]

/-- **PROP-020 `Q7A:thm:main`, rate form (`eq:finalrate`)**, for the actual model with `RootSpectralInputs` as the only open
hypothesis. Parameters as printed (`eq:parameters`): `0 < α < 1/(3d+4)`, `(d+1)α < γ < (1−α)/3`, `b > d+1`; `R_N = N^α`,
`ε_N = N^{−γ}`; a finite collection `ords ⊆ {0,…,d}` of charge orders and a joint-time box `|t_r| ≤ T_r`. There is a packet event
`𝓔_N` with `P_{N,u}(𝓔_Nᶜ) → 0` and a constant `C` such that, eventually (`N = k + q`), for every normalized `Ψ` and every `t` in the
box, `‖γ^{(k)}_{exp(−iΣ_r t_r Q_{N,r})Ψ} − γ^{(k)}_{exp(−iNΣ_r t_r L_{N,x^r})u^{⊗N}}‖₁ ≤
2‖Ψ − u^{⊗N}‖ + 8√P_{N,u}(𝓔_Nᶜ) + C(N^{α(d+1)−γ} + N^{−α(b−d−1)} + N^{α(d+1)−1})`. -/
theorem prop020_rate (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d k : ℕ) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    (α γ : ℝ) (b : ℕ) (hα : 0 < α) (_hα' : α < 1 / (3 * (d : ℝ) + 4))
    (hγ1 : ((d : ℝ) + 1) * α < γ) (hγ2 : γ < (1 - α) / 3) (hb : (d : ℝ) + 1 < b) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun N : ℕ => (bornMeasure (physBasis L hκ N) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ)
        atTop (𝓝 0) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ q : ℕ in atTop, ∀ Ψ : SymSector ℂ (L2T L) (k + q), ‖Ψ‖ = 1 →
        ∀ t : ℕ → ℝ, (∀ r ∈ ords, |t r| ≤ T r) →
          traceNorm (reducedDensityPower k q
              ((evolution (physBasis L hκ (k + q))
                (fun m => ∑ r ∈ ords, t r * eigenvalue L (k + q) (κ / ((k + q : ℕ) : ℝ)) r m) 1 Ψ :
                SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
            reducedDensityPower k q
              ((evol ((((k + q : ℕ) : ℝ) : ℂ) • ∑ r ∈ ords, ((t r : ℝ) : ℂ) •
                  Lwin L κ (μ : Measure ℝ) α h (k + q) (fun z => z ^ r) (continuous_pow r)) 1
                (wvec (k + q) u) : SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))) ≤
          ENNReal.ofReal (2 * ‖Ψ - wvec (k + q) u‖ +
            8 * Real.sqrt ((bornMeasure (physBasis L hκ (k + q)) u hu).real
              (EN (μ : Measure ℝ) (qAct L κ (k + q)) (((k + q : ℕ) : ℝ) ^ α) (cutN L α (k + q)) ρ h (eta0 L κ)
                (((k + q : ℕ) : ℝ) ^ (-γ)) b)ᶜ) +
            C * ((((k + q : ℕ) : ℝ)) ^ (α * ((d : ℝ) + 1) - γ) +
              (((k + q : ℕ) : ℝ)) ^ (-(α * ((b : ℝ) - d - 1))) +
              (((k + q : ℕ) : ℝ)) ^ (α * ((d : ℝ) + 1) - 1))) := by
  have hL : 0 < L := Fact.out
  have hpi : 0 < Real.pi := Real.pi_pos
  have hγ0 : 0 < γ := by
    have : 0 < ((d : ℝ) + 1) * α := by positivity
    linarith
  have hsum : 3 * γ + α < 1 := by linarith
  have hb1 : 1 ≤ b := by
    have h1 : (1 : ℝ) ≤ b := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
    exact_mod_cast h1
  have hpt : 1 < 2 * ((⌈1 / α⌉₊ : ℕ) : ℝ) * α := by
    have h1 : 1 / α ≤ ((⌈1 / α⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : 1 ≤ ((⌈1 / α⌉₊ : ℕ) : ℝ) * α := by rw [div_le_iff₀ hα] at h1; linarith
    linarith
  obtain ⟨ρ, hρ0, h2ρ, hprob, C0, M, η, r, K, Kd, hM1, hη, hr0, hK0, hev⟩ :=
    moving_contour_bundle hκ u hu hμ hηh hδ hd0 hin b b hb1 (by omega) α γ hα hγ0 hsum ⌈1 / α⌉₊ hpt
  refine ⟨ρ, hρ0, hprob, ?_⟩
  have hh : 0 < h := by linarith
  have hM0 : 0 < M := by linarith
  obtain ⟨d₀, s₁, a₀, c₁, Clin, hd₀, hs₁, ha₀, hc₁, hClin, hlin⟩ :=
    linearization_of_bundle hκ (μ : Measure ℝ) hh hρ0 hM1 hη hr0 hK0 hα hγ0
      (fun N => EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)
      hev d k (mp_statement L hκ h k)
  have hrr : 0 < rad d₀ s₁ a₀ := by
    unfold rad; have := rho_pos hd₀ hs₁ ha₀; positivity
  have hph := phase_of_bundle hκ (μ : Measure ℝ) hh hρ0 hM1 hη hα hγ0 hb1
    (fun N => EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)
    hev d (rad d₀ s₁ a₀ / 2) (half_pos hrr) (fz L κ (Gfull (μ : Measure ℝ)) (rad d₀ s₁ a₀))
    (qch L κ (Gfull (μ : Measure ℝ))) (fun z w hw => fz_eq_lam hrr hw.le) (fun z w v _ _ => rfl)
  have hsc := scalar_of_bundle (μ : Measure ℝ) hh hρ0 hM1 hη hα hγ0 hb1
    (fun N => EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)
    hev d (rad d₀ s₁ a₀ / 2) (half_pos hrr) (qch L κ (Gfull (μ : Measure ℝ))) (fun z w v _ _ => rfl)
  have hC0i := C0_identify hκ (μ : Measure ℝ) hh hρ0 hM1 hη hα hγ0 hb1
    (fun N => EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)
    hev d (rad d₀ s₁ a₀) hrr
  obtain ⟨Cp, hCp⟩ : ∃ c : ℝ, c = κ ^ 2 + 4 * max C0 0 * (1 + h) ^ (d + 1) / (2 * Real.pi * κ) := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ c : ℝ,
      c = 4 * Lbd M η L ((M + M * M) / (ρ / 16)) (max Kd 0) (max Kd 0 / (ρ / 2)) * (1 + h) ^ (d + 1) /
        (2 * Real.pi) := ⟨_, rfl⟩
  rw [← hCp] at hph
  rw [← hCs] at hsc
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  have hCs0 : 0 ≤ Cs := by
    have hVs0 : 0 ≤ (M + M * M) / (ρ / 16) := by positivity
    have hLq0 := Lbd_nonneg (L := L) hM1 hη hVs0 (le_max_right Kd 0) hρ0
    rw [hCs]; positivity
  obtain ⟨Tsum, hTsum⟩ : ∃ s : ℝ, s = ∑ r ∈ ords, T r := ⟨_, rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ, c = 3 + 3 * Real.pi / L := ⟨_, rfl⟩
  have hc₂0 : 0 ≤ c₂ := by rw [hc₂]; positivity
  refine ⟨(2 * Cp + 2 * Cs + Clin) * max Tsum 0 * c₂ ^ (d + 1), by positivity, ?_⟩
  have hkq : Tendsto (fun q : ℕ => k + q) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat k
  have hP1 : ∀ᶠ N : ℕ in atTop, (bornMeasure (physBasis L hκ N) u hu).real
      (EN (μ : Measure ℝ) (qAct L κ N) ((N : ℝ) ^ α) (cutN L α N) ρ h (eta0 L κ) ((N : ℝ) ^ (-γ)) b)ᶜ < 1 :=
    hprob.eventually (gt_mem_nhds one_pos)
  filter_upwards [hkq.eventually (hph.and (hsc.and (hC0i.and (hev.and (hP1.and
    ((regime_eventually hL hα hγ0 1 0).and (eventually_ge_atTop 1))))))), hlin]
    with q ⟨hphN, hscN, hC0N, hevN, hP1N, hreg, hN1⟩ hlinq
  intro Ψ hΨ t ht
  have hN : 1 ≤ k + q := hN1
  have hNpos : 0 < k + q := hN
  have hNr : (0 : ℝ) < ((k + q : ℕ) : ℝ) := by exact_mod_cast hNpos
  have ha2 : 2 ≤ cutN L α (k + q) := by linarith [hreg.1, hreg.2.2.1]
  have hw1 := norm_wvec (k + q) u hu
  have : Nontrivial (SymSector ℂ (L2T L) (k + q)) :=
    ⟨⟨wvec (k + q) u, 0, fun h0 => by rw [h0, norm_zero] at hw1; norm_num at hw1⟩⟩
  -- the event projection and `Φ_N`
  obtain ⟨PE, hPEb, _hidem, hsa, hnorm⟩ := event_projection hκ hNpos u hu
    (EN (μ : Measure ℝ) (qAct L κ (k + q)) (((k + q : ℕ) : ℝ) ^ α) (cutN L α (k + q)) ρ h (eta0 L κ)
      (((k + q : ℕ) : ℝ) ^ (-γ)) b)
  generalize hPr : (bornMeasure (physBasis L hκ (k + q)) u hu).real
    (EN (μ : Measure ℝ) (qAct L κ (k + q)) (((k + q : ℕ) : ℝ) ^ α) (cutN L α (k + q)) ρ h (eta0 L κ)
      (((k + q : ℕ) : ℝ) ^ (-γ)) b)ᶜ = Pr at hnorm hP1N ⊢
  have hw' : (1 - PE) (wvec (k + q) u) = wvec (k + q) u - PE (wvec (k + q) u) := rfl
  rw [hw'] at hnorm
  have hPr0 : 0 ≤ Pr := by rw [← hnorm]; positivity
  have hwP : ‖wvec (k + q) u - PE (wvec (k + q) u)‖ = Real.sqrt Pr := by
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  have hlt : ‖wvec (k + q) u - PE (wvec (k + q) u)‖ < 1 := by
    rw [hwP]
    calc Real.sqrt Pr < Real.sqrt 1 := Real.sqrt_lt_sqrt hPr0 hP1N
      _ = 1 := Real.sqrt_one
  obtain ⟨_hne, hΦ1, hΦw⟩ := normalize_proj PE (wvec (k + q) u) hw1 hlt
  have hsuppΦ : ∀ m ∉ EN (μ : Measure ℝ) (qAct L κ (k + q)) (((k + q : ℕ) : ℝ) ^ α) (cutN L α (k + q)) ρ h
      (eta0 L κ) (((k + q : ℕ) : ℝ) ^ (-γ)) b,
      ⟪meanField_physicalBasis L (k + q) hN hκ m,
        ((‖PE (wvec (k + q) u)‖⁻¹ : ℂ) • PE (wvec (k + q) u))⟫_ℂ = 0 := by
    intro m hm
    have h0 : PE (meanField_physicalBasis L (k + q) hN hκ m) = 0 := by
      rw [hPEb m]
      split_ifs
      exact zero_smul _ _
    rw [inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left, hsa, h0, inner_zero_left, mul_zero]
  generalize hΦ : ((‖PE (wvec (k + q) u)‖⁻¹ : ℂ) • PE (wvec (k + q) u)) = Φ at hΦ1 hΦw hsuppΦ
  rw [hwP] at hΦw
  -- a label of the event
  obtain ⟨m0, hm0⟩ : ∃ m, m ∈ EN (μ : Measure ℝ) (qAct L κ (k + q)) (((k + q : ℕ) : ℝ) ^ α) (cutN L α (k + q)) ρ h
      (eta0 L κ) (((k + q : ℕ) : ℝ) ^ (-γ)) b := by
    by_contra hne
    push Not at hne
    have hs := QuantumNLS.RootMeasureTransfer.hasSum_norm_sq (meanField_physicalBasis L (k + q) hN hκ) Φ
    have h0 : (fun m => ‖⟪meanField_physicalBasis L (k + q) hN hκ m, Φ⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext m; rw [hsuppΦ m (hne m), norm_zero]; ring
    rw [h0] at hs
    have := hs.unique hasSum_zero
    rw [hΦ1] at this; norm_num at this
  -- PROP-019 on the same event
  obtain ⟨B, hBc0, hBD, hBs, hBA, hbd⟩ := hlinq hN Φ hΦ1 hsuppΦ
  have hW := hbd 1 (pco ords t)
  -- abbreviations
  obtain ⟨Sp, hSp⟩ : ∃ s : ℝ, s = ∑ r ∈ Finset.range (d + 1), |pco ords t r| := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ s : ℝ, s = (1 + cutN L α (k + q)) ^ (d + 1) := ⟨_, rfl⟩
  obtain ⟨δN, hδN⟩ : ∃ s : ℝ, s = (((k + q : ℕ) : ℝ)) ^ (-γ) + 1 / ((((k + q : ℕ) : ℝ)) ^ α) ^ b +
      1 / ((k + q : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [abs_one, one_mul, ← hSp, ← hA, ← hδN] at hW
  have hSp0 : 0 ≤ Sp := by rw [hSp]; positivity
  have hA0 : 0 ≤ A := by
    have : (0 : ℝ) ≤ cutN L α (k + q) := by linarith
    rw [hA]; positivity
  have hδN0 : 0 ≤ δN := by
    have : 0 < (((k + q : ℕ) : ℝ)) ^ (-γ) := Real.rpow_pos_of_pos hNr _
    have : 0 < (((k + q : ℕ) : ℝ)) ^ α := Real.rpow_pos_of_pos hNr _
    rw [hδN]; positivity
  -- the window contour and its geometry
  have hZ := rect_nbhd (ρ' := ρ / 8) (by linarith : (0 : ℝ) ≤ cutN L α (k + q)) hh.le (by positivity)
    (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))
  have hIm := rect_im_le (by linarith : (0 : ℝ) ≤ cutN L α (k + q)) hh.le
    (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))
  -- continuity of `D⁻¹` along `Γ_N`
  have hDfc : ∀ z ∈ NbhdN (cutN L α (k + q)) h (ρ / 8),
      ContinuousAt (Df L κ (Gfull (μ : Measure ℝ))) z ∧ Df L κ (Gfull (μ : Measure ℝ)) z ≠ 0 := fun z hz => by
    have hP := hevN m0 hm0 z hz
    have hGc : ContinuousAt (Gfull (μ : Measure ℝ)) z := hP.2.2.2.2.1.continuousAt
    have hAc : ContinuousAt (Af κ (Gfull (μ : Measure ℝ))) z := (hGc.const_mul (Complex.I * κ)).cexp
    have hec : ContinuousAt (ef L) z := (hasDerivAt_ef L z).continuousAt
    refine ⟨hAc.sub (hec.div hAc (Complex.exp_ne_zero _)), fun h0 => ?_⟩
    have := hP.2.2.2.2.2.1; rw [h0, norm_zero] at this; linarith
  have hZ1 := rect_nbhd (ρ' := ρ / 8) (by linarith : (0 : ℝ) ≤ cutN L α (k + q)) hh.le (by positivity)
    (fun _ => (1 : ℂ)) continuous_const
  have hd : Continuous fun θ' => (Df L κ (Gfull (μ : Measure ℝ))
      (zθ (rectPieces (cutN L α (k + q)) h (fun _ => (1 : ℂ)) continuous_const) θ'))⁻¹ :=
    continuous_iff_continuousAt.2 fun θ' =>
      ((hDfc (zθ (rectPieces (cutN L α (k + q)) h (fun _ => (1 : ℂ)) continuous_const) θ')
          (hZ1 θ'.1 θ'.2 ⟨θ'.2.2.1, θ'.2.2.2⟩)).1.comp (continuous_zθ _).continuousAt).inv₀
        (hDfc (zθ (rectPieces (cutN L α (k + q)) h (fun _ => (1 : ℂ)) continuous_const) θ')
          (hZ1 θ'.1 θ'.2 ⟨θ'.2.2.1, θ'.2.2.2⟩)).2
  -- `Σ_r t_r L_{N,x^r} = L_{N,p_t}` (the operator of PROP-019)
  have hLsum : ∑ r ∈ ords, ((t r : ℝ) : ℂ) • Lwin L κ (μ : Measure ℝ) α h (k + q) (fun z => z ^ r)
      (continuous_pow r) = Lop (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
        (zθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) θ'))
        (uθ κ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))))
        (dθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) B) := by
    rw [Lwin_lin (k + q) ords t hd,
      Lwin_congr _ (continuous_pw d 1 (pco ords t)) (pw_pco d ords hords t).symm,
      Lwin_eq_Lop hh, dθ_eq _ B hBD]
  have hpb : physBasis L hκ (k + q) = meanField_physicalBasis L (k + q) hN hκ := by
    unfold physBasis; simp only [hN, ↓reduceDIte]
  rw [hpb, hLsum]
  -- the `C₀` evolution on the actual Bethe vectors
  obtain ⟨xC0, hxC0⟩ : ∃ x : MArr (k + q) → ℝ, x = fun m => ∫ θ',
      (uθ κ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) θ' *
        gθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) B θ'
          (QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m
            (zθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) θ'))).re
        ∂(nu 6) := ⟨_, rfl⟩
  have hT0 : ∀ m, ((((k + q : ℕ) : ℝ) : ℂ) • C0op (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
        (zθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) θ'))
        (uθ κ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))))
        (gθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) B))
        (meanField_physicalBasis L (k + q) hN hκ m) =
      (((((k + q : ℕ) : ℝ) * xC0 m : ℝ)) : ℂ) • meanField_physicalBasis L (k + q) hN hκ m := by
    intro m
    rw [smul_apply, C0_eig L hκ hN hc₁ _ B hZ hIm
      ((meanField_physicalBasis L (k + q) hN hκ).orthonormal.ne_zero m)
      (fun θ' => QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m
        (zθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) θ'))
      (fun θ' => transfer_physicalBasis hκ hN _ m), smul_smul, hxC0]
    congr 1
    simp only [Complex.ofReal_mul]
  -- the eigenvalue bound on `𝓔_N`
  have hδ : ∀ m ∈ EN (μ : Measure ℝ) (qAct L κ (k + q)) (((k + q : ℕ) : ℝ) ^ α) (cutN L α (k + q)) ρ h
      (eta0 L κ) (((k + q : ℕ) : ℝ) ^ (-γ)) b,
      |1 * (∑ r ∈ ords, t r * eigenvalue L (k + q) (κ / ((k + q : ℕ) : ℝ)) r m) -
          cscal L κ (μ : Measure ℝ) α h (pco ords t) d (k + q) - ((k + q : ℕ) : ℝ) * xC0 m| ≤
        Cp * Sp * A / ((k + q : ℕ) : ℝ) + Cs * Sp * A * δN := by
    intro m hm
    have hx : xC0 m = C0ev L κ (fz L κ (Gfull (μ : Measure ℝ)) (rad d₀ s₁ a₀)) α h (pco ords t) d (k + q) m := by
      rw [hxC0]
      beta_reduce
      rw [← hC0N hN (pco ords t) m hm]
      congr 1
      funext θ'
      rw [gθ_eq_pt _ B hBc0 hBD hBs hBA]
    have h1 := hphN (pco ords t) m hm
    have h2 := hscN (pco ords t) m hm
    rw [sum_pco d ords hords t, ← hSp, ← hA] at h1
    rw [← hSp, ← hA, ← hδN] at h2
    rw [one_mul, hx]
    calc _ = |(∑ r ∈ ords, t r * eigenvalue L (k + q) (κ / ((k + q : ℕ) : ℝ)) r m -
            ((k + q : ℕ) : ℝ) * C0ev L κ (fz L κ (Gfull (μ : Measure ℝ)) (rad d₀ s₁ a₀)) α h (pco ords t) d (k + q) m -
            C1ev L κ (qch L κ (Gfull (μ : Measure ℝ))) α h (pco ords t) d (k + q) m) +
          (C1ev L κ (qch L κ (Gfull (μ : Measure ℝ))) α h (pco ords t) d (k + q) m -
            cscal L κ (μ : Measure ℝ) α h (pco ords t) d (k + q))| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add h1 h2)
  have hδ1 : 0 ≤ Cp * Sp * A / ((k + q : ℕ) : ℝ) + Cs * Sp * A * δN := by positivity
  have hstep := phase_step (meanField_physicalBasis L (k + q) hN hκ)
    (evolution (meanField_physicalBasis L (k + q) hN hκ)
      (fun m => ∑ r ∈ ords, t r * eigenvalue L (k + q) (κ / ((k + q : ℕ) : ℝ)) r m) 1)
    (fun m => 1 * ∑ r ∈ ords, t r * eigenvalue L (k + q) (κ / ((k + q : ℕ) : ℝ)) r m)
    (fun m => evolution_basis _ _ 1 m) _ (fun m => ((k + q : ℕ) : ℝ) * xC0 m) hT0
    (cscal L κ (μ : Measure ℝ) α h (pco ords t) d (k + q)) _ hδ1 hδ Φ hΦ1 hsuppΦ
  -- self-adjointness of the generators
  have hsaC : IsSelfAdjoint ((((k + q : ℕ) : ℝ) : ℂ) • C0op (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
        (zθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) θ'))
        (uθ κ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))))
        (gθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) B)) :=
    isSA_real_smul _ (isSA_reOp _)
  have hsaL : IsSelfAdjoint ((((k + q : ℕ) : ℝ) : ℂ) • Lop (nu 6) (fun θ' => normalizedTransfer L κ (k + q)
        (zθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) θ'))
        (uθ κ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))))
        (dθ (rectPieces (cutN L α (k + q)) h (pw d 1 (pco ords t)) (continuous_pw d 1 (pco ords t))) B)) :=
    isSA_real_smul _ (isSA_reOp _)
  have hc : ‖Complex.exp (-((cscal L κ (μ : Measure ℝ) α h (pco ords t) d (k + q) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [show -((cscal L κ (μ : Measure ℝ) α h (pco ords t) d (k + q) : ℝ) : ℂ) * Complex.I =
      ((-cscal L κ (μ : Measure ℝ) α h (pco ords t) d (k + q) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hδ4 : 0 ≤ Clin * Sp * A * δN := by positivity
  have hchain := chain k q _ _ _ (fun x => evol_isometry _ hsaC 1 x) (fun x => evol_isometry _ hsaL 1 x)
    Ψ (wvec (k + q) u) Φ hΨ hw1 hΦ1 _ hc _ _ hstep hδ4 hW
  refine hchain.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the final arithmetic
  have hwΦ : ‖wvec (k + q) u - Φ‖ ≤ 2 * Real.sqrt Pr := by rw [norm_sub_rev]; exact hΦw
  have hNinv : 1 / ((k + q : ℕ) : ℝ) ≤ δN := by
    have : 0 < (((k + q : ℕ) : ℝ)) ^ (-γ) := Real.rpow_pos_of_pos hNr _
    have : 0 < (((k + q : ℕ) : ℝ)) ^ α := Real.rpow_pos_of_pos hNr _
    have : 0 ≤ 1 / ((((k + q : ℕ) : ℝ)) ^ α) ^ b := by positivity
    rw [hδN]; linarith
  have hX0 : 0 ≤ Cp * Sp * A := by positivity
  have h1' : Cp * Sp * A / ((k + q : ℕ) : ℝ) ≤ Cp * Sp * A * δN := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hNinv hX0
  have hSpT : Sp ≤ max Tsum 0 := by
    rw [hSp, sum_abs_pco d ords hords t]
    exact (Finset.sum_le_sum ht).trans (by rw [hTsum]; exact le_max_left _ _)
  have hrate := rate_le hL hα d b hN (γ := γ)
  rw [← hA, ← hδN, ← hc₂] at hrate
  have hK0 : 0 ≤ 2 * Cp + 2 * Cs + Clin := by positivity
  have hK2 : (2 * Cp + 2 * Cs + Clin) * Sp * (A * δN) ≤ (2 * Cp + 2 * Cs + Clin) * max Tsum 0 *
      (c₂ ^ (d + 1) * ((((k + q : ℕ) : ℝ)) ^ (α * ((d : ℝ) + 1) - γ) +
        (((k + q : ℕ) : ℝ)) ^ (-(α * ((b : ℝ) - d - 1))) + (((k + q : ℕ) : ℝ)) ^ (α * ((d : ℝ) + 1) - 1))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hSpT hK0) hrate (by positivity) (by positivity)
  linarith [hwΦ, h1', hK2, mul_nonneg hX0 hδN0]

/-- **PROP-020 `Q7A:thm:main` (`eq:fullcompare`)**, for the actual model with `RootSpectralInputs` as the only open hypothesis:
for every normalized preparation `Ψ_N` with `‖Ψ_N − u^{⊗N}‖ → 0` (indexed by `N = k + q`),
`sup_{|t_r| ≤ T_r} ‖γ^{(k)}_{exp(−iΣ_r t_r Q_{N,r})Ψ_N} − γ^{(k)}_{exp(−iNΣ_r t_r L_{N,x^r})u^{⊗N}}‖₁ → 0`. -/
theorem prop020_main (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ} (hηh : eta0 L κ < h)
    (hδ : 0 < δ) (hd0 : 0 < d0) (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (d k : ℕ) (ords : Finset ℕ) (hords : ords ⊆ Finset.range (d + 1)) (T : ℕ → ℝ)
    (α γ : ℝ) (b : ℕ) (hα : 0 < α) (hα' : α < 1 / (3 * (d : ℝ) + 4))
    (hγ1 : ((d : ℝ) + 1) * α < γ) (hγ2 : γ < (1 - α) / 3) (hb : (d : ℝ) + 1 < b)
    (Ψ : (q : ℕ) → SymSector ℂ (L2T L) (k + q)) (hΨ : ∀ q, ‖Ψ q‖ = 1)
    (hconv : Tendsto (fun q => ‖Ψ q - wvec (k + q) u‖) atTop (𝓝 0)) :
    Tendsto (fun q : ℕ => ⨆ (t : ℕ → ℝ) (_ : ∀ r ∈ ords, |t r| ≤ T r),
      traceNorm (reducedDensityPower k q
          ((evolution (physBasis L hκ (k + q))
            (fun m => ∑ r ∈ ords, t r * eigenvalue L (k + q) (κ / ((k + q : ℕ) : ℝ)) r m) 1 (Ψ q) :
            SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q)) -
        reducedDensityPower k q
          ((evol ((((k + q : ℕ) : ℝ) : ℂ) • ∑ r ∈ ords, ((t r : ℝ) : ℂ) •
              Lwin L κ (μ : Measure ℝ) α h (k + q) (fun z => z ^ r) (continuous_pow r)) 1
            (wvec (k + q) u) : SymSector ℂ (L2T L) (k + q)) : HilbertTensorPower ℂ (L2T L) (k + q))))
      atTop (𝓝 0) := by
  obtain ⟨ρ, _hρ0, hprob, C, _hC0, hev⟩ := prop020_rate hκ u hu hμ hηh hδ hd0 hin d k ords hords T α γ b hα hα'
    hγ1 hγ2 hb
  have hkq : Tendsto (fun q : ℕ => k + q) atTop atTop := by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat k
  have hγ0 : 0 < γ := by
    have : 0 < ((d : ℝ) + 1) * α := by positivity
    linarith
  have hrt := (rate_tendsto (γ := γ) hα d b (by linarith) hb (by linarith)).comp hkq
  have hpr := (Real.continuous_sqrt.tendsto 0).comp (hprob.comp hkq)
  rw [Real.sqrt_zero] at hpr
  have hlim : Tendsto (fun q : ℕ => 2 * ‖Ψ q - wvec (k + q) u‖ +
      8 * Real.sqrt ((bornMeasure (physBasis L hκ (k + q)) u hu).real
        (EN (μ : Measure ℝ) (qAct L κ (k + q)) (((k + q : ℕ) : ℝ) ^ α) (cutN L α (k + q)) ρ h (eta0 L κ)
          (((k + q : ℕ) : ℝ) ^ (-γ)) b)ᶜ) +
      C * ((((k + q : ℕ) : ℝ)) ^ (α * ((d : ℝ) + 1) - γ) +
        (((k + q : ℕ) : ℝ)) ^ (-(α * ((b : ℝ) - d - 1))) +
        (((k + q : ℕ) : ℝ)) ^ (α * ((d : ℝ) + 1) - 1))) atTop (𝓝 0) := by
    have := ((hconv.const_mul 2).add (hpr.const_mul 8)).add (hrt.const_mul C)
    simp only [Function.comp_def, mul_zero, add_zero] at this
    exact this
  have hlimE := (ENNReal.tendsto_ofReal hlim)
  rw [ENNReal.ofReal_zero] at hlimE
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimE
    (Eventually.of_forall fun _ => by simp) ?_
  filter_upwards [hev] with q hq
  exact iSup₂_le fun t ht => hq (Ψ q) (hΨ q) t ht

end QuantumNLS.Prop020Main

#print axioms QuantumNLS.Prop020Main.prop020_rate
#print axioms QuantumNLS.Prop020Main.prop020_main
