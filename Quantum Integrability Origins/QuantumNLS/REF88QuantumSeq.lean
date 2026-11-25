import Mathlib
import QuantumNLS.REF88QuantumCompare
import QuantumNLS.REF88QuantumDef
import QuantumNLS.REF88QuantumBridge
import QuantumNLS.ActualGapR26
import QuantumNLS.VarStrong

/-!
# REF88QuantumSeq: the sequential limit statements of "Quantum derivatives at arbitrary finite mass"
(R-EF8C2837, item (iii), steps S1, S2, S3)

Source: `source-text/chapters/global/physical_cubic.tex` (sha256 `64ec3e02...`), printed lines 232-262 and 245-262.
For a unit `H¹` profile `v` at coupling `K` with actual-gap datum `D : Data hK v` (accepted R-C455C541 / R-C88B5D59 /
R-1E0C40B3) and every sequence of integer occupation arrays `η^n ∈ M_{n+1}` supported in a fixed finite set whose
fractions converge to `x = II hK v` in `ℓ¹`, at couplings `κ_n → K`:

* `quantile_conv` (S1, "quantile convergence for every finite-support rounding"):
  `‖stepL2 (arrRoots L (κ_n/(n+1)) η^n) - Q2 D.bd‖ → 0`.  Route: a deterministic sample `m^n` from the accepted
  `ActualGapProbabilityR26.select_sequence` and `err_probability` (occupations `→ x`, roots `→ Q`), then the printed
  tail bound, finite-root label contraction and coupling estimate, packaged in `REF88QuantumCompare.comparison`; the
  conversion `W2 ↔ ‖stepL2 - Q2‖` is the accepted `DetGapW2.norm_step_sub_Q2` / `QuantileTransport.W2_eq_qm` (`hW2`).
* `energy_conv` (S2): `N⁻¹ ∑ q_i² → qEnergy (Mu hK v)` (`‖Q2‖² = ∫ Q²`, `norm_Q2_sq`).
* `coupling_conv` (S2, printed "`K ∂_K ℰ_N = 2ℰ_N - 2L ∫ Q_N W_N → 𝒯`"): the derivative of the finite energy at
  coupling `K_n` (the accepted finite coupling identity, `REF88QuantumBridge.finiteE_hasDerivAt`, with the Gaudin
  response `(gaudin ..).inverse q`, `bop_inverse`) converges to `qT D.bd D.F / K` by the accepted
  `VarStrong.strong_response_V`.
* `gap_conv` (S3, printed "convergence to `ω_ab` on every active pair"): `Q_2(η - e_b + e_a) - Q_2(η) → D.omega a b`
  by the accepted `ActualGapTransferR26.forward` (the accepted fixed-coupling form of `VarFinal.variable_coupling`; the
  small-`n` `η_b ≥ 1` patch is `gap_conv`'s `η'`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace QuantumNLS.REF88QuantumSeq

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.F04SelBand (Mu II)
open QuantumNLS.ActualGapDataR26 (Data err)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.StepIntegrals (stepL2)
open QuantumNLS.StrongLimitBulk (Q2)
open QuantumNLS.QuantileTransport (W2 empirical qm)
open QuantumNLS.REF88QuantumDef (qEnergy qT)
open QuantumNLS.BulkResponseForm (BulkResponseData)
open QuantumNLS.QuantileForm (uI)

variable {L : ℝ} [Fact (0 < L)]

theorem exists_pmf {K : ℝ} (hK : 0 < K) (v : L2T L) (hv : ‖v‖ = 1) :
    ∃ p : PMF ℤ, ∀ k, (p k).toReal = II hK v k := by
  obtain ⟨-, hnn, hsum, htot, -⟩ := RootIndexedMasses.root_indexed_masses_proved_clauses hK v
  have h1 : HasSum (fun k => ENNReal.ofReal (II hK v k)) 1 := by
    rw [ENNReal.summable.hasSum_iff, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
    have : ∑' k, II hK v k = 1 := by
      have := htot
      rw [hv] at this
      simpa using this
    rw [this, ENNReal.ofReal_one]
  exact ⟨⟨_, h1⟩, fun k => ENNReal.toReal_ofReal (hnn k)⟩

/-- A deterministic sample whose occupations and root quantiles converge (accepted R-1E0C40B3 ingredients). -/
theorem exists_sample {K : ℝ} (hK : 0 < K) (v : L2T L) (hv : ‖v‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 v) (D : Data hK v) :
    ∃ m : ∀ n : ℕ, MArr (n + 1),
      Tendsto (fun n : ℕ => RootOccupationLimit.occDist hK v (n + 1) (m n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ‖stepL2 (arrRoots L (K / ((n + 1 : ℕ) : ℝ)) (m n)) - Q2 D.bd‖)
        atTop (𝓝 0) := by
  obtain ⟨m, hm⟩ := ActualGapProbabilityR26.select_sequence
    (fun n => RootEnergyMomentLaws.law hK v hv (n + 1)) (fun n => err D (n + 1))
    (fun _ m => ActualGapDataR26.err_nonneg D _ m)
    (ActualGapDataR26.err_probability hK v hv hH D)
  exact ⟨m, ActualGapDataR26.err_limits D m hm⟩

theorem patch_pos {K : ℝ} (hK : 0 < K) (κs : ℕ → ℝ) (hκs : Tendsto κs atTop (𝓝 K))
    (hpos : ∀ᶠ n in atTop, 0 < κs n) :
    ∃ κs' : ℕ → ℝ, (∀ n, 0 < κs' n) ∧ Tendsto κs' atTop (𝓝 K) ∧ ∀ᶠ n in atTop, κs' n = κs n := by
  classical
  refine ⟨fun n => if 0 < κs n then κs n else K, fun n => ?_, ?_, ?_⟩
  · dsimp only; split_ifs with h
    · exact h
    · exact hK
  · refine hκs.congr' ?_
    filter_upwards [hpos] with n hn
    simp [hn]
  · filter_upwards [hpos] with n hn
    simp [hn]

/-- **S1: quantile convergence for every finite-support rounding.** -/
theorem quantile_conv {K : ℝ} (hK : 0 < K) (v : L2T L) (hv : ‖v‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 v) (D : Data hK v)
    (η : ∀ n : ℕ, MArr (n + 1)) (F : Finset ℤ) (hF : ∀ n k, k ∉ F → (η n).1 k = 0)
    (hη : Tendsto (fun n : ℕ => ∑' k : ℤ, |(((η n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - II hK v k|)
      atTop (𝓝 0))
    (κs : ℕ → ℝ) (hκs : Tendsto κs atTop (𝓝 K)) (hpos : ∀ᶠ n in atTop, 0 < κs n) :
    Tendsto (fun n : ℕ => ‖stepL2 (arrRoots L (κs n / ((n + 1 : ℕ) : ℝ)) (η n)) - Q2 D.bd‖)
      atTop (𝓝 0) := by
  obtain ⟨κs', hpos', hκs', hev⟩ := patch_pos hK κs hκs hpos
  have hL : 0 < L := Fact.out
  obtain ⟨p, hp⟩ := exists_pmf hK v hv
  obtain ⟨m, hoc, hq⟩ := exists_sample hK v hv hH D
  have hm1 : Tendsto (fun n : ℕ => ∑' k : ℤ, |(((m n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - (p k).toReal|)
      atTop (𝓝 0) := by
    refine hoc.congr fun n => ?_
    unfold RootOccupationLimit.occDist RootOccupationLimit.occVec
    refine tsum_congr fun k => ?_
    rw [hp k]
    simp only [Nat.cast_add, Nat.cast_one]
  have hm2 := ActualGapDataR26.wasserstein D m hq
  haveI := F04SelBand.Mu_prob hK v hv
  have hρ : QuantileTransport.HasFiniteSecondMoment (Mu hK v) :=
    BulkResponseRiesz.hasFiniteSecondMoment_of_moment D.bulk.finiteSecondMoment
  have hη' : Tendsto (fun n : ℕ => ∑' k : ℤ, |(((η n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - (p k).toReal|)
      atTop (𝓝 0) := by
    refine hη.congr fun n => ?_
    refine tsum_congr fun k => ?_
    rw [hp k]
  have hW := REF88QuantumCompare.comparison hL hK (Mu hK v) hρ p m hm1 hm2 η F hF hη' κs' hκs' hpos'
  have hnorm : ∀ n : ℕ, ‖stepL2 (arrRoots L (κs' n / ((n + 1 : ℕ) : ℝ)) (η n)) - Q2 D.bd‖ =
      (W2 (empirical (n + 1) (arrRoots L (κs' n / ((n : ℝ) + 1)) (η n))) (Mu hK v)).toReal := by
    intro n
    have hc : 0 < κs' n / ((n + 1 : ℕ) : ℝ) := div_pos (hpos' n) (by positivity)
    have hmono := REF88QuantumLabels.arrRoots_mono hL hc (η n)
    have := DetGapW2.norm_step_sub_Q2 D.bd (Nat.succ_pos n) hmono
    rw [this]
    simp only [Nat.cast_add, Nat.cast_one]
    rfl
  have h1 : Tendsto (fun n : ℕ => ‖stepL2 (arrRoots L (κs' n / ((n + 1 : ℕ) : ℝ)) (η n)) - Q2 D.bd‖)
      atTop (𝓝 0) := by
    simp_rw [hnorm]
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  refine h1.congr' ?_
  filter_upwards [hev] with n hn
  rw [hn]

theorem norm_Q2_sq (D : BulkResponseData) : ‖Q2 D‖ ^ 2 = qEnergy D.μ := by
  haveI := D.hμ.isProbability
  have hfin := BulkResponseRiesz.hasFiniteSecondMoment_of_moment D.hμ.finiteSecondMoment
  have h1 := BulkResponseRiesz.ofReal_norm_sq' (Q2 D)
  have h2 : ∫⁻ x, ENNReal.ofReal ((Q2 D : ℝ → ℝ) x ^ 2) ∂uI = ∫⁻ x, ENNReal.ofReal (qm D.μ x ^ 2) ∂uI :=
    lintegral_congr_ae (by
      filter_upwards [MemLp.coeFn_toLp (StrongLimitBulk.memLp_qm_bulk D)] with x hx
      have hx' : (Q2 D : ℝ → ℝ) x = qm D.μ x := hx
      rw [hx'])
  have hi : Integrable (fun x => qm D.μ x ^ 2) uI := QuantileTransport.integrable_qm_sq D.μ hfin
  have h3 : ∫⁻ x, ENNReal.ofReal (qm D.μ x ^ 2) ∂uI = ENNReal.ofReal (∫ x, qm D.μ x ^ 2 ∂uI) :=
    (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => sq_nonneg _)).symm
  rw [h2, h3] at h1
  have hnn : 0 ≤ ∫ x, qm D.μ x ^ 2 ∂uI := integral_nonneg fun x => sq_nonneg _
  exact (ENNReal.ofReal_eq_ofReal_iff (sq_nonneg _) hnn).1 h1

theorem tendsto_stepL2 {K : ℝ} (hK : 0 < K) (v : L2T L) (hv : ‖v‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 v) (D : Data hK v)
    (η : ∀ n : ℕ, MArr (n + 1)) (F : Finset ℤ) (hF : ∀ n k, k ∉ F → (η n).1 k = 0)
    (hη : Tendsto (fun n : ℕ => ∑' k : ℤ, |(((η n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - II hK v k|)
      atTop (𝓝 0))
    (κs : ℕ → ℝ) (hκs : Tendsto κs atTop (𝓝 K)) (hpos : ∀ᶠ n in atTop, 0 < κs n) :
    Tendsto (fun n : ℕ => stepL2 (arrRoots L (κs n / ((n + 1 : ℕ) : ℝ)) (η n))) atTop (𝓝 (Q2 D.bd)) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (quantile_conv hK v hv hH D η F hF hη κs hκs hpos)

/-- **S2 (energy).** `N⁻¹ ∑ q_i² → qEnergy (Mu hK v)`. -/
theorem energy_conv {K : ℝ} (hK : 0 < K) (v : L2T L) (hv : ‖v‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 v) (D : Data hK v)
    (η : ∀ n : ℕ, MArr (n + 1)) (F : Finset ℤ) (hF : ∀ n k, k ∉ F → (η n).1 k = 0)
    (hη : Tendsto (fun n : ℕ => ∑' k : ℤ, |(((η n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - II hK v k|)
      atTop (𝓝 0))
    (κs : ℕ → ℝ) (hκs : Tendsto κs atTop (𝓝 K)) (hpos : ∀ᶠ n in atTop, 0 < κs n) :
    Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹ *
      ∑ i, arrRoots L (κs n / ((n + 1 : ℕ) : ℝ)) (η n) i ^ 2) atTop (𝓝 (qEnergy (Mu hK v))) := by
  have h := (tendsto_stepL2 hK v hv hH D η F hF hη κs hκs hpos).norm.pow 2
  rw [norm_Q2_sq] at h
  refine h.congr fun n => ?_
  rw [StepIntegrals.norm_sq_step (Nat.succ_pos n)]
  unfold FiniteResponse.L2N
  rw [one_div]

theorem bop_inverse {N : ℕ} {c : ℝ} (hL : 0 < L) (hc : 0 < c) (q : Fin N → ℝ) :
    FiniteResponse.Bop L c q ((BetheRoots.gaudin L c q).inverse q) = q := by
  rw [VarStrong.bop_eq_gaudin']
  have h := (BetheSmooth.gaudin_isInvertible hL hc q).self_apply_inverse q
  unfold GaudinResponse.gaudinMatrix
  rw [← RootDisplacement.gaudin_eq_Bmat]
  exact h

/-- **S2 (response; printed `K ∂_K ℰ_N = 2ℰ_N - 2L ∫ Q_N W_N → 𝒯`).**  The derivative of the finite energy at
coupling `κ_n`, from the accepted finite coupling identity, converges to `qT D.bd D.F / K`. -/
theorem coupling_conv {K : ℝ} (hK : 0 < K) (v : L2T L) (hv : ‖v‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 v) (D : Data hK v)
    (η : ∀ n : ℕ, MArr (n + 1)) (F : Finset ℤ) (hF : ∀ n k, k ∉ F → (η n).1 k = 0)
    (hη : Tendsto (fun n : ℕ => ∑' k : ℤ, |(((η n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - II hK v k|)
      atTop (𝓝 0))
    (κs : ℕ → ℝ) (hκs : Tendsto κs atTop (𝓝 K)) (hpos : ∀ᶠ n in atTop, 0 < κs n) :
    Tendsto (fun n : ℕ => (κs n)⁻¹ *
      (2 * ((((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, arrRoots L (κs n / ((n + 1 : ℕ) : ℝ)) (η n) i ^ 2) -
        2 * L * ((((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, arrRoots L (κs n / ((n + 1 : ℕ) : ℝ)) (η n) i *
          (BetheRoots.gaudin L (κs n / ((n + 1 : ℕ) : ℝ)) (arrRoots L (κs n / ((n + 1 : ℕ) : ℝ)) (η n))).inverse
            (arrRoots L (κs n / ((n + 1 : ℕ) : ℝ)) (η n)) i)))
      atTop (𝓝 (qT D.bd D.F / K)) := by
  obtain ⟨κs', hpos', hκs', hev⟩ := patch_pos hK κs hκs hpos
  have hL : 0 < L := Fact.out
  set q : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => arrRoots L (κs' n / ((n + 1 : ℕ) : ℝ)) (η n) with hq
  set Fv : ∀ n : ℕ, Fin (n + 1) → ℝ := fun n => (BetheRoots.gaudin L (κs' n / ((n + 1 : ℕ) : ℝ)) (q n)).inverse (q n)
    with hFv
  have hQc : Tendsto (fun n : ℕ => ‖stepL2 (q n) - Q2 D.bd‖) atTop (𝓝 0) :=
    quantile_conv hK v hv hH D η F hF hη κs' hκs' (Eventually.of_forall hpos')
  have hres := VarStrong.strong_response_V D.bd D.response (κs := κs') hκs' hpos' q Fv
    (fun n => bop_inverse hL (div_pos (hpos' n) (by positivity)) (q n)) hQc
  have hE := energy_conv hK v hv hH D η F hF hη κs' hκs' (Eventually.of_forall hpos')
  have hS : Tendsto (fun n : ℕ => stepL2 (q n)) atTop (𝓝 (Q2 D.bd)) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hQc
  have hF2 : Tendsto (fun n : ℕ => stepL2 (Fv n)) atTop (𝓝 D.F) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hres
  have hin := Filter.Tendsto.inner (𝕜 := ℝ) hS hF2
  have hin' : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, q n i * Fv n i) atTop
      (𝓝 (∫ t, qm (Mu hK v) t * (D.F : ℝ → ℝ) t ∂uI)) := by
    have e : inner ℝ (Q2 D.bd) D.F = ∫ t, qm (Mu hK v) t * (D.F : ℝ → ℝ) t ∂uI := by
      rw [BulkResponseRiesz.inner_eq_integral]
      refine integral_congr_ae ?_
      filter_upwards [MemLp.coeFn_toLp (StrongLimitBulk.memLp_qm_bulk D.bd)] with t ht
      have ht' : (Q2 D.bd : ℝ → ℝ) t = qm D.bd.μ t := ht
      exact congrArg (· * (D.F : ℝ → ℝ) t) ht'
    rw [← e]
    refine hin.congr fun n => ?_
    rw [StepIntegrals.inner_step (Nat.succ_pos n)]
    unfold FiniteResponse.ipN FiniteResponse.dot
    rw [one_div]
  have hmain : Tendsto (fun n : ℕ => (κs' n)⁻¹ *
      (2 * ((((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, q n i ^ 2) -
        2 * L * ((((n + 1 : ℕ) : ℝ))⁻¹ * ∑ i, q n i * Fv n i))) atTop
      (𝓝 (K⁻¹ * (2 * qEnergy (Mu hK v) - 2 * L * ∫ t, qm (Mu hK v) t * (D.F : ℝ → ℝ) t ∂uI))) :=
    (hκs'.inv₀ hK.ne').mul ((hE.const_mul 2).sub (hin'.const_mul (2 * L)))
  have hval : K⁻¹ * (2 * qEnergy (Mu hK v) - 2 * L * ∫ t, qm (Mu hK v) t * (D.F : ℝ → ℝ) t ∂uI) =
      qT D.bd D.F / K := by
    unfold qT
    rw [div_eq_inv_mul]
    rfl
  rw [hval] at hmain
  refine hmain.congr' ?_
  filter_upwards [hev] with n hn
  simp only [hq, hFv, hn]

/-- The (total) gap sum `Q_2(η - e_b + e_a) - Q_2(η)` (`0` if `η_b = 0`). -/
def gapSum (L c : ℝ) {N : ℕ} (a b : ℤ) (m : MArr N) : ℝ :=
  if h : 1 ≤ m.1 b then F02Tightness.Q2 L c (AdjacentResponse.transfer m h a) - F02Tightness.Q2 L c m else 0

/-- **S3 (adjacent gap).**  For an active pair `b < a` and any finite-support rounding with `η_b ≥ 1` eventually,
`Q_2(η - e_b + e_a) - Q_2(η) → D.omega a b` at fixed coupling `K`. -/
theorem gap_conv {K : ℝ} (hK : 0 < K) (v : L2T L) (hv : ‖v‖ = 1)
    (hH : ProductEnergyPreparation.OneH1 v) (D : Data hK v) {a b : ℤ} (hab : b < a)
    (hb : 0 < II hK v b) (ha : 0 < II hK v a)
    (η : ∀ n : ℕ, MArr (n + 1)) (F : Finset ℤ) (hF : ∀ n k, k ∉ F → (η n).1 k = 0)
    (hη : Tendsto (fun n : ℕ => ∑' k : ℤ, |(((η n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - II hK v k|)
      atTop (𝓝 0))
    (hηb : ∀ᶠ n in atTop, 1 ≤ (η n).1 b) :
    Tendsto (fun n : ℕ => gapSum L (K / ((n + 1 : ℕ) : ℝ)) a b (η n)) atTop (𝓝 (D.omega a b)) := by
  classical
  set η' : ∀ n : ℕ, MArr (n + 1) := fun n =>
    if 1 ≤ (η n).1 b then η n else ActualGapDataR26.singleArr (n + 1) b with hη'
  have hev : ∀ᶠ n : ℕ in atTop, η' n = η n := hηb.mono fun n hn => by simp [hη', hn]
  have hmb : ∀ n, 1 ≤ (η' n).1 b := by
    intro n
    by_cases h : 1 ≤ (η n).1 b
    · simp [hη', h]
    · simp [hη', h, ActualGapDataR26.singleArr]
  have hF' : ∀ n k, k ∉ insert b F → (η' n).1 k = 0 := by
    intro n k hk
    simp only [Finset.mem_insert, not_or] at hk
    by_cases h : 1 ≤ (η n).1 b
    · have e : η' n = η n := by simp [hη', h]
      rw [e]; exact hF n k hk.2
    · have e : η' n = ActualGapDataR26.singleArr (n + 1) b := by simp [hη', h]
      have hne : b ≠ k := Ne.symm hk.1
      rw [e]
      simp [ActualGapDataR26.singleArr, Finsupp.single_apply, hne]
  have hη2 : Tendsto (fun n : ℕ => ∑' k : ℤ, |(((η' n).1 k : ℕ) : ℝ) / ((n : ℝ) + 1) - II hK v k|)
      atTop (𝓝 0) := hη.congr' (hev.mono fun n hn => by simp only [hn])
  have hq := quantile_conv hK v hv hH D η' (insert b F) hF' hη2 (fun _ => K) tendsto_const_nhds
    (Eventually.of_forall fun _ => hK)
  have hoc : Tendsto (fun n : ℕ => RootOccupationLimit.occDist hK v (n + 1) (η' n)) atTop (𝓝 0) := by
    refine hη2.congr fun n => ?_
    unfold RootOccupationLimit.occDist RootOccupationLimit.occVec
    refine tsum_congr fun k => ?_
    simp only [Nat.cast_add, Nat.cast_one]
  obtain ⟨-, hf⟩ := ActualGapTransferR26.forward hK v hv D hab hb ha η' hmb hoc hq
  have key : ∀ (c : ℝ) {N : ℕ} (m m' : MArr N) (e : m = m') (h : 1 ≤ m.1 b) (h' : 1 ≤ m'.1 b),
      F02Tightness.Q2 L c (AdjacentResponse.transfer m h a) - F02Tightness.Q2 L c m =
      F02Tightness.Q2 L c (AdjacentResponse.transfer m' h' a) - F02Tightness.Q2 L c m' := by
    intro c N m m' e h h'; subst e; rfl
  refine hf.congr' ?_
  filter_upwards [hev, hηb] with n hn h1
  rw [gapSum, dif_pos h1]
  exact key _ (η' n) (η n) hn _ _

end QuantumNLS.REF88QuantumSeq

#print axioms QuantumNLS.REF88QuantumSeq.exists_pmf
#print axioms QuantumNLS.REF88QuantumSeq.quantile_conv
#print axioms QuantumNLS.REF88QuantumSeq.norm_Q2_sq
#print axioms QuantumNLS.REF88QuantumSeq.energy_conv
#print axioms QuantumNLS.REF88QuantumSeq.bop_inverse
#print axioms QuantumNLS.REF88QuantumSeq.coupling_conv
#print axioms QuantumNLS.REF88QuantumSeq.gap_conv
