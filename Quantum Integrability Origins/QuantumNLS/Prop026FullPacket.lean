import QuantumNLS.Prop019Discharge
import QuantumNLS.Prop018SequenceBundle

/-! Uniform PROP-019 packet input, pointwise-data form (copy of `Prop019FullPacket.uniform_packet` with the background data exported instead of a packaged `BgFam`).
This is a NEW module; `Prop019FullPacket` is imported read-only. Uniform PROP-019 packet input. No convergence or power-law tolerance hypothesis.
The packet is exactly RootEvent.EN from PROP-017. RootSpectralInputs stays explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory Filter Topology Set Complex
open scoped InnerProductSpace ComplexConjugate
namespace QuantumNLS.Prop026FullPacket
open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.RootEvent (EN)
open QuantumNLS.ResolventNeighborhood (NbhdN rNbhd nbhd_dist norm_Gfull_le Gfull_hasDerivAt_of_dist)
open QuantumNLS.Prop017Quantum (qAct eta0)
open QuantumNLS.Prop017Physical (RootSpectralInputs prop017_physical)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.Prop017MovingContour (nbhd_mono Df_eq_Dsrc)
open QuantumNLS.Prop018Scalar (norm_sf_le A_eq_half)
open QuantumNLS.Prop018Phase (sNsrc_eq sLimsrc_eq)
open QuantumNLS.MPFamily (BgFam)
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis)
variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- Uniform constants and threshold, before quantification over epsilon, N, radius and cut; the background data on the
`ρ/8`-neighbourhood are exported pointwise (differentiability of `G`, bounds of `A, A⁻¹, e, D, G`), so that a background on the union with fixed
contours can be built. -/
theorem uniform_packet_data (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {μ : ProbabilityMeasure ℝ}
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) {h δ d0 : ℝ} {l0 : ℕ}
    (hηh : eta0 L κ < h) (hδ : 0 < δ) (hd0 : 0 < d0)
    (hin : RootSpectralInputs L κ (μ : Measure ℝ) h δ d0 l0)
    (b pc : ℕ) (hb : 1 ≤ b) (hbpc : b ≤ 2 * pc) :
    ∃ ρ R0 η M r Kd : ℝ, 0 < ρ ∧ 2 * ρ < h ∧ 1 ≤ R0 ∧ 0 < η ∧ 1 ≤ M ∧ 0 < r ∧ 0 ≤ Kd ∧
      ∃ N0 : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ N : ℕ, N0 ≤ N → ∀ hN : 1 ≤ N,
      ∀ R : ℝ, R0 ≤ R → ∀ l : ℕ, l0 ≤ l → ∀ a : ℝ,
      a = QuantumNLS.PROP017UniformN.cutSeq L l → 2 * R ≤ a →
      (∀ z ∈ NbhdN a h (ρ / 8), DifferentiableAt ℂ (Gfull (μ : Measure ℝ)) z ∧
        η ≤ ‖Df L κ (Gfull (μ : Measure ℝ)) z‖ ∧ ‖Af κ (Gfull (μ : Measure ℝ)) z‖ ≤ M ∧
        ‖(Af κ (Gfull (μ : Measure ℝ)) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M ∧ ‖Gfull (μ : Measure ℝ) z‖ ≤ 1 / r) ∧
        ∀ φ : QuantumNLS.PhysicalTensor.physSector L N,
          (∀ m ∉ EN (μ : Measure ℝ) (qAct L κ N) R a ρ h (eta0 L κ) ε b,
            ⟪meanField_physicalBasis L N hN hκ m, φ⟫_ℂ = 0) →
          ∀ z ∈ NbhdN a h (ρ / 8),
          ‖(normalizedTransfer L κ N z - sf L κ (Gfull (μ : Measure ℝ)) z •
            (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) φ‖ ≤
            Kd * (ε + 1 / R ^ b + 1 / (N : ℝ)) * ‖φ‖ := by
  have hL : 0 < L := Fact.out
  obtain ⟨ρ, hρ, R0, hR01, r, hr, hrad, N0, hfam⟩ :=
    prop017_physical hκ u hu hμ hηh hδ hd0 hin b pc hb hbpc
  have h2ρ : 2 * ρ < h := by
    have h1 := hrad R0 le_rfl (2 * R0) le_rfl
    have h2 : rNbhd (2 * R0) h ρ R0 δ ≤ h - 2 * ρ := min_le_left _ _
    linarith
  let M := max 1 (max (Real.exp (κ / r)) (Real.exp (L * (h + 2 * ρ))))
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM : 0 < M := by linarith
  let Kd := Real.exp (|κ| / r) * (1 + Real.exp (|L| * (h + 2 * ρ))) *
    max (κ ^ 2 / r ^ 2) (|κ| * (2 * QuantumNLS.ResolventNeighborhood.KGN (eta0 L κ) δ ρ
      (h + 5) QuantumNLS.RootMeasureConcentrationSharp.Csharp b pc (μ : Measure ℝ)))
  refine ⟨ρ, R0, d0 / 2, M, r, max Kd 0, hρ, h2ρ, hR01, by positivity,
    hM1, hr, le_max_right _ _, N0, ?_⟩
  intro ε hε hε1 N hN0 hN R hR l hl a ha h2R
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one (hR01.trans hR)
  have hap : 0 < a := by linarith
  obtain ⟨-, hev, hD⟩ := hfam ε hε hε1 N hN0 hN R hR l hl a ha h2R
  have hgap := hin.gap l hl
  rw [← ha] at hgap
  have hdist : ∀ z ∈ NbhdN a h (ρ / 8),
      (∀ᵐ (x : ℝ) ∂(μ : Measure ℝ), r ≤ ‖z - (x : ℂ)‖) ∧ |z.im| ≤ h + 2 * ρ := by
    intro z hz
    have hd := nbhd_dist (fun _ : Fin 0 => (0 : ℝ)) (μ : Measure ℝ) (R := R) hap hρ
      (by linarith : 0 < h - 2 * ρ) (hgap.mono fun x hx => hx.1)
      (hgap.mono fun x hx => hx.2) (nbhd_mono (by linarith) hz)
    exact ⟨hd.1.mono fun x hx => (hrad R hR a h2R).trans hx, hd.2.2⟩
  have hGd := fun z hz => (Gfull_hasDerivAt_of_dist (μ : Measure ℝ) hr (hdist z hz).1).differentiableAt
  have hGc := fun z hz => (hGd z hz).continuousAt
  have hAc := fun z hz => ((hGc z hz).const_mul (I * κ)).cexp
  have hec := fun z => (hasDerivAt_ef L z).continuousAt
  have hGle := fun z hz => norm_Gfull_le (μ : Measure ℝ) z hr (hdist z hz).1
  have hMb : ∀ z ∈ NbhdN a h (ρ / 8),
      ‖Af κ (Gfull (μ : Measure ℝ)) z‖ ≤ M ∧
      ‖(Af κ (Gfull (μ : Measure ℝ)) z)⁻¹‖ ≤ M ∧ ‖ef L z‖ ≤ M := by
    intro z hz
    have hx : ‖I * (κ : ℂ) * Gfull (μ : Measure ℝ) z‖ ≤ κ / r := by
      rw [norm_mul, norm_mul, norm_I, one_mul, norm_real, Real.norm_of_nonneg hκ.le]
      calc κ * ‖Gfull (μ : Measure ℝ) z‖ ≤ κ * (1 / r) := mul_le_mul_of_nonneg_left (hGle z hz) hκ.le
           _ = κ / r := by ring
    have hM2 : Real.exp (κ / r) ≤ M := (le_max_left _ _).trans (le_max_right _ _)
    have hM3 : Real.exp (L * (h + 2 * ρ)) ≤ M := (le_max_right _ _).trans (le_max_right _ _)
    refine ⟨(Complex.norm_exp_le_exp_norm _).trans ((Real.exp_le_exp.2 hx).trans hM2), ?_, ?_⟩
    · rw [Af, ← Complex.exp_neg]
      exact (Complex.norm_exp_le_exp_norm _).trans ((Real.exp_le_exp.2 (by simpa using hx)).trans hM2)
    · rw [QuantumNLS.HaarSummableReconstruction.norm_ef_eq]
      refine (Real.exp_le_exp.2 ?_).trans hM3
      have := neg_abs_le z.im
      nlinarith [mul_le_mul_of_nonneg_left (hdist z hz).2 hL.le]
  have hAlow : ∀ z ∈ NbhdN a h (ρ / 8), 1 / M ≤ ‖Af κ (Gfull (μ : Measure ℝ)) z‖ := by
    intro z hz
    have hi := (hMb z hz).2.1
    rw [norm_inv] at hi
    have hn : 0 < ‖Af κ (Gfull (μ : Measure ℝ)) z‖ := norm_pos_iff.2 (exp_ne_zero _)
    exact (one_div_le hM hn).2 (by rw [one_div]; exact hi)
  refine ⟨fun z hz => ⟨hGd z hz, ?_, (hMb z hz).1, (hMb z hz).2.1, (hMb z hz).2.2, hGle z hz⟩, ?_⟩
  · rw [Df_eq_Dsrc]; exact hD z (nbhd_mono (by linarith) hz)
  intro φ hsupp z hz
  have herr0 : 0 ≤ ε + 1 / R ^ b + 1 / (N : ℝ) := by positivity
  refine QuantumNLS.Prop019Deviation.transfer_deviation hκ hN _ z _
    (mul_nonneg (le_max_right _ _) herr0) ?_ ?_ φ hsupp
  · intro m hm j heq
    have hd := nbhd_dist (qAct L κ N m) (μ : Measure ℝ) (R := R) hap hρ (by linarith)
      (hgap.mono fun x hx => hx.1) (hgap.mono fun x hx => hx.2) (nbhd_mono (by linarith) hz)
    have hj := (hrad R hR a h2R).trans (hd.2.1 j ((hev m hm).1 j))
    rw [heq, sub_self, norm_zero] at hj
    linarith
  · intro m hm
    have h0 := (hev m hm).2.2 z (nbhd_mono (by linarith) hz) 0
    rw [sNsrc_eq, sLimsrc_eq] at h0
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul] at h0
    exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left Kd 0) herr0)

end QuantumNLS.Prop026FullPacket
#print axioms QuantumNLS.Prop026FullPacket.uniform_packet_data
