import QuantumNLS.Prop018Phase

/-!
# PROP-019 (`Q7A:lem:linearization`), input 1: the spectral deviation of the transfer quadratures on `ran P_N`

Source: `window_reconstruction.tex`, proof of `Q7A:lem:linearization`: "The real and imaginary parts of `S_N(z)` are commuting
self-adjoint coordinates with one common bounded spectral range. Their deviation from the corresponding background coordinates
on `P_N` is at most `Δ = C_b(ε+R^{−b}+N^{−1})`."

* `eigen_eq_sNf`: away from the roots, the eigenvalue of the actual normalized transfer `S_N(z)` on `Ψ_{N,m}` is
  `s_N(z; q(m)) = ∏(1 + ic/(z−q_j)) + e^{iLz}∏(1 − ic/(z−q_j))`, `c = κ/N`, `q = arrRoots` (generalizes
  `RootMeasureTransfer.eigen_eq_sProd`, which needs `Im z > 0`, to every non-root `z`, in particular to all of `Γ_N`);
* `transfer_deviation`: for `φ` supported on a label set `S` (i.e. `φ ∈ ran P^S`) with `|s_N(z;q(m)) − s| ≤ δ` for `m ∈ S`,
  `‖(S_N(z) − s)φ‖ ≤ δ‖φ‖` (spectral variance in the Bethe basis);
* **`deviation_of_bundle`**: on the PROP-018 bundle event (same `ρ`, same `𝓔_N`), eventually in `N`, for every `φ ∈ ran P_N` and
  every `z` in the `ρ/8`-neighbourhood of `Γ_N`: `‖(S_N(z) − s(z))φ‖ ≤ K_d'(ε_N + R_N^{−b} + N^{−1})‖φ‖`.
  This is exactly the deviation hypothesis `hsδ` of `MixedQuadratures.prop026_traceNorm_physical` (and of the
  PROP-026 actual-contour theorem) on the window contour, with `δ = Δ_N`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology Complex Set
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.Prop019Deviation

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.BetheLabels (MArr arrRoots)
open QuantumNLS.Extrapolation (Gfull GN)
open QuantumNLS.ResolventNeighborhood (NbhdN sNsrc sLimsrc)
open QuantumNLS.PROP018Probability (cutN)
open QuantumNLS.Prop017Quantum (qAct)
open QuantumNLS.PeriodReconstructionCore
open QuantumNLS.NormalizedTransfer (normalizedTransfer)
open QuantumNLS.UnconditionalBetheBasis (meanField_physicalBasis transfer_physicalBasis)
open QuantumNLS.Prop018Phase (sNsrc_eq sLimsrc_eq)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-- Away from the roots, the actual transfer eigenvalue is `s_N(z; q(m))`. -/
theorem eigen_eq_sNf (hκ : 0 < κ) {N : ℕ} (hN : 0 < N) (m : MArr N) (z : ℂ)
    (hz : ∀ j, z ≠ (qAct L κ N m j : ℂ)) :
    QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m z = sNf L (κ / N) (qAct L κ N m) z := by
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (Nat.cast_pos.2 hN)
  have hL : 0 < L := Fact.out
  have hroot : ∀ i, QuantumNLS.BetheSmooth.sourceRoots L (QuantumNLS.NormalityBridge.label m).1 (κ / N) i =
      arrRoots L (κ / N) m (Fin.rev i) := fun i => by
    rw [QuantumNLS.RootMeasureTransfer.label_val]
    exact QuantumNLS.BetheLabels.sourceRoots_eq_roots_rev hL hc _ i
  unfold QuantumNLS.NormalityBridge.eigen
  rw [QuantumNLS.BetheSpectralContinuity.spectralValue_nonpole L hc (QuantumNLS.NormalityBridge.label m).2 z
    (fun k hk => hz (Fin.rev k) (by rw [hk, hroot k]))]
  unfold QuantumNLS.TransferSeparation.sFun
  simp only [hroot]
  have p1 := Equiv.prod_comp Fin.revPerm
    (fun j => 1 + Complex.I * ((κ / N : ℝ) : ℂ) / (z - (arrRoots L (κ / N) m j : ℂ)))
  have p2 := Equiv.prod_comp Fin.revPerm
    (fun j => 1 - Complex.I * ((κ / N : ℝ) : ℂ) / (z - (arrRoots L (κ / N) m j : ℂ)))
  simp only [Fin.revPerm_apply] at p1 p2
  rw [p1, p2]
  simp only [sNf, ANf, ef, QuantumNLS.Prop017Quantum.qAct]
  push_cast
  ring_nf

/-- **Spectral deviation on `ran P^S`**: if `φ` has no Bethe component outside `S` and `|s_N(z;q(m)) − s| ≤ δ` on `S`, then
`‖(S_N(z) − s)φ‖ ≤ δ‖φ‖`. -/
theorem transfer_deviation (hκ : 0 < κ) {N : ℕ} (hN : 1 ≤ N) (S : Set (MArr N)) (z s : ℂ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hS : ∀ m ∈ S, ∀ j, z ≠ (qAct L κ N m j : ℂ))
    (hδ : ∀ m ∈ S, ‖sNf L (κ / N) (qAct L κ N m) z - s‖ ≤ δ)
    (φ : QuantumNLS.PhysicalTensor.physSector L N)
    (hφ : ∀ m ∉ S, ⟪meanField_physicalBasis L N hN hκ m, φ⟫_ℂ = 0) :
    ‖(normalizedTransfer L κ N z - s • (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) φ‖ ≤ δ * ‖φ‖ := by
  classical
  set b := meanField_physicalBasis L N hN hκ with hb
  have h1 := QuantumNLS.RootMeasureTransfer.hasSum_norm_sq_diag b (normalizedTransfer L κ N z)
    (fun m => QuantumNLS.NormalityBridge.eigen (L := L) κ hκ hN m z)
    (fun m => transfer_physicalBasis hκ hN z m) s φ
  have h2 := (QuantumNLS.RootMeasureTransfer.hasSum_norm_sq b φ).mul_right (δ ^ 2)
  have hle := hasSum_le (fun m => ?_) h1 h2
  · have hsq : ‖(normalizedTransfer L κ N z - s • (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) φ‖ ^ 2 ≤ (δ * ‖φ‖) ^ 2 := by
      rw [mul_pow]; linarith [hle]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 hsq
  · by_cases hm : m ∈ S
    · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [eigen_eq_sNf hκ hN m z (hS m hm)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hδ m hm) 2
    · rw [hφ m hm, norm_zero]
      simp

/-- **The deviation on the PROP-018 bundle event**: eventually in `N`, for every `φ ∈ ran P_N` (no Bethe component outside
`E N`) and every `z` in the `ρ/8`-neighbourhood of `Γ_N`,
`‖(S_N(z) − s(z))φ‖ ≤ max K_d 0 · (N^{−γ} + N^{−θb} + N^{−1}) ‖φ‖`. The hypothesis on `E` is the part of the
`Prop018Bundle.moving_contour_bundle` conclusion that is used (root distance and `eq:derivative` at order `0`). -/
theorem deviation_of_bundle (hκ : 0 < κ) (μ : Measure ℝ) {h ρ Kd θ γ : ℝ} {b : ℕ}
    (E : (N : ℕ) → Set (MArr N))
    (hev : ∀ᶠ N : ℕ in atTop, ∀ m ∈ E N, ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8),
      (∀ j, 2 * |κ / (N : ℝ)| < ‖z - (qAct L κ N m j : ℂ)‖) ∧
      ‖iteratedDeriv 0 (fun w => sNsrc κ L (qAct L κ N m) w - sLimsrc κ L μ w) z‖ ≤
        (Nat.factorial 0) * (Kd * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) / (ρ / 2) ^ 0) :
    ∀ᶠ N : ℕ in atTop, ∀ (hN : 1 ≤ N) (φ : QuantumNLS.PhysicalTensor.physSector L N),
      (∀ m ∉ E N, ⟪meanField_physicalBasis L N hN hκ m, φ⟫_ℂ = 0) →
      ∀ z ∈ NbhdN (cutN L θ N) h (ρ / 8),
        ‖(normalizedTransfer L κ N z - sf L κ (Gfull μ) z • (1 : QuantumNLS.KernelDefinition.BoundedSymmetricKernel (L2T L) N)) φ‖ ≤
          (max Kd 0 * ((N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ))) * ‖φ‖ := by
  filter_upwards [hev, eventually_ge_atTop 1] with N hevN hN1
  intro hN φ hφ z hz
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδN0 : 0 ≤ (N : ℝ) ^ (-γ) + 1 / ((N : ℝ) ^ θ) ^ b + 1 / (N : ℝ) := by
    have : 0 < (N : ℝ) ^ θ := Real.rpow_pos_of_pos hNr θ
    have : 0 < (N : ℝ) ^ (-γ) := Real.rpow_pos_of_pos hNr _
    positivity
  refine transfer_deviation hκ hN (E N) z _ (mul_nonneg (le_max_right _ _) hδN0) (fun m hm j h0 => ?_)
    (fun m hm => ?_) φ hφ
  · have := (hevN m hm z hz).1 j
    rw [h0, sub_self, norm_zero] at this
    have : 0 ≤ 2 * |κ / (N : ℝ)| := by positivity
    linarith
  · have h0 := (hevN m hm z hz).2
    rw [sNsrc_eq, sLimsrc_eq] at h0
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, one_mul] at h0
    exact h0.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hδN0)

end QuantumNLS.Prop019Deviation

#print axioms QuantumNLS.Prop019Deviation.eigen_eq_sNf
#print axioms QuantumNLS.Prop019Deviation.transfer_deviation
#print axioms QuantumNLS.Prop019Deviation.deviation_of_bundle
