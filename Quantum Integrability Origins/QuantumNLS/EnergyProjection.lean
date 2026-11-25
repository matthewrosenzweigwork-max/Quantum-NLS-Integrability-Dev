import QuantumNLS.LinearTailHamiltonian
import QuantumNLS.DiagSelfAdjointCommute
import QuantumNLS.TransferNormality
import QuantumNLS.HilbertDiagOp

/-!
# R-36C23346 clause (c), Part C-1: the energy projection `P_{N,E}` in the eigenbasis of `H_N`

Source: `source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:611-613` (`P_{N,E} = 1_{[0,NE]}(H_N)`) and clause (c).

Route (as the integrator directed): `H_N = Hop (κ/N)` has the orthonormal eigenbasis of normalized waves (accepted
UBB1 basis conclusion), with eigenvalues `e_n = Σ_j sourceRoots_j²`. Each `e_n ≥ 0`. The projection `P_{N,E}` is the
bounded diagonal operator with mask `1_{e_n ≤ NE}` in that basis. This is the diagonal (basis) form of
`1_{[0,NE]}(H_N)`: a bounded selfadjoint idempotent, commuting with `H_N` and with the transported `L_N(t)`.

Proved here (standard axioms only): `energy_projection`. The Borel functional-calculus form of `1_{[0,NE]}(H_N)` is not
used; the basis form is the one the repository supports for the diagonal `H_N`.

Clause (c) (the N-uniform marginal estimate) remains OPEN; see the report.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace QuantumNLS.EnergyProjection

open QuantumNLS.ContactOperator QuantumNLS.BetheConditionalBasis QuantumNLS.BethePhysicalTransfer
open QuantumNLS.LinearTailGenerator QuantumNLS.LinearTailCommute QuantumNLS.LinearTailHamiltonian
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor QuantumNLS.BetheFreeFamily

variable (L : ℝ) [Fact (0 < L)]

/-- The `H_N` eigenvalue of the normalized wave `n`: `Σ_j sourceRoots_j²`. -/
def energyEig (κ : ℝ) (N : ℕ) (n : Label N) : ℝ :=
  ∑ j, (QuantumNLS.BetheSmooth.sourceRoots L n.val (κ / (N : ℝ)) j) ^ 2

theorem energyEig_nonneg (κ : ℝ) (N : ℕ) (n : Label N) : 0 ≤ energyEig L κ N n :=
  Finset.sum_nonneg (fun j _ => sq_nonneg _)

/-- A diagonal bounded projector in a Hilbert basis from a `0/1` mask. -/
theorem diag_projection {ι : Type*} [DecidableEq ι] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (B : HilbertBasis ι ℂ H) (μ : ι → ℝ)
    (hμ : ∀ i, μ i = 0 ∨ μ i = 1) :
    ∃ P : H →L[ℂ] H, (∀ i, P (B i) = (μ i : ℂ) • B i) ∧ P * P = P ∧
      ContinuousLinearMap.adjoint P = P := by
  obtain ⟨P, hcoef, -⟩ := QuantumNLS.HilbertDiagOp.diag_exists B (fun i => (μ i : ℂ)) 1
    (by intro i; rcases hμ i with h | h <;> simp [h]) zero_le_one
  have hPb : ∀ i, P (B i) = (μ i : ℂ) • B i := by
    intro i
    have hdiff : ∀ j, ⟪B j, P (B i) - (μ i : ℂ) • B i⟫_ℂ = 0 := by
      intro j
      rw [inner_sub_right, inner_smul_right, hcoef j (B i)]
      by_cases hji : j = i
      · subst hji
        ring
      · rw [B.orthonormal.inner_eq_zero hji]
        ring
    have hsum := QuantumNLS.HilbertDiagOp.parseval_hasSum B (P (B i) - (μ i : ℂ) • B i)
    have hz : (fun j => ‖⟪B j, P (B i) - (μ i : ℂ) • B i⟫_ℂ‖ ^ 2) = fun _ => (0 : ℝ) := by
      funext j
      rw [hdiff j]
      simp
    rw [hz] at hsum
    have h0 := hsum.unique hasSum_zero
    have h1 : ‖P (B i) - (μ i : ℂ) • B i‖ = 0 := (pow_eq_zero_iff two_ne_zero).mp h0
    exact sub_eq_zero.mp (norm_eq_zero.mp h1)
  have hPP : P * P = P := by
    apply QuantumNLS.TransferNormality.ext_of_hilbertBasis B
    intro i
    rw [ContinuousLinearMap.mul_apply, hPb i, map_smul, hPb i, smul_smul]
    rcases hμ i with h | h <;> simp [h]
  have hadj : ContinuousLinearMap.adjoint P = P := by
    apply QuantumNLS.TransferNormality.ext_of_hilbertBasis B
    intro i
    rw [QuantumNLS.TransferNormality.adjoint_diag B P (fun i => (μ i : ℂ)) hPb i, hPb i,
      Complex.conj_ofReal]
  exact ⟨P, hPb, hPP, hadj⟩

/-- **Energy projection `P_{N,E}`** (`P_{N,E} = 1_{[0,NE]}(H_N)` in the diagonal form of the basis, clause (c)
ingredient). For `κ > 0`, `N ≥ 1`, `E` real, there is a bounded operator `P` with:
(i) `P (ψ_n) = 1_{e_n ≤ NE} ψ_n` on the normalized-wave basis (the eigenvalues of `H_N`);
(ii) `P` is an orthogonal projection (`P * P = P`, `P` selfadjoint);
(iii) `P` commutes with `H_N` on its domain;
(iv) `P` commutes with the transported `L_N(t)`. -/
theorem energy_projection (κ : ℝ) (hκ : 0 < κ) (N : ℕ) (hN : 1 ≤ N) (E : ℝ)
    (s : Finset ℤ) (t : ℤ → ℝ) :
    ∃ P : SymL2 L N →L[ℂ] SymL2 L N,
      (∀ n : Label N, P (normalizedWave L N ⟨κ / (N : ℝ), (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n) =
        ((if energyEig L κ N n ≤ (N : ℝ) * E then (1 : ℝ) else 0 : ℝ) : ℂ) •
          normalizedWave L N ⟨κ / (N : ℝ), (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le⟩ n) ∧
      P * P = P ∧ ContinuousLinearMap.adjoint P = P ∧
      (∀ ψ (hψ : ψ ∈ (Hop (L := L) (N := N) (κ / (N : ℝ))
          (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le).domain),
        ∃ h : P ψ ∈ (Hop (L := L) (N := N) (κ / (N : ℝ))
            (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le).domain,
          Hop (L := L) (N := N) (κ / (N : ℝ))
              (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le ⟨P ψ, h⟩ =
            P (Hop (L := L) (N := N) (κ / (N : ℝ))
              (div_pos hκ (by exact_mod_cast (show 0 < N by omega))).le ⟨ψ, hψ⟩)) ∧
      Commute P (symGen L κ N s t) := by
  classical
  have hN0 : 0 < N := by omega
  have hc : 0 < κ / (N : ℝ) := div_pos hκ (by exact_mod_cast hN0)
  obtain ⟨-, -, -, -, -, hortho, hdense, heig⟩ :=
    QuantumNLS.UnconditionalBetheBasis.basis L N hN (κ / (N : ℝ)) hc
  let Bn := HilbertBasis.mk hortho hdense.ge
  have hB : ∀ n, Bn n = normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n := fun n =>
    congrFun (HilbertBasis.coe_mk hortho hdense.ge) n
  have hmem : ∀ n, Bn n ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain := fun n => by
    have key0 : ∀ x : SymL2 L N, x = normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n →
        x ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain := by
      rintro x rfl
      exact (heig n).choose
    exact key0 (Bn n) (hB n)
  have hval : ∀ n, (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le) ⟨Bn n, hmem n⟩ =
      ((energyEig L κ N n : ℝ) : ℂ) • Bn n := by
    intro n
    have hv : (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le)
        ⟨normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n, (heig n).choose⟩ =
        ((energyEig L κ N n : ℝ) : ℂ) • normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n := (heig n).choose_spec
    have key1 : ∀ (x : SymL2 L N) (hx : x ∈ (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le).domain),
        x = normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n →
        (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le) ⟨x, hx⟩ = ((energyEig L κ N n : ℝ) : ℂ) • x := by
      rintro x hx rfl
      exact hv
    exact key1 (Bn n) (hmem n) (hB n)
  have hpos : ∀ n : Label N, normalizedWave L N ⟨κ / (N : ℝ), hc.le⟩ n =
      symmetricPosition L N (QuantumNLS.UnconditionalBetheBasis.meanField_physicalBasis L N hN hκ
        (QuantumNLS.BetheConditionalBasis.labelArr N n)) := by
    intro n
    have h := QuantumNLS.UnconditionalBetheBasis.physicalBasis_position L N hN (κ / (N : ℝ)) hc
      (QuantumNLS.BetheConditionalBasis.labelArr N n)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  let lam : Label N → ℂ := fun n =>
    genEigen L κ hκ N hN0 s t (QuantumNLS.BetheConditionalBasis.labelArr N n)
  have hT : ∀ n : Label N, (symGen L κ N s t) (Bn n) = lam n • Bn n := by
    intro n
    rw [hB n, hpos n, symGen_sp, genSum_meanField L κ hκ N hN s t, map_smul]
  let μ : Label N → ℝ := fun n => if energyEig L κ N n ≤ (N : ℝ) * E then 1 else 0
  have hμ : ∀ n, μ n = 0 ∨ μ n = 1 := by
    intro n
    by_cases h : energyEig L κ N n ≤ (N : ℝ) * E
    · right; simp [μ, h]
    · left; simp [μ, h]
  obtain ⟨P, hPb, hPP, hadj⟩ := diag_projection Bn μ hμ
  refine ⟨P, ?_, hPP, hadj, ?_, ?_⟩
  · intro n
    have h := hPb n
    rw [hB n] at h
    rw [h]
  · intro ψ hψ
    exact QuantumNLS.DiagSelfAdjointCommute.diag_selfAdjoint_commute Bn
      (Hop (L := L) (N := N) (κ / (N : ℝ)) hc.le)
      (Hop_isSelfAdjoint (L := L) (N := N) (c := κ / (N : ℝ)) hc.le)
      (fun n => energyEig L κ N n) hmem hval P (fun n => (μ n : ℂ)) hPb ψ hψ
  · exact QuantumNLS.TransferNormality.commute_of_diag Bn P (symGen L κ N s t)
      (fun n => (μ n : ℂ)) (fun n => lam n) hPb hT

end QuantumNLS.EnergyProjection

#print axioms QuantumNLS.EnergyProjection.energy_projection
