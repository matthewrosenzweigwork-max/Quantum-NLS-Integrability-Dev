/-
QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound40 — candidate-list
representation helpers and assembly of the positive-overlap commutator.
-/
import QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound39
import QuantumNLS.RootOverlapLimit

set_option linter.style.haveILetI false

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberPrefixCommutator
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound39
  QuantumNLS.RadiusBound QuantumNLS.LocalPlacement

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound40

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem genericU_zero {N n : ℕ} (hn : n ≤ N) :
    genericU_N_r N n hn (0 : BoundedSymmetricKernel H n) = 0 := by
  have h := QuantumNLS.RootOverlapLimit.genericU_add N n hn
    (0 : BoundedSymmetricKernel H n) 0
  have h' : genericU_N_r N n hn (0 : BoundedSymmetricKernel H n) =
      genericU_N_r N n hn 0 + genericU_N_r N n hn 0 := by
    simpa using h
  have hcancel :
      genericU_N_r N n hn 0 + (0 : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) =
        genericU_N_r N n hn 0 + genericU_N_r N n hn 0 := by
    simpa only [add_zero] using h'
  exact (add_left_cancel hcancel).symm

private theorem genericU_sum {N n : ℕ} (hn : n ≤ N) {ι : Type*}
    [Fintype ι] (F : ι → BoundedSymmetricKernel H n) :
    genericU_N_r N n hn (∑ i, F i) = ∑ i, genericU_N_r N n hn (F i) := by
  classical
  have hsum (s : Finset ι) :
      genericU_N_r N n hn (∑ i ∈ s, F i) =
        ∑ i ∈ s, genericU_N_r N n hn (F i) := by
    induction s using Finset.induction_on with
    | empty => simp [genericU_zero]
    | @insert i s his ih =>
        simp only [Finset.sum_insert his]
        rw [QuantumNLS.RootOverlapLimit.genericU_add, ih]
  simpa using hsum Finset.univ

private theorem represented_sum {N : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → KernelList (H := H) N) :
    represented (∑ i, F i) = ∑ i, represented (F i) := by
  classical
  unfold represented
  calc
    (∑ p : Fin (N + 1),
        Q N p.1 (Nat.lt_succ_iff.mp p.2) ((∑ i, F i) p)) =
      ∑ p : Fin (N + 1), ∑ i,
        genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (F i p) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [RadiusBound.Q_eq_genericU_N_r]
          simpa only [Finset.sum_apply] using
            genericU_sum (Nat.lt_succ_iff.mp p.2) (fun i => F i p)
    _ = ∑ i, ∑ p : Fin (N + 1),
          genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (F i p) := by
          exact Finset.sum_comm
    _ = ∑ i, represented (F i) := by
          simp [represented, RadiusBound.Q_eq_genericU_N_r]

private theorem represented_zero {N : ℕ} :
    represented (0 : KernelList (H := H) N) = 0 := by
  classical
  have h := represented_sum (N := N) (ι := Empty) (fun i => (0 : KernelList (H := H) N))
  simpa using h

private theorem represented_kernelSpike {N n : ℕ} (hn : n ≤ N)
    (K : BoundedSymmetricKernel H n) :
    represented (kernelSpike (H := H) K) = genericU_N_r N n hn K := by
  classical
  let k : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  unfold represented kernelSpike
  rw [Finset.sum_eq_single k]
  · simp [k, RadiusBound.Q_eq_genericU_N_r, castSymSectorOperator]
  · intro j hj hjk
    have hjn : j.1 ≠ n := by
      intro h
      apply hjk
      apply Fin.ext
      exact h
    simpa [RadiusBound.Q_eq_genericU_N_r, hjn] using
      genericU_zero (N := N) (n := j.1) (Nat.lt_succ_iff.mp j.2)
  · simp [k]

private theorem represented_scaledKernelSpike {N n : ℕ} (hn : n ≤ N)
    (c : ℂ) (K : BoundedSymmetricKernel H n) :
    represented (kernelSpike (H := H) (c • K)) =
      c • genericU_N_r N n hn K := by
  rw [represented_kernelSpike]
  exact QuantumNLS.RootOverlapLimit.genericU_smul N n hn c K

theorem represented_positiveOverlapCommutatorList_eq_finiteOperatorSum {N : ℕ}
    (A B : KernelList (H := H) N) :
    represented (positiveOverlapCommutatorList N A B) =
      ∑ p : Fin (N + 1), ∑ q : Fin (N + 1), ∑ s : Fin (N + 1),
        if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
            unionSize p.1 q.1 s.1 ≤ N then
          genericU_N_r N (unionSize p.1 q.1 s.1) h.2.2
            ((((Complex.I : ℂ) * (N : ℂ) *
              ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
              overlapCommutatorKernel
                (le_trans h.2.1 (min_le_left _ _))
                (le_trans h.2.1 (min_le_right _ _)) (A p) (B q)))
        else 0 := by
  classical
  unfold positiveOverlapCommutatorList
  simp only [represented_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
      unionSize p.1 q.1 s.1 ≤ N
  · simp only [dite_eq_left h]
    rw [QuantumNLS.RootOverlapLimit.genericU_smul]
    exact represented_scaledKernelSpike (N := N)
      (n := unionSize p.1 q.1 s.1) h.2.2
      (((Complex.I : ℂ) * (N : ℂ) *
        ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)))
      (overlapCommutatorKernel
        (le_trans h.2.1 (min_le_left _ _))
        (le_trans h.2.1 (min_le_right _ _)) (A p) (B q))
  · simp only [dite_eq_right h]
    exact represented_zero (H := H) (N := N)

#print axioms represented_positiveOverlapCommutatorList_eq_finiteOperatorSum

end QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound40

end
