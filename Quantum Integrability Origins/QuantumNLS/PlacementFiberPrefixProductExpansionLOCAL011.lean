/-
QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011 — the chosen
kernel-list product expansion required by LOCAL-011.

The finite-degree overlap identity is assembled into an actual kernel list
for arbitrary input lists. Its represented operator and its radius bound
are proved directly from the overlap construction and the source-weighted
radius majorant.
-/
import QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound42

set_option linter.style.haveILetI false
set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberGrouping
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound42
  QuantumNLS.PlacementFiberPrefixAlignedTransport
  QuantumNLS.PlacementFiberBound QuantumNLS.PlacementGrouping
  QuantumNLS.RadiusBound QuantumNLS.LocalPlacement

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- One source-normalized overlap contribution inserted at its union degree. -/
def overlapProductKernelTerm {N : ℕ} (A B : KernelList (H := H) N)
    (p q : Fin (N + 1)) (s : FeasibleOverlapIndex N p.1 q.1) :
    KernelList (H := H) N :=
  kernelSpike (H := H)
    (((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ) •
      averagedOverlapKernel
        (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
        (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) (A p) (B q))

/-- The chosen product kernel list: degreewise overlap kernels are grouped
by their union degree using kernelSpike. -/
def chosenProductKernelList (N : ℕ) (A B : KernelList (H := H) N) :
    KernelList (H := H) N :=
  ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
    ∑ s : FeasibleOverlapIndex N p.1 q.1,
      overlapProductKernelTerm A B p q s

private theorem castSymSectorOperator_eq_cast {m n : ℕ} (h : m = n)
    (K : BoundedSymmetricKernel H m) :
    castSymSectorOperator h K = h ▸ K := by
  cases h
  rfl

private theorem genericU_zero {N n : ℕ} (hn : n ≤ N) :
    genericU_N_r N n hn (0 : BoundedSymmetricKernel H n) = 0 := by
  have h := QuantumNLS.RootOverlapLimit.genericU_add N n hn
    (0 : BoundedSymmetricKernel H n) 0
  have h' : genericU_N_r N n hn (0 : BoundedSymmetricKernel H n) =
      genericU_N_r N n hn 0 + genericU_N_r N n hn 0 := by
    simpa using h
  have hcancel :
      genericU_N_r N n hn (0 : BoundedSymmetricKernel H n) + 0 =
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
          genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (F i p) :=
      Finset.sum_comm
    _ = ∑ i, represented (F i) := by
          simp [represented, RadiusBound.Q_eq_genericU_N_r]

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

private theorem radiusBound_finsetSum_le {N : ℕ} {ι : Type*}
    (R : ℝ) (hR : 0 ≤ R) (s : Finset ι)
    (F : ι → KernelList (H := H) N) :
    QuantumNLS.RadiusBound.radiusBound R (∑ i ∈ s, F i) ≤ ∑ i ∈ s, QuantumNLS.RadiusBound.radiusBound R (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [radiusBound_zero]
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      calc
        QuantumNLS.RadiusBound.radiusBound R (F i + ∑ j ∈ s, F j) ≤
            QuantumNLS.RadiusBound.radiusBound R (F i) + QuantumNLS.RadiusBound.radiusBound R (∑ j ∈ s, F j) :=
          radiusBound_add hR (F i) _
        _ ≤ QuantumNLS.RadiusBound.radiusBound R (F i) + ∑ j ∈ s, QuantumNLS.RadiusBound.radiusBound R (F j) :=
          add_le_add_right ih _

private theorem radiusBound_fintypeSum_le {N : ℕ} {ι : Type*}
    [Fintype ι] (R : ℝ) (hR : 0 ≤ R)
    (F : ι → KernelList (H := H) N) :
    QuantumNLS.RadiusBound.radiusBound R (∑ i, F i) ≤ ∑ i, QuantumNLS.RadiusBound.radiusBound R (F i) := by
  classical
  simpa using radiusBound_finsetSum_le R hR Finset.univ F

private theorem radiusBound_kernelSpike {N n : ℕ} (hn : n ≤ N)
    (R : ℝ) (K : BoundedSymmetricKernel H n) :
    QuantumNLS.RadiusBound.radiusBound (N := N) R (kernelSpike (H := H) (N := N) K) = R ^ n * ‖K‖ := by
  classical
  let k : Fin (N + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  unfold QuantumNLS.RadiusBound.radiusBound
  rw [Finset.sum_eq_single k]
  · simp [kernelSpike, k, castSymSectorOperator_eq_cast]
  · intro j hj hjk
    have hjn : j.1 ≠ n := by
      intro h
      apply hjk
      apply Fin.ext
      exact h
    rw [kernelSpike, dite_eq_right hjn]
    have hzero :
        ‖(0 : SymSector ℂ H j.1 →L[ℂ] SymSector ℂ H j.1)‖ = 0 := norm_zero (E := SymSector ℂ H j.1 →L[ℂ] SymSector ℂ H j.1)
    rw [hzero, mul_zero]
  · simp [k]

private theorem radiusBound_overlapProductKernelTerm {N : ℕ} {R : ℝ}
    (p q : Fin (N + 1)) (A B : KernelList (H := H) N)
    (s : FeasibleOverlapIndex N p.1 q.1) :
    QuantumNLS.RadiusBound.radiusBound R (overlapProductKernelTerm A B p q s) =
      sourceWeightedOverlapTerm N p.1 q.1 R (A p) (B q) s.1.1 := by
  have hsp : s.1.1 ≤ p.1 :=
    le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _)
  have hsq : s.1.1 ≤ q.1 :=
    le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)
  have hcoef : 0 ≤ overlapCoefficient N p.1 q.1 s.1.1 :=
    overlapCoefficient_nonneg N p.1 q.1 s.1.1
  have hnorm :
      ‖((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ)‖ =
        overlapCoefficient N p.1 q.1 s.1.1 := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hcoef]
  unfold overlapProductKernelTerm
  let K := averagedOverlapKernel
    (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
    (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) (A p) (B q)
  let c : ℂ := ((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ)
  have hc : ‖c‖ = overlapCoefficient N p.1 q.1 s.1.1 := by
    simpa [c] using hnorm
  change QuantumNLS.RadiusBound.radiusBound R
      (kernelSpike (H := H) (N := N) (c • K)) =
    sourceWeightedOverlapTerm N p.1 q.1 R (A p) (B q) s.1.1
  have hspike := radiusBound_kernelSpike (N := N)
    (n := unionSize p.1 q.1 s.1.1) s.2 R (c • K)
  rw [hspike, norm_smul_kernel, hc]
  simp [sourceWeightedOverlapTerm, le_min hsp hsq]
  ring

private theorem radiusBound_feasibleOverlap_sum_le {N p q : ℕ} {R : ℝ}
    (hp : p ≤ N) (hq : q ≤ N) (hR : 1 ≤ R)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (∑ s : FeasibleOverlapIndex N p q,
      sourceWeightedOverlapTerm N p q R A Bop s.1.1) ≤
      (R ^ p * ‖A‖) * (R ^ q * ‖Bop‖) := by
  classical
  let S := Finset.range (min p q + 1)
  let F := feasibleOverlapFinset N p q
  let E := feasibleOverlapFilterEquiv N p q
  have hindex :
      (∑ s : FeasibleOverlapIndex N p q,
        sourceWeightedOverlapTerm N p q R A Bop s.1.1) =
        ∑ s ∈ F, sourceWeightedOverlapTerm N p q R A Bop s := by
    calc
      _ = ∑ s : FeasibleOverlapIndex N p q,
            sourceWeightedOverlapTerm N p q R A Bop (E s).1 := by
          apply Finset.sum_congr rfl
          intro s hs
          rfl
      _ = ∑ s : {s : ℕ // s ∈ F},
            sourceWeightedOverlapTerm N p q R A Bop s.1 :=
          Equiv.sum_comp E (fun s => sourceWeightedOverlapTerm N p q R A Bop s.1)
      _ = ∑ s ∈ F, sourceWeightedOverlapTerm N p q R A Bop s :=
          Finset.sum_attach F (fun s => sourceWeightedOverlapTerm N p q R A Bop s)
  have hfilter :
      (∑ s ∈ F, sourceWeightedOverlapTerm N p q R A Bop s) =
        ∑ s ∈ S, sourceWeightedOverlapTerm N p q R A Bop s := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro s hs hnot
    have hsmin : s ≤ min p q := by
      have hs' := Finset.mem_range.mp hs
      omega
    have hlarge : N < unionSize p q s := by
      apply Nat.lt_of_not_ge
      intro hsmall
      apply hnot
      exact Finset.mem_filter.mpr ⟨hs, hsmall⟩
    have hsQ : s ≤ q := le_trans hsmin (min_le_right _ _)
    simp [sourceWeightedOverlapTerm, hsmin,
      overlapCoefficient_eq_zero_of_unionSize_gt hp hsQ hlarge]
  rw [hindex, hfilter]
  exact sourceWeightedOverlap_radius_majorant hp hq hR A Bop

/-- Each fixed pair of input degrees contributes at most the product of
its two source radius weights to the assembled product list. -/
private theorem radiusBound_overlapProductKernelTerm_sum_le {N : ℕ}
    {R : ℝ} (hR : 1 ≤ R) (A B : KernelList (H := H) N)
    (p q : Fin (N + 1)) :
    (∑ s : FeasibleOverlapIndex N p.1 q.1,
      QuantumNLS.RadiusBound.radiusBound R (overlapProductKernelTerm A B p q s)) ≤
      (R ^ p.1 * ‖A p‖) * (R ^ q.1 * ‖B q‖) := by
  calc
    _ = ∑ s : FeasibleOverlapIndex N p.1 q.1,
          sourceWeightedOverlapTerm N p.1 q.1 R (A p) (B q) s.1.1 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact radiusBound_overlapProductKernelTerm p q A B s
    _ ≤ _ := radiusBound_feasibleOverlap_sum_le
      (Nat.lt_succ_iff.mp p.2) (Nat.lt_succ_iff.mp q.2) hR (A p) (B q)

/-- The chosen product list has expansion radius no larger than the product
of the two input expansion radii. -/
theorem chosenProductKernelList_radius_le {N : ℕ} {R : ℝ}
    (hR : 1 ≤ R) (A B : KernelList (H := H) N) :
    QuantumNLS.RadiusBound.radiusBound R (chosenProductKernelList N A B) ≤
      QuantumNLS.RadiusBound.radiusBound R A * QuantumNLS.RadiusBound.radiusBound R B := by
  classical
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  unfold chosenProductKernelList
  calc
    QuantumNLS.RadiusBound.radiusBound R
        (∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          ∑ s : FeasibleOverlapIndex N p.1 q.1,
            overlapProductKernelTerm A B p q s) ≤
      ∑ p : Fin (N + 1), QuantumNLS.RadiusBound.radiusBound R
        (∑ q : Fin (N + 1),
          ∑ s : FeasibleOverlapIndex N p.1 q.1,
            overlapProductKernelTerm A B p q s) := by
        exact radiusBound_fintypeSum_le R hR0 _
    _ ≤ ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          QuantumNLS.RadiusBound.radiusBound R
            (∑ s : FeasibleOverlapIndex N p.1 q.1,
              overlapProductKernelTerm A B p q s) := by
        apply Finset.sum_le_sum
        intro p hp
        exact radiusBound_fintypeSum_le R hR0 _
    _ ≤ ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          ∑ s : FeasibleOverlapIndex N p.1 q.1,
            QuantumNLS.RadiusBound.radiusBound R (overlapProductKernelTerm A B p q s) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        exact radiusBound_fintypeSum_le R hR0 _
    _ ≤ ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          (R ^ p.1 * ‖A p‖) * (R ^ q.1 * ‖B q‖) := by
        apply Finset.sum_le_sum
        intro p hp
        apply Finset.sum_le_sum
        intro q hq
        exact radiusBound_overlapProductKernelTerm_sum_le hR A B p q
    _ = QuantumNLS.RadiusBound.radiusBound R A * QuantumNLS.RadiusBound.radiusBound R B := by
        simp only [QuantumNLS.RadiusBound.radiusBound]
        rw [Finset.sum_mul_sum]

private theorem comp_sum_left {N : ℕ} {ι : Type*} [Fintype ι]
    (F : ι → SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
    (T : SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    (∑ i, F i).comp T = ∑ i, (F i).comp T := by
  classical
  ext x
  simp

private theorem comp_sum_right {N : ℕ} {ι : Type*} [Fintype ι]
    (T : SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
    (F : ι → SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    T.comp (∑ i, F i) = ∑ i, T.comp (F i) := by
  classical
  let hcomp := ContinuousLinearMap.isBoundedLinearMap_comp_left
    (𝕜 := ℂ) (E := SymSector ℂ H N) T
  let L : (SymSector ℂ H N →L[ℂ] SymSector ℂ H N) →ₗ[ℂ]
      (SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :=
    IsBoundedLinearMap.toLinearMap
      (fun f : SymSector ℂ H N →L[ℂ] SymSector ℂ H N => T.comp f) hcomp
  change L (∑ i, F i) = ∑ i, L (F i)
  simpa using (map_sum L Finset.univ F)

private theorem comp_sum_sum {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → SymSector ℂ H N →L[ℂ] SymSector ℂ H N)
    (G : κ → SymSector ℂ H N →L[ℂ] SymSector ℂ H N) :
    (∑ i, F i).comp (∑ j, G j) = ∑ i, ∑ j, (F i).comp (G j) := by
  classical
  calc
    (∑ i, F i).comp (∑ j, G j) =
        ∑ i, (F i).comp (∑ j, G j) := comp_sum_left F _
    _ = ∑ i, ∑ j, (F i).comp (G j) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact comp_sum_right (F i) G

private theorem represented_eq_genericUSum {N : ℕ}
    (A : KernelList (H := H) N) :
    represented A = ∑ p : Fin (N + 1),
      genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p) := by
  unfold represented
  apply Finset.sum_congr rfl
  intro p hp
  exact RadiusBound.Q_eq_genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p)

/-- The assembled chosen list represents the operator product, by the exact
fixed-degree overlap product identity. -/
theorem represented_chosenProductKernelList {N : ℕ}
    (A B : KernelList (H := H) N) :
    represented (chosenProductKernelList N A B) =
      (represented A).comp (represented B) := by
  classical
  calc
    represented (chosenProductKernelList N A B) =
        ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          ∑ s : FeasibleOverlapIndex N p.1 q.1,
            (((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ) •
              genericU_N_r N (unionSize p.1 q.1 s.1.1) s.2
                (averagedOverlapKernel
                  (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
                  (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _))
                  (A p) (B q))) := by
      simp only [chosenProductKernelList, represented_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro s hs
      simpa [overlapProductKernelTerm] using represented_scaledKernelSpike s.2
        ((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ)
        (averagedOverlapKernel
          (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
          (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _))
          (A p) (B q))
    _ = ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          (genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p)).comp
            (genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      exact (QuantumNLS.PlacementFiberPrefixAlignedTransport.genericU_product_eq_overlapKernelExpansion
          (Nat.lt_succ_iff.mp p.2) (Nat.lt_succ_iff.mp q.2) (A p) (B q)).symm
    _ = (represented A).comp (represented B) := by
      rw [represented_eq_genericUSum, represented_eq_genericUSum]
      exact (comp_sum_sum
        (fun p : Fin (N + 1) =>
          genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p))
        (fun q : Fin (N + 1) =>
          genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q))).symm

/-- Package the constructed kernel list as LOCAL-011's chosen expansion,
with the represented operator fixed to the product of the inputs. -/
def chosenProductExpansion {N : ℕ} (A B : KernelList (H := H) N) :
    ChosenExpansion (H := H) N where
  kernels := chosenProductKernelList N A B
  operator := (represented A).comp (represented B)
  represents := by
    rw [← RadiusBound.represented_eq_representedOperator]
    exact (represented_chosenProductKernelList A B).symm

/-- The chosen product expansion itself satisfies the printed expansion
radius bound. -/
theorem chosenProductExpansion_radius_le {N : ℕ} {R : ℝ}
    (hR : 1 ≤ R) (A B : KernelList (H := H) N) :
    LocalPlacement.radiusBound (chosenProductExpansion A B) R ≤
      QuantumNLS.RadiusBound.radiusBound R A *
        QuantumNLS.RadiusBound.radiusBound R B := by
  rw [← RadiusBound.radiusBound_eq_local R (chosenProductExpansion A B)]
  exact chosenProductKernelList_radius_le hR A B

/-- Local placement algebra clauses in source order. The first clause now
constructs the chosen product expansion for arbitrary lists and proves both
its representation and source radius inequality. The remaining clauses
restate the fixed-degree product and commutator support, including the
accepted represented commutator and its radius loss. -/
theorem local011_full_source_ordered_clauses {N : ℕ} {r R : ℝ}
    (hr : 1 ≤ r) (hR : r < R) (A B : KernelList (H := H) N) :
    (∃ C : ChosenExpansion (H := H) N,
      C.operator = (represented A).comp (represented B) ∧
      LocalPlacement.radiusBound C R ≤
        QuantumNLS.RadiusBound.radiusBound R A *
          QuantumNLS.RadiusBound.radiusBound R B) ∧
    (∀ (n p q : ℕ) (hp : p ≤ n) (hq : q ≤ n)
      (K : BoundedSymmetricKernel H p) (L : BoundedSymmetricKernel H q),
      (genericU_N_r n p hp K).comp (genericU_N_r n q hq L) =
        ∑ s : FeasibleOverlapIndex n p q,
          (((overlapCoefficient n p q s.1.1 : ℝ) : ℂ) •
            genericU_N_r n (unionSize p q s.1.1) s.2
              (averagedOverlapKernel
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) K L))) ∧
    (∀ {n p q : ℕ} {ρ : ℝ} (hp : p ≤ n) (hq : q ≤ n) (_hρ : 1 ≤ ρ)
      (K : BoundedSymmetricKernel H p) (L : BoundedSymmetricKernel H q),
      ‖(genericU_N_r n p hp K).comp (genericU_N_r n q hq L)‖ ≤
        (ρ ^ p * ‖K‖) * (ρ ^ q * ‖L‖)) ∧
    (∀ (n p q : ℕ) (hp : p ≤ n) (hq : q ≤ n)
      (K : BoundedSymmetricKernel H p) (L : BoundedSymmetricKernel H q),
      (n : ℝ) *
          ‖(genericU_N_r n p hp K).comp (genericU_N_r n q hq L) -
            (genericU_N_r n q hq L).comp (genericU_N_r n p hp K)‖ ≤
        2 * (p * q : ℝ) * ‖K‖ * ‖L‖) ∧
    represented (positiveOverlapCommutatorList N A B) =
      ((Complex.I : ℂ) * (N : ℂ)) •
        ((represented A).comp (represented B) -
          (represented B).comp (represented A)) ∧
    QuantumNLS.RadiusBound.radiusBound r (positiveOverlapCommutatorList N A B) ≤
      (2 / (R - r)) *
        (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
        QuantumNLS.RadiusBound.radiusBound R B := by
  have h42 := QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound42.local011_source_ordered_clauses
    hr hR A B
  refine ⟨?_, h42.1, h42.2.1, h42.2.2.1, h42.2.2.2.1, h42.2.2.2.2⟩
  exact ⟨chosenProductExpansion A B, rfl,
    chosenProductExpansion_radius_le (lt_of_le_of_lt hr hR).le A B⟩

#print axioms chosenProductKernelList_radius_le
#print axioms represented_chosenProductKernelList
#print axioms chosenProductExpansion_radius_le
#print axioms local011_full_source_ordered_clauses

end QuantumNLS.PlacementFiberPrefixProductExpansionLOCAL011

end
