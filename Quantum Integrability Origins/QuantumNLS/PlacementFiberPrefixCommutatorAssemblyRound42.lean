/-
QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound42 — transfer the
ungrouped positive-overlap radius estimate to the degreewise grouped list.
-/
import QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound41

set_option linter.style.haveILetI false
set_option maxHeartbeats 5000000

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberPrefixCommutator
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound39
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound40
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound41
  QuantumNLS.PlacementFiberPrefixAlignedTransport
  QuantumNLS.RadiusBound QuantumNLS.LocalPlacement

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound42

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem radiusBound_finsetSum_le {N : ℕ} {ι : Type*}
    (r : ℝ) (hr : 0 ≤ r) (s : Finset ι)
    (F : ι → KernelList (H := H) N) :
    radiusBound r (∑ i ∈ s, F i) ≤ ∑ i ∈ s, radiusBound r (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [radiusBound_zero]
  | @insert i s his ih =>
      simp only [Finset.sum_insert his]
      calc
        radiusBound r (F i + ∑ j ∈ s, F j) ≤
            radiusBound r (F i) + radiusBound r (∑ j ∈ s, F j) :=
          radiusBound_add hr (F i) _
        _ ≤ radiusBound r (F i) + ∑ j ∈ s, radiusBound r (F j) :=
          add_le_add_right ih _

private theorem radiusBound_fintypeSum_le {N : ℕ} {ι : Type*}
    [Fintype ι] (r : ℝ) (hr : 0 ≤ r)
    (F : ι → KernelList (H := H) N) :
    radiusBound r (∑ i, F i) ≤ ∑ i, radiusBound r (F i) := by
  classical
  simpa using radiusBound_finsetSum_le r hr Finset.univ F

private theorem fin_sum_eq_cutoff_sum {N q : ℕ} (hq : q ≤ N)
    (f : ℕ → ℝ) (hzero : ∀ m, q < m → f m = 0) :
    (∑ s : Fin (N + 1), f s.1) = ∑ m ∈ Finset.range (q + 1), f m := by
  calc
    _ = ∑ m ∈ Finset.range (N + 1), f m :=
      Fin.sum_univ_eq_sum_range f (N + 1)
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hq))
      intro m hm hmn
      have hmqnot : ¬m < q + 1 := by simpa using hmn
      have hmq : q < m := by omega
      simp [hzero m hmq]

private theorem fin_sum_positive_cutoff {N q : ℕ} (hq : q ≤ N)
    (f : ℕ → ℝ) (hzero : ∀ m, q < m → f m = 0) :
    (∑ s : Fin (N + 1), if 1 ≤ s.1 then f s.1 else 0) =
      ∑ s ∈ (Finset.range (q + 1)).filter (fun s => 1 ≤ s), f s := by
  calc
    _ = ∑ m ∈ Finset.range (q + 1), if 1 ≤ m then f m else 0 :=
      fin_sum_eq_cutoff_sum hq (fun m => if 1 ≤ m then f m else 0)
        (by
          intro m hmq
          have hmpos : 1 ≤ m := by omega
          simp [hmpos, hzero m hmq])
    _ = _ := by rw [← Finset.sum_filter]

private theorem castSymSectorOperator_eq_cast {m n : ℕ} (h : m = n)
    (K : BoundedSymmetricKernel H m) :
    castSymSectorOperator h K = h ▸ K := by
  cases h
  rfl

private theorem radiusBound_kernelSpike_round42 {N n : ℕ} (hn : n ≤ N)
    (r : ℝ) (K : BoundedSymmetricKernel H n) :
    QuantumNLS.RadiusBound.radiusBound (N := N) r
        (kernelSpike (H := H) (N := N) (n := n) K) =
      r ^ n * ‖K‖ := by
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
    change r ^ j.1 *
      ‖(0 : SymSector ℂ H j.1 →L[ℂ] SymSector ℂ H j.1)‖ = 0
    have hnorm :
        ‖(0 : SymSector ℂ H j.1 →L[ℂ] SymSector ℂ H j.1)‖ = 0 :=
      norm_zero (E := SymSector ℂ H j.1 →L[ℂ] SymSector ℂ H j.1)
    rw [hnorm, mul_zero]
  · simp [k]

private theorem overlapContribution_radius_nonneg
    {N p q s : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q)
    (hs : s ≤ min p q) :
    0 ≤ (N : ℝ) * overlapCoefficient N p q s *
      (r ^ unionSize p q s *
        ‖(Complex.I : ℂ) • overlapCommutatorKernel (p := p) (q := q) (s := s)
          (le_trans hs (min_le_left _ _))
          (le_trans hs (min_le_right _ _)) A Bop‖) := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg N) (overlapCoefficient_nonneg N p q s))
    (mul_nonneg (pow_nonneg hr _)
      (norm_nonneg ((Complex.I : ℂ) • overlapCommutatorKernel
        (p := p) (q := q) (s := s)
        (le_trans hs (min_le_left _ _))
        (le_trans hs (min_le_right _ _)) A Bop)))

/-- Grouping equal output degrees into a `KernelList` costs at most the
ungrouped sum of the source-weighted positive-overlap kernel norms.  The
conversion from `Fin (N+1)` to the `q`-bounded overlap range records the
coefficient-sum bridge used by the radius-loss estimate. -/
theorem positiveOverlapCommutatorList_radius_le_ungrouped
    {N : ℕ} {r : ℝ} (hr : 1 ≤ r)
    (A B : KernelList (H := H) N) :
    radiusBound r (positiveOverlapCommutatorList N A B) ≤
      (∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
        ∑ s ∈ (Finset.range (q.1 + 1)).filter (fun s => 1 ≤ s),
          if hs : s ≤ min p.1 q.1 then
            (N : ℝ) * overlapCoefficient N p.1 q.1 s *
              (r ^ unionSize p.1 q.1 s *
                ‖(Complex.I : ℂ) • overlapCommutatorKernel
                  (p := p.1) (q := q.1) (s := s)
                  (le_trans hs (min_le_left _ _))
                  (le_trans hs (min_le_right _ _)) (A p) (B q)‖)
          else 0) := by
  classical
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr
  unfold positiveOverlapCommutatorList
  calc
    radiusBound r
        (∑ p : Fin (N + 1), ∑ q : Fin (N + 1), ∑ s : Fin (N + 1),
          if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
              unionSize p.1 q.1 s.1 ≤ N then
            kernelSpike (H := H) (N := N) (n := unionSize p.1 q.1 s.1)
              (((Complex.I : ℂ) * (N : ℂ) *
                ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
                overlapCommutatorKernel (p := p.1) (q := q.1) (s := s.1)
                  (le_trans h.2.1 (min_le_left _ _))
                  (le_trans h.2.1 (min_le_right _ _)) (A p) (B q))
          else 0)
        ≤ ∑ p : Fin (N + 1),
            RadiusBound.radiusBound r
              (∑ q : Fin (N + 1), ∑ s : Fin (N + 1),
                if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
                    unionSize p.1 q.1 s.1 ≤ N then
                  kernelSpike (H := H) (N := N) (n := unionSize p.1 q.1 s.1)
                    (((Complex.I : ℂ) * (N : ℂ) *
                      ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
                      overlapCommutatorKernel (p := p.1) (q := q.1) (s := s.1)
                        (le_trans h.2.1 (min_le_left _ _))
                        (le_trans h.2.1 (min_le_right _ _)) (A p) (B q))
                else 0) := by
          exact radiusBound_fintypeSum_le r hr0
            (fun p => ∑ q : Fin (N + 1), ∑ s : Fin (N + 1),
              if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
                  unionSize p.1 q.1 s.1 ≤ N then
                kernelSpike (H := H) (N := N) (n := unionSize p.1 q.1 s.1)
                  (((Complex.I : ℂ) * (N : ℂ) *
                    ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
                    overlapCommutatorKernel (p := p.1) (q := q.1) (s := s.1)
                      (le_trans h.2.1 (min_le_left _ _))
                      (le_trans h.2.1 (min_le_right _ _)) (A p) (B q))
              else 0)
    _ ≤ ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          RadiusBound.radiusBound r
            (∑ s : Fin (N + 1),
              if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
                  unionSize p.1 q.1 s.1 ≤ N then
                kernelSpike (H := H) (N := N) (n := unionSize p.1 q.1 s.1)
                  (((Complex.I : ℂ) * (N : ℂ) *
                    ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
                    overlapCommutatorKernel (p := p.1) (q := q.1) (s := s.1)
                      (le_trans h.2.1 (min_le_left _ _))
                      (le_trans h.2.1 (min_le_right _ _)) (A p) (B q))
              else 0) := by
          apply Finset.sum_le_sum
          intro p hp
          exact radiusBound_fintypeSum_le r hr0
            (fun q => ∑ s : Fin (N + 1),
              if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
                  unionSize p.1 q.1 s.1 ≤ N then
                kernelSpike (H := H) (N := N) (n := unionSize p.1 q.1 s.1)
                  (((Complex.I : ℂ) * (N : ℂ) *
                    ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
                    overlapCommutatorKernel (p := p.1) (q := q.1) (s := s.1)
                      (le_trans h.2.1 (min_le_left _ _))
                      (le_trans h.2.1 (min_le_right _ _)) (A p) (B q))
              else 0)
    _ ≤ ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          ∑ s : Fin (N + 1),
            RadiusBound.radiusBound r
              (if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
                  unionSize p.1 q.1 s.1 ≤ N then
                kernelSpike (H := H) (N := N) (n := unionSize p.1 q.1 s.1)
                  (((Complex.I : ℂ) * (N : ℂ) *
                    ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
                    overlapCommutatorKernel (p := p.1) (q := q.1) (s := s.1)
                      (le_trans h.2.1 (min_le_left _ _))
                      (le_trans h.2.1 (min_le_right _ _)) (A p) (B q))
              else 0) := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          exact radiusBound_fintypeSum_le r hr0
            (fun (s : Fin (N + 1)) => if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
                unionSize p.1 q.1 s.1 ≤ N then
              let K : BoundedSymmetricKernel H (unionSize p.1 q.1 s.1) :=
                overlapCommutatorKernel (p := p.1) (q := q.1) (s := s.1)
                  (le_trans h.2.1 (min_le_left _ _))
                  (le_trans h.2.1 (min_le_right _ _)) (A p) (B q)
              kernelSpike (H := H) (N := N) (n := unionSize p.1 q.1 s.1)
                (((Complex.I : ℂ) * (N : ℂ) *
                  ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) • K)
            else 0)
    _ ≤ ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          ∑ s : Fin (N + 1),
            if hs : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 then
              (N : ℝ) * overlapCoefficient N p.1 q.1 s.1 *
                (r ^ unionSize p.1 q.1 s.1 *
                  ‖(Complex.I : ℂ) • overlapCommutatorKernel
                    (p := p.1) (q := q.1) (s := s)
                    (le_trans hs.2 (min_le_left _ _))
                  (le_trans hs.2 (min_le_right _ _)) (A p) (B q)‖)
            else 0 := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          apply Finset.sum_le_sum
          intro s hs
          by_cases hs' : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1
          · by_cases hN : unionSize p.1 q.1 s.1 ≤ N
            · have hguard : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
                  unionSize p.1 q.1 s.1 ≤ N := ⟨hs'.1, hs'.2, hN⟩
              let K : BoundedSymmetricKernel H (unionSize p.1 q.1 s.1) :=
                overlapCommutatorKernel (p := p.1) (q := q.1) (s := s.1)
                  (le_trans hs'.2 (min_le_left _ _))
                  (le_trans hs'.2 (min_le_right _ _)) (A p) (B q)
              let c : ℂ := (Complex.I : ℂ) * (N : ℂ) *
                ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)
              have hspike := radiusBound_kernelSpike_round42 (H := H)
                (N := N) (n := unionSize p.1 q.1 s.1) hN r (c • K)
              have hscalar :
                  ‖c‖ =
                    (N : ℝ) * overlapCoefficient N p.1 q.1 s.1 := by
                dsimp [c]
                rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_natCast,
                  Complex.norm_real]
                rw [Real.norm_eq_abs,
                  abs_of_nonneg (overlapCoefficient_nonneg N p.1 q.1 s.1)]
                ring
              simp only [dif_pos hguard, dif_pos hs']
              rw [hspike, norm_smul_kernel, norm_smul_kernel, hscalar]
              rw [Complex.norm_I]
              dsimp [K]
              apply le_of_eq
              ring
            · have hlarge : N < unionSize p.1 q.1 s.1 := by omega
              have hcoefzero := PlacementGrouping.overlapCoefficient_eq_zero_of_unionSize_gt
                (Nat.lt_succ_iff.mp p.2)
                (le_trans hs'.2 (min_le_right _ _)) hlarge
              have hguard : ¬ (1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
                  unionSize p.1 q.1 s.1 ≤ N) := by omega
              simp only [dif_neg hguard, dif_pos hs']
              rw [hcoefzero]
              simp [RadiusBound.radiusBound_zero]
          · have hguard : ¬ (1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
                unionSize p.1 q.1 s.1 ≤ N) := by
              intro h
              exact hs' ⟨h.1, h.2.1⟩
            simp only [dif_neg hguard]
            simp only [RadiusBound.radiusBound_zero, dif_neg hs']
            norm_num
    _ = ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          ∑ s ∈ (Finset.range (q.1 + 1)).filter (fun s => 1 ≤ s),
            if hs : s ≤ min p.1 q.1 then
              (N : ℝ) * overlapCoefficient N p.1 q.1 s *
                (r ^ unionSize p.1 q.1 s *
                  ‖(Complex.I : ℂ) • overlapCommutatorKernel
                    (p := p.1) (q := q.1) (s := s)
                    (le_trans hs (min_le_left _ _))
                    (le_trans hs (min_le_right _ _)) (A p) (B q)‖)
            else 0 := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          let f : ℕ → ℝ := fun s =>
            if hs : s ≤ min p.1 q.1 then
              (N : ℝ) * overlapCoefficient N p.1 q.1 s *
                (r ^ unionSize p.1 q.1 s *
                  ‖(Complex.I : ℂ) • overlapCommutatorKernel
                    (p := p.1) (q := q.1) (s := s)
                    (le_trans hs (min_le_left _ _))
                    (le_trans hs (min_le_right _ _)) (A p) (B q)‖)
            else 0
          have hzero : ∀ s, q.1 < s → f s = 0 := by
            intro s hsq
            have hnot : ¬ s ≤ min p.1 q.1 := by omega
            simp only [f, dif_neg hnot]
          calc
            (∑ s : Fin (N + 1),
                if hs : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 then
                  (N : ℝ) * overlapCoefficient N p.1 q.1 s.1 *
                    (r ^ unionSize p.1 q.1 s.1 *
                      ‖(Complex.I : ℂ) • overlapCommutatorKernel
                        (p := p.1) (q := q.1) (s := s.1)
                        (le_trans hs.2 (min_le_left _ _))
                        (le_trans hs.2 (min_le_right _ _)) (A p) (B q)‖)
                else 0) =
              ∑ s : Fin (N + 1), if hs : 1 ≤ s.1 then f s.1 else 0 := by
                apply Finset.sum_congr rfl
                intro s hs
                by_cases hpos : 1 ≤ s.1
                · simp [f, hpos]
                · simp [hpos]
            _ = ∑ s ∈ (Finset.range (q.1 + 1)).filter (fun s => 1 ≤ s), f s :=
              fin_sum_positive_cutoff (Nat.lt_succ_iff.mp q.2) f hzero
            _ = _ := by
              apply Finset.sum_congr rfl
              intro s hs
              simp [f]

/-- The source's commutator radius loss follows from the grouped-to-ungrouped
coefficient-sum inequality and the established ungrouped majorant. -/
theorem candidateRadiusBound {N : ℕ} {r R : ℝ}
    (hr : 1 ≤ r) (hR : r < R)
    (A B : KernelList (H := H) N) :
    radiusBound r (positiveOverlapCommutatorList N A B) ≤
      (2 / (R - r)) *
        (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
        radiusBound R B := by
  calc
    radiusBound r (positiveOverlapCommutatorList N A B) ≤
        (∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
          ∑ s ∈ (Finset.range (q.1 + 1)).filter (fun s => 1 ≤ s),
            if hs : s ≤ min p.1 q.1 then
              (N : ℝ) * overlapCoefficient N p.1 q.1 s *
                (r ^ unionSize p.1 q.1 s *
                  ‖(Complex.I : ℂ) • overlapCommutatorKernel
                    (p := p.1) (q := q.1) (s := s)
                    (le_trans hs (min_le_left _ _))
                    (le_trans hs (min_le_right _ _)) (A p) (B q)‖)
            else 0) :=
      positiveOverlapCommutatorList_radius_le_ungrouped hr A B
    _ ≤ (2 / (R - r)) *
          (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
          radiusBound R B :=
      positiveOverlap_commutatorSeries_radius_majorant hr hR A B

/-- LOCAL-011's proved clauses in source order: the frozen finite-degree
product grouping, product norm and fixed-degree commutator clauses, followed
by the represented positive-overlap commutator and its radius-loss bound. -/
theorem local011_source_ordered_clauses {N : ℕ} {r R : ℝ}
    (hr : 1 ≤ r) (hR : r < R)
    (A B : KernelList (H := H) N) :
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
    radiusBound r (positiveOverlapCommutatorList N A B) ≤
      (2 / (R - r)) *
        (∑ p : Fin (N + 1), (p.1 : ℝ) * r ^ p.1 * ‖A p‖) *
        radiusBound R B := by
  have hbase :=
    QuantumNLS.PlacementFiberPrefixCommutatorAssembly.local011_product_and_fixedDegree_clauses
      (H := H)
  exact ⟨hbase.1, hbase.2.1, hbase.2.2,
    QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound41.represented_positiveOverlapCommutatorList_eq_scaledCommutator
      A B,
    candidateRadiusBound hr hR A B⟩

#print axioms positiveOverlapCommutatorList_radius_le_ungrouped
#print axioms candidateRadiusBound
#print axioms local011_source_ordered_clauses

end QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound42

end
