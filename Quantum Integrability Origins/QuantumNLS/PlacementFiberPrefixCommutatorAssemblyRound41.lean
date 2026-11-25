/-
QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound41 — reindex the two
finite product expansions and cancel their zero-overlap fibers.
-/
import QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound40

set_option linter.style.haveILetI false

open scoped InnerProductSpace TensorProduct
open QuantumNLS.TensorCarrier QuantumNLS.TensorPlacements
  QuantumNLS.KernelDefinition QuantumNLS.PlacementFusion
  QuantumNLS.PlacementOverlap QuantumNLS.PlacementProduct
  QuantumNLS.PlacementUnionReindex QuantumNLS.PlacementFiberTransport
  QuantumNLS.PlacementFiberOperator QuantumNLS.PlacementFiberPrefixCommutator
  QuantumNLS.PlacementFiberPrefixCommutatorAssembly
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound39
  QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound40
  QuantumNLS.PlacementFiberPrefixAlignedTransport
  QuantumNLS.RadiusBound QuantumNLS.LocalPlacement

noncomputable section

namespace QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound41

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem unionSize_swap (p q s : ℕ) (hsp : s ≤ p) (hsq : s ≤ q) :
    unionSize q p s = unionSize p q s := by
  dsimp [unionSize]
  omega

private theorem feasible_overlap_left_le {N p q : ℕ}
    (s : FeasibleOverlapIndex N p q) : s.1.1 ≤ p :=
  le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _)

private theorem feasible_overlap_right_le {N p q : ℕ}
    (s : FeasibleOverlapIndex N p q) : s.1.1 ≤ q :=
  le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)

private def feasibleOverlapSwap (N p q : ℕ) :
    FeasibleOverlapIndex N p q ≃ FeasibleOverlapIndex N q p := by
  let hmin : min p q = min q p := Nat.min_comm p q
  let hfin : min p q + 1 = min q p + 1 := congrArg (fun n : ℕ => n + 1) hmin
  refine
    { toFun := fun s => ⟨Fin.cast hfin s.1, ?_⟩
      invFun := fun s => ⟨Fin.cast hfin.symm s.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hsp : s.1.1 ≤ p := feasible_overlap_left_le s
    have hsq : s.1.1 ≤ q := feasible_overlap_right_le s
    have hval : (Fin.cast hfin s.1).1 = s.1.1 := by simp
    rw [hval, unionSize_swap p q s.1.1 hsp hsq]
    exact s.2
  · have hsp : s.1.1 ≤ q := feasible_overlap_left_le s
    have hsq : s.1.1 ≤ p := feasible_overlap_right_le s
    have hval : (Fin.cast hfin.symm s.1).1 = s.1.1 := by simp
    rw [hval, (unionSize_swap p q s.1.1 hsq hsp).symm]
    exact s.2
  · intro s
    apply Subtype.ext
    simp [Fin.cast_cast]
  · intro s
    apply Subtype.ext
    simp [Fin.cast_cast]

private theorem genericU_cast_eq {N m n : ℕ} (h : m = n)
    (hm : m ≤ N) (hn : n ≤ N) (K : BoundedSymmetricKernel H m) :
    genericU_N_r N n hn (castSymSectorOperator h K) =
      genericU_N_r N m hm K := by
  subst n
  have hproof : hn = hm := Subsingleton.elim _ _
  subst hn
  simp [genericU_N_r, castSymSectorOperator]

private theorem castSymSectorOperator_eq_cast {m n : ℕ} (h : m = n)
    (K : BoundedSymmetricKernel H m) :
    castSymSectorOperator h K = h ▸ K := by
  cases h
  rfl

private theorem genericU_sub {N n : ℕ} (hn : n ≤ N)
    (K L : BoundedSymmetricKernel H n) :
    genericU_N_r N n hn (K - L) =
      genericU_N_r N n hn K - genericU_N_r N n hn L := by
  calc
    genericU_N_r N n hn (K - L) =
        genericU_N_r N n hn (K + -L) := by rw [sub_eq_add_neg]
    _ = genericU_N_r N n hn K + genericU_N_r N n hn (-L) :=
      QuantumNLS.RootOverlapLimit.genericU_add N n hn K (-L)
    _ = genericU_N_r N n hn K - genericU_N_r N n hn L := by
      have hneg : genericU_N_r N n hn (-L) =
          -genericU_N_r N n hn L := by
        have h := QuantumNLS.RootOverlapLimit.genericU_smul N n hn (-1 : ℂ) L
        have hL : (-1 : ℂ) • L = -L := neg_one_smul ℂ L
        have hT : (-1 : ℂ) • genericU_N_r N n hn L =
            -genericU_N_r N n hn L :=
          neg_one_smul ℂ (genericU_N_r N n hn L)
        calc
          _ = genericU_N_r N n hn ((-1 : ℂ) • L) :=
            congrArg (genericU_N_r N n hn) hL.symm
          _ = (-1 : ℂ) • genericU_N_r N n hn L := h
          _ = _ := hT
      rw [hneg]
      simp [sub_eq_add_neg]

/-- Reindex the swapped finite product expansion by the same feasible
overlap size, transport its kernel degree, and cancel the zero-overlap
average with the frozen Round39 identity. -/
theorem genericU_commutator_eq_positiveOverlapExpansion
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    (genericU_N_r N p hp A).comp (genericU_N_r N q hq Bop) -
        (genericU_N_r N q hq Bop).comp (genericU_N_r N p hp A) =
      ∑ s : FeasibleOverlapIndex N p q,
        if hs : 1 ≤ s.1.1 then
          (((overlapCoefficient N p q s.1.1 : ℝ) : ℂ) •
            genericU_N_r N (unionSize p q s.1.1) s.2
              (overlapCommutatorKernel
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _)) A Bop))
        else 0 := by
  classical
  let E := feasibleOverlapSwap N p q
  let hsP := fun s : FeasibleOverlapIndex N p q =>
    feasible_overlap_left_le s
  let hsQ := fun s : FeasibleOverlapIndex N p q =>
    feasible_overlap_right_le s
  let hsize := fun s : FeasibleOverlapIndex N p q =>
    unionSize_swap p q s.1.1 (feasible_overlap_left_le s)
      (feasible_overlap_right_le s)
  let hBAdegree := fun s : FeasibleOverlapIndex N p q =>
    calc
      unionSize q p (E s).1.1 = unionSize q p s.1.1 := by
        simp [E, feasibleOverlapSwap]
      _ = unionSize p q s.1.1 := hsize s
  let KBA := fun s : FeasibleOverlapIndex N p q =>
    castSymSectorOperator (hBAdegree s) (by
      let t : FeasibleOverlapIndex N q p := E s
      have htq : t.1.1 ≤ q := feasible_overlap_left_le t
      have htp : t.1.1 ≤ p := feasible_overlap_right_le t
      exact averagedOverlapKernel htq htp Bop A)
  have hAB := genericU_product_eq_overlapKernelExpansion hp hq A Bop
  have hBA := genericU_product_eq_overlapKernelExpansion hq hp Bop A
  have hBA_reindex :
      (∑ t : FeasibleOverlapIndex N q p,
        (((overlapCoefficient N q p t.1.1 : ℝ) : ℂ) •
          genericU_N_r N (unionSize q p t.1.1) t.2
            (averagedOverlapKernel
              (feasible_overlap_left_le t)
              (feasible_overlap_right_le t) Bop A))) =
      ∑ s : FeasibleOverlapIndex N p q,
        (((overlapCoefficient N q p (E s).1.1 : ℝ) : ℂ) •
          genericU_N_r N (unionSize q p (E s).1.1) (E s).2
            (averagedOverlapKernel
              (feasible_overlap_left_le (E s))
              (feasible_overlap_right_le (E s)) Bop A)) := by
    symm
    exact Equiv.sum_comp E (fun t =>
      (((overlapCoefficient N q p t.1.1 : ℝ) : ℂ) •
        genericU_N_r N (unionSize q p t.1.1) t.2
          (averagedOverlapKernel
            (feasible_overlap_left_le t)
            (feasible_overlap_right_le t) Bop A)))
  rw [hAB, hBA, hBA_reindex, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  have hval : (E s).1.1 = s.1.1 := by
    simp [E, feasibleOverlapSwap]
  have hcoeff : overlapCoefficient N p q s.1.1 =
      overlapCoefficient N q p (E s).1.1 := by
    rw [hval]
    exact overlapCoefficient_symmetric N p q s.1.1 hp hq
      (feasible_overlap_left_le s) (feasible_overlap_right_le s)
  have hBAop :
      genericU_N_r N (unionSize q p (E s).1.1) (E s).2
          (averagedOverlapKernel
            (feasible_overlap_left_le (E s))
            (feasible_overlap_right_le (E s)) Bop A) =
        genericU_N_r N (unionSize p q s.1.1) s.2 (KBA s) := by
    have hdeg : unionSize q p (E s).1.1 = unionSize p q s.1.1 := by
      exact hBAdegree s
    have hcast := genericU_cast_eq (hBAdegree s) (E s).2 s.2
      (averagedOverlapKernel (feasible_overlap_left_le (E s))
        (feasible_overlap_right_le (E s)) Bop A)
    exact hcast.symm
  by_cases hs0 : s.1.1 = 0
  · have hnot : ¬ 1 ≤ s.1.1 := by omega
    simp only [dite_eq_right hnot]
    have hzeroFeasible : unionSize p q 0 ≤ N := by
      simpa [hs0] using s.2
    let s0 : FeasibleOverlapIndex N p q := ⟨0, hzeroFeasible⟩
    have hsEq : s = s0 := by
      apply Subtype.ext
      exact Fin.ext hs0
    subst s
    rw [hcoeff, hBAop]
    have hz := zeroOverlapKernelIdentity (H := H) p q A Bop
    have hsp0 : hsP s0 = Nat.zero_le p := Subsingleton.elim _ _
    have hsq0 : hsQ s0 = Nat.zero_le q := Subsingleton.elim _ _
    have hABavg :
        averagedOverlapKernel (hsP s0) (hsQ s0) A Bop =
          averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) A Bop := by
      cases hsp0
      cases hsq0
      rfl
    have hq0 : feasible_overlap_left_le (E s0) = Nat.zero_le q :=
      Subsingleton.elim _ _
    have hp0 : feasible_overlap_right_le (E s0) = Nat.zero_le p :=
      Subsingleton.elim _ _
    have hBAavg :
        averagedOverlapKernel (feasible_overlap_left_le (E s0))
            (feasible_overlap_right_le (E s0)) Bop A =
          averagedOverlapKernel (Nat.zero_le q) (Nat.zero_le p) Bop A := by
      cases hq0
      cases hp0
      rfl
    have h0 : unionSize p q 0 = unionSize q p 0 := by
      dsimp [unionSize]
      omega
    have h0degree : hBAdegree s0 = h0.symm := Subsingleton.elim _ _
    have hKBA : KBA s0 =
        castSymSectorOperator h0.symm
          (averagedOverlapKernel (Nat.zero_le q) (Nat.zero_le p) Bop A) := by
      change castSymSectorOperator (hBAdegree s0)
          (averagedOverlapKernel (feasible_overlap_left_le (E s0))
            (feasible_overlap_right_le (E s0)) Bop A) = _
      rw [hBAavg]
      exact congrArg (fun h => castSymSectorOperator h
        (averagedOverlapKernel (Nat.zero_le q) (Nat.zero_le p) Bop A)) h0degree
    have hz' :
        averagedOverlapKernel (hsP s0) (hsQ s0) A Bop = KBA s0 := by
      have hABavg0 :
          averagedOverlapKernel (hsP s0) (hsQ s0) A Bop =
            averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) A Bop := by
        simpa [s0] using hABavg
      have hz0 :
          averagedOverlapKernel (Nat.zero_le p) (Nat.zero_le q) A Bop =
            castSymSectorOperator h0.symm
              (averagedOverlapKernel (Nat.zero_le q) (Nat.zero_le p) Bop A) := by
        simpa [unionSize] using hz
      exact hABavg0.trans (hz0.trans hKBA.symm)
    rw [hz']
    simp
  · have hspos : 1 ≤ s.1.1 := Nat.one_le_iff_ne_zero.mpr hs0
    simp only [dite_eq_left hspos]
    rw [hcoeff, hBAop]
    have hcomm :
        averagedOverlapKernel (hsP s) (hsQ s) A Bop - KBA s =
          overlapCommutatorKernel (hsP s) (hsQ s) A Bop := by
      unfold overlapCommutatorKernel
      dsimp [KBA]
      rw [castSymSectorOperator_eq_cast]
      rfl
    let c : ℂ := ((overlapCoefficient N q p (E s).1.1 : ℝ) : ℂ)
    calc
      c • genericU_N_r N (unionSize p q s.1.1) s.2
          (averagedOverlapKernel (hsP s) (hsQ s) A Bop) -
        c • genericU_N_r N (unionSize p q s.1.1) s.2 (KBA s) =
          c • genericU_N_r N (unionSize p q s.1.1) s.2
            (overlapCommutatorKernel (hsP s) (hsQ s) A Bop) := by
              calc
                _ = c • (genericU_N_r N (unionSize p q s.1.1) s.2
                    (averagedOverlapKernel (hsP s) (hsQ s) A Bop) -
                  genericU_N_r N (unionSize p q s.1.1) s.2 (KBA s)) :=
                    (smul_sub c _ _).symm
                _ = c • genericU_N_r N (unionSize p q s.1.1) s.2
                    (averagedOverlapKernel (hsP s) (hsQ s) A Bop - KBA s) := by
                      rw [← genericU_sub]
                _ = _ := by rw [hcomm]

private abbrev PositiveFeasibleOverlapIndex (N p q : ℕ) :=
  {s : FeasibleOverlapIndex N p q // 1 ≤ s.1.1}

private abbrev ActiveFinOverlapIndex (N p q : ℕ) :=
  {s : Fin (N + 1) //
    1 ≤ s.1 ∧ s.1 ≤ min p q ∧ unionSize p q s.1 ≤ N}

private def positiveFeasibleOverlapEquiv (N p q : ℕ) (hp : p ≤ N) (hq : q ≤ N) :
    PositiveFeasibleOverlapIndex N p q ≃ ActiveFinOverlapIndex N p q where
  toFun s :=
    ⟨⟨s.1.1.1, by
        have hlt := s.1.1.2
        have hmin : min p q ≤ N := le_trans (min_le_left _ _) hp
        omega⟩,
      ⟨s.2, Nat.lt_succ_iff.mp s.1.1.2, s.1.2⟩⟩
  invFun s :=
    ⟨⟨⟨s.1.1, by omega⟩, s.2.2.2⟩, s.2.1⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    rfl
  right_inv s := by
    apply Subtype.ext
    apply Fin.ext
    rfl

private theorem sum_guarded_subtype {α β : Type*} [Fintype α]
    [AddCommMonoid β] (P : α → Prop) [Fintype {a : α // P a}]
    [DecidablePred P] (F : α → β) :
    (∑ a : {a : α // P a}, F a.1) =
      ∑ a : α, if P a then F a else 0 := by
  classical
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) F).symm

private def activePositiveOverlapTerm (N : ℕ) (p q : Fin (N + 1))
    (A B : KernelList (H := H) N)
    (s : ActiveFinOverlapIndex N p.1 q.1) :
    SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
  genericU_N_r N (unionSize p.1 q.1 s.1.1) s.2.2.2
    ((((Complex.I : ℂ) * (N : ℂ) *
      ((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ)) •
      overlapCommutatorKernel (le_trans s.2.2.1 (min_le_left _ _))
        (le_trans s.2.2.1 (min_le_right _ _)) (A p) (B q)))

private theorem represented_comp_eq_double_sum {N : ℕ}
    (A B : KernelList (H := H) N) :
    (represented A).comp (represented B) =
      ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
        (genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p)).comp
          (genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q)) := by
  classical
  have hA : represented A =
      ∑ p : Fin (N + 1),
        genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p) := by
    unfold represented
    apply Finset.sum_congr rfl
    intro p hp
    exact RadiusBound.Q_eq_genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p)
  have hB : represented B =
      ∑ q : Fin (N + 1),
        genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q) := by
    unfold represented
    apply Finset.sum_congr rfl
    intro q hq
    exact RadiusBound.Q_eq_genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q)
  rw [hA, hB]
  ext x
  simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  rw [Finset.sum_comm]

private theorem represented_commutator_eq_double_sum {N : ℕ}
    (A B : KernelList (H := H) N) :
    (represented A).comp (represented B) -
        (represented B).comp (represented A) =
      ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
        ((genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p)).comp
            (genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q)) -
          (genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q)).comp
            (genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p))) := by
  classical
  have hAB := represented_comp_eq_double_sum A B
  have hBA := represented_comp_eq_double_sum B A
  have hBA_swap :
      (∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
        (genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (B p)).comp
          (genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (A q))) =
      ∑ p : Fin (N + 1), ∑ q : Fin (N + 1),
        (genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q)).comp
          (genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p)) := by
    exact Finset.sum_comm
  rw [hAB, hBA, hBA_swap, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_sub_distrib]
private theorem genericU_commutator_eq_scaledPositiveOverlapExpansion
    {N p q : ℕ} (hp : p ≤ N) (hq : q ≤ N)
    (A : BoundedSymmetricKernel H p) (Bop : BoundedSymmetricKernel H q) :
    ((Complex.I : ℂ) * (N : ℂ)) •
      ((genericU_N_r N p hp A).comp (genericU_N_r N q hq Bop) -
       (genericU_N_r N q hq Bop).comp (genericU_N_r N p hp A)) =
      ∑ s : FeasibleOverlapIndex N p q,
        if hs : 1 ≤ s.1.1 then
          ((((Complex.I : ℂ) * (N : ℂ) *
            ((overlapCoefficient N p q s.1.1 : ℝ) : ℂ)) •
            genericU_N_r N (unionSize p q s.1.1) s.2
              (overlapCommutatorKernel
                (feasible_overlap_left_le s) (feasible_overlap_right_le s)
                A Bop)))
        else 0 := by
  classical
  rw [genericU_commutator_eq_positiveOverlapExpansion hp hq A Bop,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : 1 ≤ s.1.1
  · simp only [dite_eq_left h]
    rw [smul_smul]
  · simp only [dite_eq_right h]
    simp

private theorem positiveOverlapPair_sum_eq_scaled_commutator
    {N : ℕ} (p q : Fin (N + 1))
    (A B : KernelList (H := H) N) :
    (∑ s : Fin (N + 1),
      if h : 1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧
          unionSize p.1 q.1 s.1 ≤ N then
        genericU_N_r N (unionSize p.1 q.1 s.1) h.2.2
          ((((Complex.I : ℂ) * (N : ℂ) *
            ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
            overlapCommutatorKernel
              (le_trans h.2.1 (min_le_left _ _))
              (le_trans h.2.1 (min_le_right _ _)) (A p) (B q)))
      else 0) =
      ((Complex.I : ℂ) * (N : ℂ)) •
        ((genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p)).comp
          (genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q)) -
         (genericU_N_r N q.1 (Nat.lt_succ_iff.mp q.2) (B q)).comp
          (genericU_N_r N p.1 (Nat.lt_succ_iff.mp p.2) (A p))) := by
  classical
  let P : Fin (N + 1) → Prop := fun s =>
    1 ≤ s.1 ∧ s.1 ≤ min p.1 q.1 ∧ unionSize p.1 q.1 s.1 ≤ N
  let e := positiveFeasibleOverlapEquiv N p.1 q.1
    (Nat.lt_succ_iff.mp p.2) (Nat.lt_succ_iff.mp q.2)
  let T : ActiveFinOverlapIndex N p.1 q.1 →
      SymSector ℂ H N →L[ℂ] SymSector ℂ H N :=
    activePositiveOverlapTerm N p q A B
  let F : Fin (N + 1) → SymSector ℂ H N →L[ℂ] SymSector ℂ H N := fun s =>
    if hs : P s then T ⟨s, hs⟩ else 0
  have hguard := sum_guarded_subtype P F
  have hcandidate :
      (∑ s : Fin (N + 1), if h : P s then
        genericU_N_r N (unionSize p.1 q.1 s.1) h.2.2
          ((((Complex.I : ℂ) * (N : ℂ) *
            ((overlapCoefficient N p.1 q.1 s.1 : ℝ) : ℂ)) •
            overlapCommutatorKernel
              (le_trans h.2.1 (min_le_left _ _))
              (le_trans h.2.1 (min_le_right _ _)) (A p) (B q)))
        else 0) =
      ∑ s : ActiveFinOverlapIndex N p.1 q.1, T s := by
    calc
      _ = ∑ s : Fin (N + 1), if P s then F s else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases h : P s
        · simp [F, T, h, activePositiveOverlapTerm]
        · simp [h]
      _ = ∑ s : {s : Fin (N + 1) // P s}, F s.1 := hguard.symm
      _ = ∑ s : ActiveFinOverlapIndex N p.1 q.1, T s := by
        apply Finset.sum_congr rfl
        intro s hs
        have hpos : 1 ≤ s.1.1 := s.2.1
        have hmin : s.1.1 ≤ min p.1 q.1 := s.2.2.1
        have hunion : unionSize p.1 q.1 s.1.1 ≤ N := s.2.2.2
        have hpleft : s.1.1 ≤ p.1 := le_trans hmin (min_le_left _ _)
        have hqright : s.1.1 ≤ q.1 := le_trans hmin (min_le_right _ _)
        have hpleftFin : s.1 ≤ p := Fin.le_iff_val_le_val.mpr hpleft
        have hqrightFin : s.1 ≤ q := Fin.le_iff_val_le_val.mpr hqright
        have hactive : 1 ≤ s.1.1 ∧ s.1.1 ≤ min p.1 q.1 ∧
            unionSize p.1 q.1 s.1.1 ≤ N := ⟨hpos, hmin, hunion⟩
        simp [F, T, P, hactive, hpleftFin, hqrightFin,
          activePositiveOverlapTerm]
  have hindex :
      (∑ s : ActiveFinOverlapIndex N p.1 q.1, T s) =
        ∑ t : PositiveFeasibleOverlapIndex N p.1 q.1, T (e t) := by
    exact (Equiv.sum_comp e T).symm
  have hterms :
      (∑ t : PositiveFeasibleOverlapIndex N p.1 q.1, T (e t)) =
        ∑ t : PositiveFeasibleOverlapIndex N p.1 q.1,
          (((Complex.I : ℂ) * (N : ℂ) *
            ((overlapCoefficient N p.1 q.1 t.1.1.1 : ℝ) : ℂ)) •
            genericU_N_r N (unionSize p.1 q.1 t.1.1.1) t.1.2
              (overlapCommutatorKernel
                (le_trans (Nat.lt_succ_iff.mp t.1.1.2) (min_le_left _ _))
                (le_trans (Nat.lt_succ_iff.mp t.1.1.2) (min_le_right _ _))
                (A p) (B q))) := by
    apply Finset.sum_congr rfl
    intro t ht
    simp [T, e, positiveFeasibleOverlapEquiv, activePositiveOverlapTerm]
    rw [QuantumNLS.RootOverlapLimit.genericU_smul]
  let G : FeasibleOverlapIndex N p.1 q.1 →
      SymSector ℂ H N →L[ℂ] SymSector ℂ H N := fun s =>
    if hs : 1 ≤ s.1.1 then
      (((Complex.I : ℂ) * (N : ℂ) *
        ((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ)) •
        genericU_N_r N (unionSize p.1 q.1 s.1.1) s.2
          (overlapCommutatorKernel
            (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
            (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _))
            (A p) (B q)))
    else 0
  have hguardFeasible := sum_guarded_subtype
    (fun s : FeasibleOverlapIndex N p.1 q.1 => 1 ≤ s.1.1) G
  have hpositive :
      (∑ t : PositiveFeasibleOverlapIndex N p.1 q.1,
        (((Complex.I : ℂ) * (N : ℂ) *
          ((overlapCoefficient N p.1 q.1 t.1.1.1 : ℝ) : ℂ)) •
          genericU_N_r N (unionSize p.1 q.1 t.1.1.1) t.1.2
            (overlapCommutatorKernel
              (le_trans (Nat.lt_succ_iff.mp t.1.1.2) (min_le_left _ _))
              (le_trans (Nat.lt_succ_iff.mp t.1.1.2) (min_le_right _ _))
              (A p) (B q)))) =
      ∑ s : FeasibleOverlapIndex N p.1 q.1, if hs : 1 ≤ s.1.1 then
        (((Complex.I : ℂ) * (N : ℂ) *
          ((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ)) •
          genericU_N_r N (unionSize p.1 q.1 s.1.1) s.2
            (overlapCommutatorKernel
              (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
              (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _))
              (A p) (B q))) else 0 := by
    calc
      _ = ∑ t : PositiveFeasibleOverlapIndex N p.1 q.1, G t.1 := by
        apply Finset.sum_congr rfl
        intro t ht
        simp [G, t.2]
      _ = ∑ s : FeasibleOverlapIndex N p.1 q.1,
          if hs : 1 ≤ s.1.1 then G s else 0 := hguardFeasible
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases h : 1 ≤ s.1.1
        · simp [G, h]
        · simp [G, h]
  have hscaled := genericU_commutator_eq_scaledPositiveOverlapExpansion
    (Nat.lt_succ_iff.mp p.2) (Nat.lt_succ_iff.mp q.2) (A p) (B q)
  calc
    _ = ∑ s : ActiveFinOverlapIndex N p.1 q.1, T s := hcandidate
    _ = ∑ t : PositiveFeasibleOverlapIndex N p.1 q.1,
          (((Complex.I : ℂ) * (N : ℂ) *
            ((overlapCoefficient N p.1 q.1 t.1.1.1 : ℝ) : ℂ)) •
            genericU_N_r N (unionSize p.1 q.1 t.1.1.1) t.1.2
              (overlapCommutatorKernel
                (le_trans (Nat.lt_succ_iff.mp t.1.1.2) (min_le_left _ _))
                (le_trans (Nat.lt_succ_iff.mp t.1.1.2) (min_le_right _ _))
                (A p) (B q))) := hindex.trans hterms
    _ = ∑ s : FeasibleOverlapIndex N p.1 q.1, if hs : 1 ≤ s.1.1 then
          (((Complex.I : ℂ) * (N : ℂ) *
            ((overlapCoefficient N p.1 q.1 s.1.1 : ℝ) : ℂ)) •
            genericU_N_r N (unionSize p.1 q.1 s.1.1) s.2
              (overlapCommutatorKernel
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_left _ _))
                (le_trans (Nat.lt_succ_iff.mp s.1.2) (min_le_right _ _))
                (A p) (B q))) else 0 := hpositive
    _ = _ := hscaled.symm

theorem represented_positiveOverlapCommutatorList_eq_scaledCommutator
    {N : ℕ} (A B : KernelList (H := H) N) :
    represented (positiveOverlapCommutatorList N A B) =
      ((Complex.I : ℂ) * (N : ℂ)) •
        ((represented A).comp (represented B) -
          (represented B).comp (represented A)) := by
  classical
  rw [represented_positiveOverlapCommutatorList_eq_finiteOperatorSum,
    represented_commutator_eq_double_sum]
  simp_rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact positiveOverlapPair_sum_eq_scaled_commutator p q A B

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

private theorem radiusBound_sum_le {N : ℕ} {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : 0 ≤ r) (F : ι → KernelList (H := H) N) :
    radiusBound r (∑ i, F i) ≤ ∑ i, radiusBound r (F i) := by
  classical
  simpa using radiusBound_finsetSum_le r hr Finset.univ F

private theorem radiusBound_kernelSpike {N n : ℕ} (hn : n ≤ N)
    (r : ℝ) (K : BoundedSymmetricKernel H n) :
    QuantumNLS.RadiusBound.radiusBound (N := N) r
        (kernelSpike (H := H) (N := N) (n := n) K) = r ^ n * ‖K‖ := by
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

#print axioms genericU_commutator_eq_positiveOverlapExpansion
#print axioms genericU_commutator_eq_scaledPositiveOverlapExpansion
#print axioms positiveOverlapPair_sum_eq_scaled_commutator
#print axioms represented_positiveOverlapCommutatorList_eq_scaledCommutator
#print axioms radiusBound_finsetSum_le
#print axioms radiusBound_sum_le
#print axioms radiusBound_kernelSpike

end QuantumNLS.PlacementFiberPrefixCommutatorAssemblyRound41

end
