import QuantumNLS.ResolventWordCoefficientLOCAL005

set_option autoImplicit false
noncomputable section

namespace QuantumNLS.ResolventWordLabelInjectiveLOCAL005

open QuantumNLS.ResolventWordCoefficientLOCAL005

/-- At fixed output mode, the successive Fourier labels recover every
intermediate parity-sector shift. -/
theorem pathLabels_injective {k : ℕ} (n : ℤ)
    {q q' : Fin (k - 1) → ℤ}
    (h : ∀ j : Fin k, wordLabel n q j = wordLabel n q' j) : q = q' := by
  classical
  have hvals : ∀ m (hm : m < k - 1), q ⟨m, hm⟩ = q' ⟨m, hm⟩ := by
    intro m
    induction m with
    | zero =>
        intro hm
        have hkNe : (1 : ℕ) ≠ k := by omega
        have hzero := h ⟨0, by omega⟩
        simp [wordLabel, previousShift, nextShift, hkNe] at hzero
        omega
    | succ m ih =>
        intro hm
        have hprev : m < k - 1 := by omega
        have hprevEq := ih hprev
        have hnotzero : m + 1 ≠ 0 := by omega
        have hnotlast : m + 1 + 1 ≠ k := by omega
        have hstep := h ⟨m + 1, by omega⟩
        simp [wordLabel, previousShift, nextShift, hnotzero, hnotlast,
          Nat.succ_sub_one] at hstep
        rw [hprevEq] at hstep
        omega
  funext i
  simpa using hvals i.val i.isLt

#print axioms pathLabels_injective

end QuantumNLS.ResolventWordLabelInjectiveLOCAL005
