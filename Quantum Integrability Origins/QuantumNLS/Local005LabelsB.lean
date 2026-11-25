import QuantumNLS.Local005CountingB

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
namespace QuantumNLS.Local005
open QuantumNLS.ResolventWordCoefficientLOCAL005
open QuantumNLS.ResolventWordLabelInjectiveLOCAL005

/-- Endpoint-completed intermediate shift; both endpoint shifts are zero. -/
def vertex {k : ℕ} (q : Fin (k - 1) → ℤ) (t : ℕ) : ℤ :=
  if h : 0 < t ∧ t < k then q ⟨t - 1, by omega⟩ else 0

/-- The path's actual parity-sector mode at each vertex. -/
def modeAt {k : ℕ} (n : ℤ) (q : Fin (k - 1) → ℤ) (t : ℕ) : ℤ :=
  n + 2 * vertex q t

theorem label_vertex {k : ℕ} (n : ℤ) (q : Fin (k - 1) → ℤ) (j : Fin k) :
    wordLabel n q j = n + vertex q j.val + vertex q (j.val + 1) := by
  unfold wordLabel previousShift nextShift vertex
  split_ifs <;> simp_all <;> omega

theorem mode_label {k : ℕ} (n : ℤ) (q : Fin (k - 1) → ℤ) (j : Fin k) :
    modeAt n q j.val + modeAt n q (j.val + 1) = 2 * wordLabel n q j := by
  rw [label_vertex]
  unfold modeAt
  ring

/-- In odd degree the endpoint recursion recovers the output mode too. -/
theorem odd_output_eq {k : ℕ} (hk : Odd k) (n n' : ℤ)
    (q q' : Fin (k - 1) → ℤ)
    (h : ∀ j : Fin k, wordLabel n q j = wordLabel n' q' j) : n = n' := by
  have hd : ∀ t : ℕ, t ≤ k →
      modeAt n q t - modeAt n' q' t = (-1 : ℤ) ^ t * (n - n') := by
    intro t
    induction t with
    | zero => simp [modeAt, vertex]
    | succ t ih =>
      intro ht
      have hlt : t < k := by omega
      have hp := ih (by omega)
      have he := h ⟨t, hlt⟩
      have hleft := mode_label n q ⟨t, hlt⟩
      have hright := mode_label n' q' ⟨t, hlt⟩
      simp only at hleft hright
      rw [he] at hleft
      rw [pow_succ]
      nlinarith
  have he := hd k le_rfl
  rw [hk.neg_one_pow] at he
  simp [modeAt, vertex] at he
  omega

/-- All Fourier labels uniquely determine an odd-degree path and its output. -/
theorem odd_labels_injective {k : ℕ} (hk : Odd k) :
    Function.Injective (fun p : ℤ × (Fin (k - 1) → ℤ) => wordLabel p.1 p.2) := by
  rintro ⟨n, q⟩ ⟨n', q'⟩ h
  have hn := odd_output_eq hk n n' q q' (congrFun h)
  subst n'
  have hq := pathLabels_injective n (congrFun h)
  exact Prod.ext rfl hq

#print axioms odd_output_eq
#print axioms odd_labels_injective
end QuantumNLS.Local005
