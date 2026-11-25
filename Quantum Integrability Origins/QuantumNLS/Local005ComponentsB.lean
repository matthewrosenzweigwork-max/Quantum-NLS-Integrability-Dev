import QuantumNLS.Local005CountingB

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace QuantumNLS.Local005

/-- A potential factor exchanges the two vector components. -/
def componentAfter (k : ℕ) (j : Fin 2) : Fin 2 :=
  ⟨(j.val + k) % 2, Nat.mod_lt _ (by decide)⟩

theorem componentAfter_zero (j : Fin 2) : componentAfter 0 j = j := by
  apply Fin.ext
  simp [componentAfter, Nat.mod_eq_of_lt j.isLt]

theorem componentAfter_step (k : ℕ) (j : Fin 2) :
    componentAfter (k + 1) j ≠ componentAfter k j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [componentAfter] at hv
  omega

/-- Every allowed component path is forced by the potential's off-diagonal support. -/
theorem component_path_unique (k : ℕ) (σ : ℕ → Fin 2)
    (h : ∀ t < k, σ (t + 1) ≠ σ t) : σ k = componentAfter k (σ 0) := by
  have hall : ∀ t, t ≤ k → σ t = componentAfter t (σ 0) := by
    intro t
    induction t with
    | zero => intro _; exact (componentAfter_zero _).symm
    | succ t ih =>
      intro ht
      have he := ih (by omega)
      have hne := h t (by omega)
      have hc := componentAfter_step t (σ 0)
      apply Fin.ext
      have hs0 := (σ (t + 1)).isLt
      have hs1 := (σ t).isLt
      have hc0 := (componentAfter (t + 1) (σ 0)).isLt
      have hc1 := (componentAfter t (σ 0)).isLt
      have hval := congrArg Fin.val he
      have hnval : (σ (t + 1)).val ≠ (σ t).val := fun hv => hne (Fin.ext hv)
      have hncval : (componentAfter (t + 1) (σ 0)).val ≠
          (componentAfter t (σ 0)).val := fun hv => hc (Fin.ext hv)
      omega
  exact hall k le_rfl

theorem componentAfter_odd {k : ℕ} (hk : Odd k) (j : Fin 2) :
    componentAfter k j ≠ j := by
  intro h
  have hv := congrArg Fin.val h
  have hp := Nat.odd_iff.mp hk
  have hj := j.isLt
  change (j.val + k) % 2 = j.val at hv
  omega

theorem componentAfter_even {k : ℕ} (hk : Even k) (j : Fin 2) :
    componentAfter k j = j := by
  apply Fin.ext
  have hp : k % 2 = 0 := Nat.even_iff.mp hk
  change (j.val + k) % 2 = j.val
  have hj := j.isLt
  omega

/-- A scalar Fourier path occupies precisely the component reached after k exchanges. -/
def supportedEntry (k : ℕ) (a : ℝ) (i j : Fin 2) : ℝ :=
  if i = componentAfter k j then a else 0

/-- Odd-degree words have zero diagonal. -/
theorem supportedEntry_odd {k : ℕ} (hk : Odd k) (a : ℝ) (j : Fin 2) :
    supportedEntry k a j j = 0 := by
  simp [supportedEntry, Ne.symm (componentAfter_odd hk j)]

/-- Even-degree words have zero off-diagonal entries. -/
theorem supportedEntry_even {k : ℕ} (hk : Even k) (a : ℝ) (i j : Fin 2) (hij : i ≠ j) :
    supportedEntry k a i j = 0 := by
  simp [supportedEntry, componentAfter_even hk j, hij]

#print axioms component_path_unique
#print axioms supportedEntry_odd
#print axioms supportedEntry_even
end QuantumNLS.Local005
