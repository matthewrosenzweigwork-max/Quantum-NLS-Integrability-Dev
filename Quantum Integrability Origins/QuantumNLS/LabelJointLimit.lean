import Mathlib

/-!
# PROP-002 `lem:B3-weak-joint-limit`: the finite Bethe pairing identity (algebraic core)

Source: `source/chapters/propagation/label_periods.tex:43-90` (statement and proof), with the Bethe relation
`QG:eq:our-bethe` (`source/chapters/core/QUANTUM_GAUGE_COMPONENTS.tex:132-136`):
`L q_j = 2π n_j + 2 Σ_{ℓ≠j} arctan(c/(q_j − q_ℓ))`, `c = κ/N`, `q_1 < ⋯ < q_N`, `n_1 ≤ ⋯ ≤ n_N`.

What is proved here (literal): for finitely many on-shell roots `q_j` with integer labels `n_j` obeying the
Bethe relation, and any real function `f`, the identity (`eq:B3-weak-bethe-identity`)

  `(1/N) Σ_j n_j f(q_j) = (L/2π) (1/N) Σ_j q_j f(q_j) − (κ/2π) (1/N²) Σ_{j,ℓ} K_N(q_j, q_ℓ)`,

with `K_N(t,u) = (N/κ)(f(t) − f(u)) arctan(κ/(N(t−u)))` off the diagonal and `K_N(t,t) = 0`
(`eq:B3-weak-kernel`). The proof symmetrizes the arctangent sum (antisymmetry of `arctan`), as printed.

NOT formalized here (the remaining content of PROP-002), listed explicitly:
1. Tightness of the integer marginal and the bound `|n_j| ≤ …` on compact `q`-sets, from the uniform label
   distance `|q_j − 2πn_j/L| ≤ 3√(κ/L)` (`QG:eq:B3-uniform-label-distance`, not imported here).
2. The weak limit `γ` of the joint empirical measures `N⁻¹Σ_j δ_{(q_j,n_j)}` (Mathlib weak convergence of
   probability measures on `ℝ × ℤ`), the monotonicity `(q−q′)(n−n′) ≥ 0` passing to the limit, and the
   structural conclusion `γ(dt,dn) = μ(dt) δ_{n(t)}(dn)` (nonatomicity of `μ`).
3. The kernel limit: off diagonal strips `K_N → (f(t)−f(u))/(t−u)`, the nonatomic diagonal argument, and the
   identity `∫ n(t) f(t) dμ(t) = (L/2π)∫ t f(t) dμ(t) − (κ/2π) ∬ (f(t)−f(u))/(t−u) dμ dμ`.
4. The classical data `μ`, `n(t) = Lt/(2π) − κ Re G_μ(t+i0)/π` (`def:PF-indexed-scalar`), and the realized
   objects DEF-010 (`EmpiricalRapidity`) and DEF-011 (`BornConvergence`) are NOT imported: the weak-limit step
   is stated on deterministic configurations here, and the mapping from the Born law to these empirical
   measures is not part of this module.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace QuantumNLS.LabelJointLimit

/-- On-shell Bethe data for `N` roots: strictly ordered real roots `q`, nondecreasing integer labels `n`, obeying
`QG:eq:our-bethe` with `c = κ/N`. -/
structure OnShellBethe (L κ : ℝ) (N : ℕ) where
  q : Fin N → ℝ
  n : Fin N → ℤ
  q_strict : StrictMono q
  n_mono : Monotone n
  bethe : ∀ j : Fin N,
    L * q j = 2 * Real.pi * (n j : ℝ) +
      2 * ∑ ℓ ∈ Finset.univ.erase j, Real.arctan ((κ / (N : ℝ)) / (q j - q ℓ))

/-- The pairwise kernel `K_N(t,u)` (`eq:B3-weak-kernel`), with `K_N(t,t) = 0`. -/
def pairKernel (κ : ℝ) (N : ℕ) (f : ℝ → ℝ) (t u : ℝ) : ℝ :=
  if t = u then 0 else ((N : ℝ) / κ) * (f t - f u) * Real.arctan (κ / ((N : ℝ) * (t - u)))

/-- `arctan` of the Bethe argument is antisymmetric in the two roots. -/
theorem arctan_antisymm (κ : ℝ) (N : ℕ) (x y : ℝ) (hxy : x ≠ y) :
    Real.arctan ((κ / (N : ℝ)) / (x - y)) = -Real.arctan ((κ / (N : ℝ)) / (y - x)) := by
  rw [← Real.arctan_neg]
  congr 1
  rw [show y - x = -(x - y) by ring, div_neg, neg_neg]

/-- **Finite Bethe pairing identity** (`eq:B3-weak-bethe-identity`), the algebraic core of PROP-002. -/
theorem bethe_pairing_identity {L κ : ℝ} {N : ℕ} (hκ : κ ≠ 0) (hN : 0 < N)
    (B : OnShellBethe L κ N) (f : ℝ → ℝ) :
    (1 / (N : ℝ)) * ∑ j, (B.n j : ℝ) * f (B.q j) =
      (L / (2 * Real.pi)) * ((1 / (N : ℝ)) * ∑ j, B.q j * f (B.q j)) -
        (κ / (2 * Real.pi)) * ((1 / (N : ℝ) ^ 2) *
          ∑ j, ∑ ℓ, pairKernel κ N f (B.q j) (B.q ℓ)) := by
  have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  obtain ⟨A, hA⟩ : ∃ A : Fin N → Fin N → ℝ,
      ∀ j ℓ, A j ℓ = Real.arctan ((κ / (N : ℝ)) / (B.q j - B.q ℓ)) := ⟨_, fun _ _ => rfl⟩
  have hdiag : ∀ j, A j j = 0 := by intro j; rw [hA]; simp
  have hanti : ∀ j ℓ, A j ℓ = -A ℓ j := by
    intro j ℓ
    by_cases h : j = ℓ
    · subst h; rw [hdiag]; simp
    · rw [hA, hA]
      exact arctan_antisymm κ N (B.q j) (B.q ℓ) (B.q_strict.injective.ne h)
  -- the Bethe relation with the full sum (the diagonal term vanishes)
  have hbethe' : ∀ j, L * B.q j = 2 * Real.pi * (B.n j : ℝ) + 2 * ∑ ℓ, A j ℓ := by
    intro j
    rw [B.bethe j, Finset.sum_erase (f := fun ℓ => Real.arctan ((κ / (N : ℝ)) / (B.q j - B.q ℓ)))
      Finset.univ (show Real.arctan ((κ / (N : ℝ)) / (B.q j - B.q j)) = 0 by simp)]
    simp only [hA]
  -- multiply by f(q_j) and sum
  have E1 : ∑ j, L * B.q j * f (B.q j) =
      ∑ j, 2 * Real.pi * (B.n j : ℝ) * f (B.q j) + 2 * ∑ j, ∑ ℓ, A j ℓ * f (B.q j) := by
    have hterm : ∀ j, L * B.q j * f (B.q j) =
        2 * Real.pi * (B.n j : ℝ) * f (B.q j) + 2 * ∑ ℓ, A j ℓ * f (B.q j) := by
      intro j
      rw [hbethe' j, add_mul, mul_assoc 2 (∑ ℓ, A j ℓ) (f (B.q j)), Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, Finset.mul_sum]
  -- symmetrization: the swapped sum is the negative of the original
  have E2 : ∑ j, ∑ ℓ, A j ℓ * f (B.q ℓ) = -∑ j, ∑ ℓ, A j ℓ * f (B.q j) := by
    rw [Finset.sum_comm]
    calc ∑ ℓ, ∑ j, A j ℓ * f (B.q ℓ) = ∑ ℓ, ∑ j, (-A ℓ j) * f (B.q ℓ) :=
          Finset.sum_congr rfl fun ℓ _ => Finset.sum_congr rfl fun j _ => by rw [hanti j ℓ]
      _ = -∑ j, ∑ ℓ, A j ℓ * f (B.q j) := by
          simp only [neg_mul, Finset.sum_neg_distrib]
  -- the kernel identity, termwise
  have E3 : ∀ j ℓ, A j ℓ * (f (B.q j) - f (B.q ℓ)) = (κ / (N : ℝ)) * pairKernel κ N f (B.q j) (B.q ℓ) := by
    intro j ℓ
    by_cases h : j = ℓ
    · subst h; rw [hdiag]; simp [pairKernel]
    · have hne : B.q j ≠ B.q ℓ := B.q_strict.injective.ne h
      unfold pairKernel
      rw [if_neg hne, hA, div_div]
      have hd : B.q j - B.q ℓ ≠ 0 := sub_ne_zero.mpr hne
      field_simp
  have hD : ∑ j, ∑ ℓ, A j ℓ * (f (B.q j) - f (B.q ℓ)) = 2 * ∑ j, ∑ ℓ, A j ℓ * f (B.q j) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [E2]
    ring
  have hK : ∑ j, ∑ ℓ, A j ℓ * (f (B.q j) - f (B.q ℓ)) =
      (κ / (N : ℝ)) * ∑ j, ∑ ℓ, pairKernel κ N f (B.q j) (B.q ℓ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => E3 j ℓ
  have key : L * ∑ j, B.q j * f (B.q j) =
      2 * Real.pi * ∑ j, (B.n j : ℝ) * f (B.q j) +
        (κ / (N : ℝ)) * ∑ j, ∑ ℓ, pairKernel κ N f (B.q j) (B.q ℓ) := by
    have hL : L * ∑ j, B.q j * f (B.q j) = ∑ j, L * B.q j * f (B.q j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have hX : ∑ j, 2 * Real.pi * (B.n j : ℝ) * f (B.q j) = 2 * Real.pi * ∑ j, (B.n j : ℝ) * f (B.q j) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [hL, E1, hX]
    have hS : 2 * ∑ j, ∑ ℓ, A j ℓ * f (B.q j) = (κ / (N : ℝ)) * ∑ j, ∑ ℓ, pairKernel κ N f (B.q j) (B.q ℓ) := by
      rw [← hK, hD]
    rw [hS]
  have key' : (N : ℝ) * (L * ∑ j, B.q j * f (B.q j)) =
      (N : ℝ) * (2 * Real.pi * ∑ j, (B.n j : ℝ) * f (B.q j)) +
        κ * ∑ j, ∑ ℓ, pairKernel κ N f (B.q j) (B.q ℓ) := by
    have h1 : (N : ℝ) * (κ / (N : ℝ)) = κ := by field_simp
    linear_combination (N : ℝ) * key + (∑ j, ∑ ℓ, pairKernel κ N f (B.q j) (B.q ℓ)) * h1
  -- the target follows from `key'` by clearing the denominators `2π N²`
  field_simp
  linear_combination (-1 : ℝ) * key'

end QuantumNLS.LabelJointLimit

/-! Axiom audit. -/
#print axioms QuantumNLS.LabelJointLimit.arctan_antisymm
#print axioms QuantumNLS.LabelJointLimit.bethe_pairing_identity
