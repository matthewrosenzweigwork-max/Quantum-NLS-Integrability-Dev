import QuantumNLS.Local005ContourB
import QuantumNLS.Local005ComponentsB

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ENNReal
open Complex
namespace QuantumNLS.Local005
open QuantumNLS.ResetFreeResolventLOCAL001

/-- The two potential matrix entries have opposite phases and the same modulus. -/
def slotPhase (L κ : ℝ) (j : Fin 2) : ℂ :=
  if j = 0 then 2 * I * (Real.sqrt (κ / L) : ℂ)
  else -(2 * I * (Real.sqrt (κ / L) : ℂ))

theorem slotPhase_norm (L κ : ℝ) (j : Fin 2) :
    ‖slotPhase L κ j‖ = 2 * Real.sqrt (κ / L) := by
  by_cases hj : j = 0 <;> simp [slotPhase, hj, norm_mul, Real.sqrt_nonneg]

/-- Exact integrated complex path coefficient. Inputs in conjugated slots
are independent variables on the complexification. -/
def pathCoefficient (L r κ : ℝ) (kind : WordKind) {k : ℕ} (j : Fin 2)
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) : ℂ :=
  (∏ t : Fin k, slotPhase L κ (componentAfter t.val j)) *
    (∏ t : Fin k, u t (QuantumNLS.ResolventWordCoefficientLOCAL005.wordLabel n q t)) *
      contourScalar L r kind n q

theorem pathCoefficient_norm (L r κ : ℝ) (kind : WordKind) {k : ℕ} (j : Fin 2)
    (u : Fin k → ℤ → ℂ) (n : ℤ) (q : Fin (k - 1) → ℤ) :
    ‖pathCoefficient L r κ kind j u n q‖ = contourAbsTerm L r κ kind u n q := by
  simp [pathCoefficient, norm_mul, norm_prod, slotPhase_norm, contourAbsTerm, amplitude]

/-- The integrated Fourier path series, with its component support. -/
def coefficientEntry (L r κ : ℝ) (kind : WordKind) (k : ℕ)
    (u : Fin k → ℤ → ℂ) (n : ℤ) (i j : Fin 2) : ℂ :=
  if i = componentAfter k j then
    ∑' q : Fin (k - 1) → ℤ, pathCoefficient L r κ kind j u n q else 0

/-- Absolute convergence, hence the norm of each integrated entry is bounded by its majorant. -/
theorem coefficient_converges {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < spacing L / 2) (κ : ℝ) (kind : WordKind) {k : ℕ}
    (u : Fin k → ℤ → ℂ) (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2)
    (n : ℤ) (i j : Fin 2) :
    Summable (fun q : Fin (k - 1) → ℤ => ‖pathCoefficient L r κ kind j u n q‖) ∧
      ‖coefficientEntry L r κ kind k u n i j‖ ≤ contourMajorant L r κ kind k u n := by
  have hd := contour_majorant_data hL hr hsmall κ kind u hu n
  have hs : Summable (fun q : Fin (k - 1) → ℤ => ‖pathCoefficient L r κ kind j u n q‖) := by
    simpa only [pathCoefficient_norm] using hd.1
  refine ⟨hs, ?_⟩
  unfold coefficientEntry
  split_ifs
  · simpa only [pathCoefficient_norm, contourMajorant] using norm_tsum_le_tsum_norm hs
  · simpa using hd.2.1

/-- Odd words have no diagonal coefficient. -/
theorem coefficient_odd {k : ℕ} (hk : Odd k) (L r κ : ℝ) (kind : WordKind)
    (u : Fin k → ℤ → ℂ) (n : ℤ) (j : Fin 2) :
    coefficientEntry L r κ kind k u n j j = 0 := by
  simp [coefficientEntry, Ne.symm (componentAfter_odd hk j)]

/-- Even words have no off-diagonal coefficient. -/
theorem coefficient_even {k : ℕ} (hk : Even k) (L r κ : ℝ) (kind : WordKind)
    (u : Fin k → ℤ → ℂ) (n : ℤ) (i j : Fin 2) (hij : i ≠ j) :
    coefficientEntry L r κ kind k u n i j = 0 := by
  simp [coefficientEntry, componentAfter_even hk j, hij]

/-- Code arbitrary countable paths by naturals, retaining every nonnegative term. -/
def codedTerm {α : Type*} [Encodable α] (a : α → ℝ≥0∞) (N : ℕ) : ℝ≥0∞ :=
  ∑' q : α, if Encodable.encode q = N then a q else 0

/-- The authorized GP-11 is applied to the actual coded nonnegative path sum. -/
theorem path_monotone_convergence {α : Type*} [Encodable α] (a : α → ℝ≥0∞) :
    ∑' q : α, a q = ⨆ N, ∑ i ∈ Finset.range N, codedTerm a i := by
  rw [← QuantumNLS.ResolventWordGP11LOCAL005.nonnegativeWordTruncations]
  unfold codedTerm
  rw [ENNReal.tsum_comm]
  simp

/-- GP-11 identifies the absolute integrated word with its increasing finite truncations. -/
theorem contour_monotone_convergence {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hsmall : r < QuantumNLS.ResetFreeResolventLOCAL001.spacing L / 2) (κ : ℝ)
    (kind : WordKind) {k : ℕ} (u : Fin k → ℤ → ℂ)
    (hu : ∀ j, Summable fun m => ‖u j m‖ ^ 2) (n : ℤ) :
    ENNReal.ofReal (contourMajorant L r κ kind k u n) =
      ⨆ N, ∑ i ∈ Finset.range N,
        codedTerm (fun q : Fin (k - 1) → ℤ => ENNReal.ofReal (contourAbsTerm L r κ kind u n q)) i := by
  rw [contourMajorant, ENNReal.ofReal_tsum_of_nonneg
    (contourAbsTerm_nonneg L r κ kind u n)
    (contour_majorant_data hL hr hsmall κ kind u hu n).1]
  exact path_monotone_convergence _

#print axioms pathCoefficient_norm
#print axioms coefficient_converges
#print axioms coefficient_odd
#print axioms coefficient_even
#print axioms path_monotone_convergence
#print axioms contour_monotone_convergence
end QuantumNLS.Local005
