import QuantumNLS.LocalSpectralOperator
import QuantumNLS.Fourier
import QuantumNLS.HaarKernelFactorizationSym

set_option autoImplicit false
noncomputable section
open MeasureTheory AddCircle
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.ResetFreeResolventLOCAL001
open QuantumNLS.LocalSpectral

/-- The free graph in the source's parity sector. -/
abbrev freeGraph (L κ : ℝ) (n : ℤ) :=
  LocalSpectral.LuGraph L κ (fun _ => 0) (LocalSpectral.parity n)

/-- The `L²(0,L;ℂ²)` carrier used by the source. -/
abbrev VectorInterval (L : ℝ) := LocalSpectral.H2 L

/-- Equality of source parities forces the mode difference to be even. -/
theorem parity_eq_even_sub {m n : ℤ}
    (h : LocalSpectral.parity m = LocalSpectral.parity n) : Even (m - n) := by
  rcases Int.even_or_odd' m with ⟨a, ha | ha⟩
  · rcases Int.even_or_odd' n with ⟨b, hb | hb⟩
    · change m = 2 * a at ha
      change n = 2 * b at hb
      subst m n
      change ∃ c : ℤ, 2 * a - 2 * b = c + c
      exact ⟨a - b, by ring⟩
    · change m = 2 * a at ha
      change n = 2 * b + 1 at hb
      have hma : Even (2 * a : ℤ) := even_two_mul a
      have hnb : ¬ Even (2 * b + 1 : ℤ) := Int.not_even_two_mul_add_one b
      rw [ha, hb] at h
      simp [LocalSpectral.parity, hma, hnb] at h
  · rcases Int.even_or_odd' n with ⟨b, hb | hb⟩
    · change m = 2 * a + 1 at ha
      change n = 2 * b at hb
      have hma : ¬ Even (2 * a + 1 : ℤ) := Int.not_even_two_mul_add_one a
      have hnb : Even (2 * b : ℤ) := even_two_mul b
      rw [ha, hb] at h
      simp [LocalSpectral.parity, hma, hnb] at h
    · change m = 2 * a + 1 at ha
      change n = 2 * b + 1 at hb
      subst m n
      change ∃ c : ℤ, (2 * a + 1) - (2 * b + 1) = c + c
      exact ⟨a - b, by ring⟩

/-! ### The source spacing and contour denominators -/

/-- The spacing of distinct eigenvalues in one parity sector. -/
def spacing (L : ℝ) : ℝ := 4 * Real.pi / L

/-- The integer shift of the periodic or antiperiodic scalar Fourier lattice. -/
def parityTag (n : ℤ) : ℕ := if Even n then 0 else 1

/-- The unit boundary sign, viewed as a complex scalar. -/
def parityComplex (n : ℤ) : ℂ := (((LocalSpectral.parity n : ℤˣ) : ℤ) : ℂ)

theorem parityComplex_eq_pow (n : ℤ) :
    parityComplex n = (-1 : ℂ) ^ parityTag n := by
  by_cases hn : Even n <;> simp [parityComplex, parityTag, LocalSpectral.parity, hn]

theorem parityComplex_sq (n : ℤ) : parityComplex n * parityComplex n = 1 := by
  rw [parityComplex_eq_pow]
  by_cases hn : Even n <;> simp [parityTag, hn]

theorem deltaR_parityTag (n : ℤ) :
    QuantumNLS.HaarKernelFactorizationSym.deltaR (parityTag n + 1) =
      (parityTag n : ℝ) / 2 := by
  by_cases hn : Even n <;>
    simp [parityTag, QuantumNLS.HaarKernelFactorizationSym.deltaR, hn] <;> norm_num


/-- The squared source constant, with the positive integers represented by `ℕ+`. -/
def resolventConstantSq (L r : ℝ) : ℝ :=
  L⁻¹ * (r⁻¹ ^ 2 + 2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2)

/-- The sharp scalar Fourier-series constant in the source lemma. -/
def resolventConstant (L r : ℝ) : ℝ := Real.sqrt (resolventConstantSq L r)

theorem resolventConstantSq_nonneg {L r : ℝ} (hL : 0 < L) :
    0 ≤ resolventConstantSq L r := by
  unfold resolventConstantSq
  apply mul_nonneg (inv_nonneg.mpr hL.le)
  apply add_nonneg (sq_nonneg _)
  exact mul_nonneg (by norm_num) (tsum_nonneg fun _ => sq_nonneg _)

theorem resolventConstant_sq {L r : ℝ} (hL : 0 < L) :
    resolventConstant L r ^ 2 = L⁻¹ * (r⁻¹ ^ 2 +
      2 * ∑' k : ℕ+, (spacing L * (k : ℝ) - r)⁻¹ ^ 2) := by
  rw [resolventConstant, Real.sq_sqrt (resolventConstantSq_nonneg hL),
    resolventConstantSq]

theorem spacing_pos {L : ℝ} (hL : 0 < L) : 0 < spacing L := by
  unfold spacing
  positivity

theorem spacing_gt_two_mul {L r : ℝ} (hsmall : r < spacing L / 2) :
    2 * r < spacing L := by linarith

/-- Advancing the mode number by two adds exactly one sector spacing. -/
theorem pm_even_shift {L : ℝ} (n k : ℤ) :
    (pm L (n + 2 * k) : ℂ) = (pm L n : ℂ) + (spacing L * k : ℝ) := by
  unfold pm spacing
  push_cast
  field_simp
  ring


/-- The source's ordered free modes are the two `LocalSpectral.chi` vectors. -/
abbrev chi_mj (L : ℝ) (m : ℤ) (j : Fin 2) : VectorInterval L :=
  LocalSpectral.chi L m j

/-- The free eigenfunction and eigenvalue are the source modes `χ_{m,j}` and `p_m`. -/
theorem chi_free_eigen {L : ℝ} (hL : 0 < L) (κ : ℝ) (m : ℤ) (j : Fin 2) :
    (LocalSpectral.chi L m j, (LocalSpectral.pm L m : ℂ) • LocalSpectral.chi L m j) ∈
      freeGraph L κ m := by
  exact LocalSpectral.free_eigen hL κ m j

/-- The source mode `χ_{m,j}` has precisely the parity `(-1)^m`. -/
theorem chi_has_parity {L : ℝ} (hL : 0 < L) (m : ℤ) (j : Fin 2) :
    LocalSpectral.chi L m j ∈ LocalSpectral.domain L (LocalSpectral.parity m) :=
  LocalSpectral.chi_mem_domain hL m j

#print axioms chi_free_eigen
#print axioms chi_has_parity
#print axioms pm_even_shift

end QuantumNLS.ResetFreeResolventLOCAL001
