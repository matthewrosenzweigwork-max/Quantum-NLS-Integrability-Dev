import QuantumNLS.Fourier
import QuantumNLS.PhysicalTensor

/-!
# DEF-001 `def:report-1`: the physical torus, Hilbert space and Fourier normalization (realization)

Source (`source/chapters/definitions.tex`, `def:report-1`): `T_L = ℝ/Lℤ` with Lebesgue measure of mass `L`; the
Hilbert space `L²(T_L;ℂ)` with `⟨f,g⟩ = ∫₀ᴸ conj f · g` linear in the second variable; orthonormal Fourier functions
`e_n(x) = L^{-1/2} e^{2πinx/L}`; Fourier coefficient `û(n) = ⟨e_n,u⟩`.

Each clause is proved from the repository objects: `AddCircle L` with `volume` (`Fourier`, `PhysicalTensor`), the Lp
carrier `L2T L`, `Fourier.mode` (`e_n`), `Fourier.modeLp` (`e_n` as an `L²` class), `Fourier.coeff` (`û`), and
`Fourier.fourierL2` (the unitary onto `ℓ²(ℤ)`).

Proved here (standard axioms only):
* `clause_mass`: `volume (T_L) = L`.
* `clause_inner`: `⟨f,g⟩ = ∫₀ᴸ conj(f x) g x` (interval form); `clause_linear_second`, `clause_conj_linear_first`: the convention.
* `coeff_eq_inner`: `û(n) = ⟨e_n, u⟩` for `u ∈ L²`.
* `clause_orthonormal`: `⟨e_n, e_m⟩ = δ_{nm}`.
* `clause_complete`: `u ⊥ every e_n ⇒ u = 0`.
* `clause_basis`: a Hilbert basis indexed by `ℤ` with `b n = e_n`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.DEF001Realization

open QuantumNLS.Fourier QuantumNLS.PhysicalTensor

variable (L : ℝ) [Fact (0 < L)]

/-- Clause (mass): the torus `ℝ/Lℤ` has Lebesgue measure of total mass `L`. -/
theorem clause_mass : (volume : Measure (AddCircle L)) Set.univ = ENNReal.ofReal L :=
  QuantumNLS.Fourier.torus_mass L

/-- Clause (inner product): `⟨f,g⟩ = ∫₀ᴸ conj f · g`. -/
theorem clause_inner (f g : L2T L) :
    ⟪f, g⟫_ℂ = ∫ x in (0 : ℝ)..L, (starRingEnd ℂ) (f (x : AddCircle L)) * g (x : AddCircle L) :=
  inner_L2T L f g

/-- Clause (convention): linear in the second variable. -/
theorem clause_linear_second (f g : L2T L) (c : ℂ) : ⟪f, c • g⟫_ℂ = c * ⟪f, g⟫_ℂ := by
  rw [inner_smul_right]

/-- Clause (convention): conjugate-linear in the first variable. -/
theorem clause_conj_linear_first (f g : L2T L) (c : ℂ) :
    ⟪c • f, g⟫_ℂ = (starRingEnd ℂ) c * ⟪f, g⟫_ℂ := by
  rw [inner_smul_left]

/-- Clause (coefficient): `û(n) = ⟨e_n, u⟩`, for `u ∈ L²`. -/
theorem coeff_eq_inner (u : L2T L) (n : ℤ) :
    coeff L (u : AddCircle L → ℂ) n = ⟪modeLp L n, u⟫_ℂ := by
  unfold coeff
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coeFn_modeLp L n] with x hx
  simp [hx, RCLike.inner_apply, mul_comm]

/-- Clause (orthonormality): `⟨e_n, e_m⟩ = δ_{nm}`. -/
theorem clause_orthonormal (n m : ℤ) : ⟪modeLp L n, modeLp L m⟫_ℂ = if n = m then 1 else 0 := by
  rw [← coeff_eq_inner L (modeLp L m) n, ← fourierL2_apply L (modeLp L m) n, fourierL2_modeLp L m,
    lp.single_apply]
  simp [Pi.single_apply]

/-- Clause (completeness): a vector orthogonal to every `e_n` is zero. -/
theorem clause_complete (u : L2T L) (h : ∀ n : ℤ, ⟪modeLp L n, u⟫_ℂ = 0) : u = 0 := by
  have hf : fourierL2 L u = 0 := by
    ext n
    rw [fourierL2_apply L u n, coeff_eq_inner L u n, h n]
    simp
  exact (fourierL2 L).map_eq_zero_iff.mp hf

theorem orthonormal_modeLp : Orthonormal ℂ (modeLp L) := by
  rw [orthonormal_iff_ite]
  intro i j
  exact clause_orthonormal L i j

theorem orthogonal_span_eq_bot : (Submodule.span ℂ (Set.range (modeLp L)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  apply clause_complete L x
  intro n
  exact (Submodule.mem_orthogonal _ _).1 hx (modeLp L n) (Submodule.subset_span ⟨n, rfl⟩)

/-- The physical Hilbert basis `(e_n)_{n∈ℤ}` of `L²(T_L)` (DEF-001). -/
def physicalBasis : HilbertBasis ℤ ℂ (L2T L) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_modeLp L) (orthogonal_span_eq_bot L)

/-- Clause (basis): the Hilbert basis is `e_n`. -/
theorem clause_basis (n : ℤ) : physicalBasis L n = modeLp L n := by
  unfold physicalBasis
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]

end QuantumNLS.DEF001Realization

#print axioms QuantumNLS.DEF001Realization.clause_mass
#print axioms QuantumNLS.DEF001Realization.clause_inner
#print axioms QuantumNLS.DEF001Realization.coeff_eq_inner
#print axioms QuantumNLS.DEF001Realization.clause_orthonormal
#print axioms QuantumNLS.DEF001Realization.clause_complete
#print axioms QuantumNLS.DEF001Realization.clause_basis
