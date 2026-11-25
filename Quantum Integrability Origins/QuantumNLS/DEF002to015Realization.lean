import QuantumNLS.Fourier
import QuantumNLS.FullMass
import QuantumNLS.PhysicalTensor
import QuantumNLS.SymplecticBracket

/-!
# DEF-002, DEF-003, DEF-004, DEF-015: clause-by-clause realization (bindings to existing objects)

Source: `source/chapters/definitions.tex`: `def:report-2` (DEF-002, line 13), `def:report-3` (DEF-003, line 19),
`def:report-4` (DEF-004, line 25), `def:report-15` (DEF-015, line 91). Each clause is either a definitional identity
(`rfl`) or a lemma from the repository's existing realization. The existing modules realizing each clause are listed
in the clause comments; clauses without an existing realization are listed at the end of the module.

Proved here (standard axioms only): the bindings below.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace QuantumNLS.DEF002to015Realization

open QuantumNLS.PhysicalTensor (L2T)

variable {L : ℝ} [Fact (0 < L)]

/-! ## DEF-002 (Sobolev and weighted sequence spaces) -/

/-- Clause: the weight `(1+|2πn/L|)^{2s}`. Realized by `Fourier.sobolevWeight`. -/
theorem clause_weight (s : ℝ) (n : ℤ) :
    QuantumNLS.Fourier.sobolevWeight L s n = (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (2 * s) := rfl

/-- Clause: `h^s(ℤ)` is the sequences with finite weighted square sum. Realized by `Fourier.MemHs`. -/
theorem clause_hs_seq (s : ℝ) (x : ℤ → ℂ) :
    QuantumNLS.Fourier.MemHs L s x ↔
      Summable (fun n : ℤ => (1 + |2 * Real.pi * (n : ℝ) / L|) ^ (2 * s) * ‖x n‖ ^ 2) := Iff.rfl

/-- Clause: `H^s(T_L)` is the `L²` fields whose weighted sum over the orthonormal coefficients `û(n)` is finite.
Realized by `Fourier.MemHsField`. -/
theorem clause_hs_field (s : ℝ) (u : AddCircle L → ℂ) :
    QuantumNLS.Fourier.MemHsField L s u ↔
      MemLp u 2 (volume : Measure (AddCircle L)) ∧ QuantumNLS.Fourier.MemHs L s (QuantumNLS.Fourier.coeff L u) :=
  Iff.rfl

/-- Clause: the DEF-002 squared norm, computed in `ℓ²` through the unitary `fourierL2`. Realized by
`Fourier.hsNormSq_fourierL2`. -/
theorem clause_norm_via_l2 (s : ℝ) (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    QuantumNLS.Fourier.hsNormSq L s (fun n => QuantumNLS.Fourier.fourierL2 L u n) =
      QuantumNLS.Fourier.hsFieldNormSq L s (u : AddCircle L → ℂ) :=
  QuantumNLS.Fourier.hsNormSq_fourierL2 L s u

/-- Clause: `H^s` membership is `h^s` membership of the `ℓ²` coefficients. Realized by `Fourier.memHs_fourierL2_iff`. -/
theorem clause_hs_iff_l2 (s : ℝ) (u : Lp ℂ 2 (volume : Measure (AddCircle L))) :
    QuantumNLS.Fourier.MemHsField L s (u : AddCircle L → ℂ) ↔
      QuantumNLS.Fourier.MemHs L s (fun n => QuantumNLS.Fourier.fourierL2 L u n) :=
  QuantumNLS.Fourier.memHs_fourierL2_iff L s u

/-! ## DEF-003 (Mass and normalized product preparation) -/

/-- Clause: the physical mass `m = ‖u‖²` is the total mass of `M_{κ,u}` (`FullMass.Mmeas_univ`). -/
theorem clause_total_mass (κ : ℝ) (u : L2T L) :
    QuantumNLS.FullMass.Mmeas κ u Set.univ = ENNReal.ofReal (‖u‖ ^ 2) :=
  QuantumNLS.FullMass.Mmeas_univ κ u

/-- Clause: the unit field `u/√m` (for `m > 0`) is `FullMass.unitDir u` and has norm one. -/
theorem clause_unit_field (u : L2T L) (h : u ≠ 0) :
    ‖QuantumNLS.FullMass.unitDir u‖ = 1 :=
  QuantumNLS.FullMass.norm_unitDir h

/-- Clause: `u/√m = unitDir u` for `m = ‖u‖²`. -/
theorem clause_unit_field_div_sqrt (u : L2T L) :
    QuantumNLS.FullMass.unitDir u = ((Real.sqrt (‖u‖ ^ 2))⁻¹ : ℝ) • u := by
  unfold QuantumNLS.FullMass.unitDir
  rw [Real.sqrt_sq (norm_nonneg u)]
  rfl

/-- Clause: the measure at `u = 0` is zero. Realized by `FullMass.Mmeas_zero`. -/
theorem clause_zero_measure (κ : ℝ) : QuantumNLS.FullMass.Mmeas κ (0 : L2T L) = 0 :=
  QuantumNLS.FullMass.Mmeas_zero κ

/-- Clause: for `u ≠ 0`, the measure is `m μ_{κm, u/√m}` (coupling `κm`). Realized by `FullMass.Mmeas_of_ne`. -/
theorem clause_scaled_measure (κ : ℝ) {u : L2T L} (h : u ≠ 0) :
    QuantumNLS.FullMass.Mmeas κ u = ENNReal.ofReal (‖u‖ ^ 2) •
      (QuantumNLS.FreeLimit.muKappa (QuantumNLS.FullMass.unitDir u)
        (QuantumNLS.FullMass.norm_unitDir h) (κ * ‖u‖ ^ 2) : Measure ℝ) :=
  QuantumNLS.FullMass.Mmeas_of_ne κ h

/-- Clause: the normalized bosonic product `u^{⊗N}` of a unit field has norm one. Realized by
`TensorCarrier.htpow` and `TensorCarrier.norm_htpow`. -/
theorem clause_normalized_product (N : ℕ) (u : L2T L) (h : u ≠ 0) :
    ‖(QuantumNLS.TensorCarrier.htpow N (QuantumNLS.FullMass.unitDir u) : QuantumNLS.TensorCarrier.HilbertTensorPower ℂ (L2T L) N)‖ = 1 := by
  rw [QuantumNLS.TensorCarrier.norm_htpow, QuantumNLS.FullMass.norm_unitDir h, one_pow]

/-! ## DEF-004 (Bosonic sector and symmetric projection) -/

/-- Clause: `H_N = Sym^N L²(T_L)`. Realized by `PhysicalTensor.physSector` (an `abbrev` of `SymSector`). -/
theorem clause_sector (N : ℕ) :
    QuantumNLS.PhysicalTensor.physSector L N =
      QuantumNLS.TensorCarrier.SymSector ℂ (QuantumNLS.PhysicalTensor.L2T L) N := rfl

/-- Clause: `P_N` is the orthogonal projection onto `H_N`, and equals the average of the `N!` permutations.
Realized by `PhysicalTensor.physSymProj_eq`. -/
theorem clause_projection (N : ℕ) :
    QuantumNLS.TensorCarrier.symProj ℂ (QuantumNLS.PhysicalTensor.L2T L) N =
        (QuantumNLS.PhysicalTensor.physSector L N).starProjection ∧
      QuantumNLS.TensorCarrier.symProj ℂ (QuantumNLS.PhysicalTensor.L2T L) N =
        ((N.factorial : ℂ)⁻¹) • ∑ σ : Equiv.Perm (Fin N),
          (QuantumNLS.TensorCarrier.permRep ℂ (QuantumNLS.PhysicalTensor.L2T L) N σ :
            QuantumNLS.TensorCarrier.HilbertTensorPower ℂ (QuantumNLS.PhysicalTensor.L2T L) N →L[ℂ] _) :=
  QuantumNLS.PhysicalTensor.physSymProj_eq L N

/-- Clause: the zero-particle sector is `ℂ`. Realized by `PhysicalTensor.physZeroSector`. -/
theorem clause_zero_sector :
    QuantumNLS.PhysicalTensor.physSector L 0 = ⊤ ∧
      Nonempty (QuantumNLS.TensorCarrier.HilbertTensorPower ℂ (QuantumNLS.PhysicalTensor.L2T L) 0 ≃ₗᵢ[ℂ] ℂ) :=
  QuantumNLS.PhysicalTensor.physZeroSector L

/-! ## DEF-015 (Physical symplectic form and Poisson bracket) -/

section DEF015

attribute [local instance] InnerProductSpace.complexToReal

open QuantumNLS.SymplecticBracket

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Clause: `Ω(h,k) = 2 Im⟨h,k⟩`. Realized by `SymplecticBracket.omega` (definitional). -/
theorem clause_omega (h k : H) : omega h k = 2 * (inner ℂ h k).im := rfl

/-- Clause: `dF(u)[h] = 2 Re⟨∇F(u),h⟩`. Realized by `SymplecticBracket.fderiv_eq_two_inner_gradient` and
`real_inner_eq_re_inner`. -/
theorem clause_dF (F : H → ℝ) (u h : H) : fderiv ℝ F u h = 2 * (inner ℂ (SymplecticBracket.gradient F u) h).re := by
  rw [fderiv_eq_two_inner_gradient, real_inner_eq_re_inner ℂ]
  rfl

/-- Clause: `X_F = −i∇F`. Realized by `SymplecticBracket.hamField` (definitional). -/
theorem clause_hamField (F : H → ℝ) (u : H) : hamField F u = (-Complex.I) • SymplecticBracket.gradient F u := rfl

/-- Clause: the real bracket `{F,G} = dF[X_G]`. Realized by `SymplecticBracket.pbR` (definitional). -/
theorem clause_pbR (F G : H → ℝ) (u : H) : pbR F G u = fderiv ℝ F u (hamField G u) := rfl

/-- Clause: complex brackets extended complex bilinearly. Realized by `SymplecticBracket.pbC` (definitional
expansion in real and imaginary parts). -/
theorem clause_pbC (F G : H → ℂ) (u : H) :
    pbC F G u = ⟨pbR (fun v => (F v).re) (fun v => (G v).re) u - pbR (fun v => (F v).im) (fun v => (G v).im) u,
      pbR (fun v => (F v).im) (fun v => (G v).re) u + pbR (fun v => (F v).re) (fun v => (G v).im) u⟩ := rfl

/-- Clause: a single complex coordinate has bracket `{z, z̄} = −i`. Realized by `SymplecticBracket.pbC_coord_conj_phys`
(for the coordinate `⟨e,·⟩` of a unit vector `e` of the physical space). -/
theorem clause_coordinate_bracket {e : L2T L} (he : ‖e‖ = 1) (u : L2T L) :
    pbC (fun v : L2T L => inner ℂ e v) (fun v => (starRingEnd ℂ) (inner ℂ e v)) u = -Complex.I :=
  pbC_coord_conj_phys L he u

end DEF015

end QuantumNLS.DEF002to015Realization

#print axioms QuantumNLS.DEF002to015Realization.clause_hs_iff_l2
#print axioms QuantumNLS.DEF002to015Realization.clause_unit_field_div_sqrt
#print axioms QuantumNLS.DEF002to015Realization.clause_projection
#print axioms QuantumNLS.DEF002to015Realization.clause_zero_sector
#print axioms QuantumNLS.DEF002to015Realization.clause_dF
#print axioms QuantumNLS.DEF002to015Realization.clause_coordinate_bracket
