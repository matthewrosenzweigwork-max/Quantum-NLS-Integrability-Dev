import NlsGge.Analysis.ComplexHilbertSchmidtBasisChange

/-!
The complex Hilbert–Schmidt energy is defined using an internally chosen Hilbert
basis. We prove that it agrees with every supplied basis and every matrix-energy
sum. Finiteness is checked in extended nonnegative reals before the real norm
is used; totalized toReal/sqrt is not a claim of a finite norm for non-HS maps.
This is NEW-F02.06 infrastructure, not the concrete DVD estimate.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal InnerProduct InnerProductSpace
namespace NlsGge.Pilot

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- An internal choice, with no basis hypothesis imposed on the operator. -/
def chosenComplexHilbertBasisIndex : Set E :=
  Classical.choose (exists_hilbertBasis ℂ E)

def chosenComplexHilbertBasis :
    HilbertBasis (chosenComplexHilbertBasisIndex (E := E)) ℂ E :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ E))

def complexHilbertSchmidtEnergy (T : E →L[ℂ] F) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (‖T (chosenComplexHilbertBasis i)‖ ^ 2)

def IsComplexHilbertSchmidt (T : E →L[ℂ] F) : Prop :=
  complexHilbertSchmidtEnergy T ≠ ∞

def complexHilbertSchmidtNorm (T : E →L[ℂ] F) : ℝ :=
  Real.sqrt (complexHilbertSchmidtEnergy T).toReal

theorem complexHilbertSchmidtEnergy_eq_basis {ι : Type*}
    (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E) :
    complexHilbertSchmidtEnergy T =
      ∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2) := by
  exact complex_ennreal_source_basis_energy_eq T chosenComplexHilbertBasis b
    chosenComplexHilbertBasis

theorem complexHilbertSchmidtEnergy_eq_matrix {ι κ : Type*}
    (T : E →L[ℂ] F) (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F) :
    complexHilbertSchmidtEnergy T =
      ∑' i : ι, ∑' k : κ, ENNReal.ofReal (‖⟪d k, T (b i)⟫_ℂ‖ ^ 2) := by
  rw [complexHilbertSchmidtEnergy_eq_basis T b]
  apply tsum_congr
  intro i
  exact (ennreal_tsum_complex_norm_sq_inner_of_hilbertBasis d (T (b i))).symm

theorem isComplexHilbertSchmidt_of_summable_basis {ι : Type*}
    {T : E →L[ℂ] F} (b : HilbertBasis ι ℂ E)
    (hb : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    IsComplexHilbertSchmidt T := by
  unfold IsComplexHilbertSchmidt
  rw [complexHilbertSchmidtEnergy_eq_basis T b]
  exact hb.tsum_ofReal_ne_top

theorem complexHilbertSchmidtNorm_eq_basis {ι : Type*}
    {T : E →L[ℂ] F} (b : HilbertBasis ι ℂ E)
    (hb : Summable (fun i : ι => ‖T (b i)‖ ^ 2)) :
    complexHilbertSchmidtNorm T = Real.sqrt (∑' i : ι, ‖T (b i)‖ ^ 2) := by
  unfold complexHilbertSchmidtNorm
  rw [complexHilbertSchmidtEnergy_eq_basis T b,
    ← ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hb,
    ENNReal.toReal_ofReal (tsum_nonneg (fun i => sq_nonneg _))]

theorem isComplexHilbertSchmidt_of_energy_le {T : E →L[ℂ] F} {K : ℝ}
    (h : complexHilbertSchmidtEnergy T ≤ ENNReal.ofReal K) :
    IsComplexHilbertSchmidt T := by
  exact ne_of_lt (lt_of_le_of_lt h ENNReal.ofReal_lt_top)

theorem complexHilbertSchmidtNorm_le_of_energy_le {T : E →L[ℂ] F} {R : ℝ}
    (hR : 0 ≤ R)
    (h : complexHilbertSchmidtEnergy T ≤ ENNReal.ofReal (R ^ 2)) :
    complexHilbertSchmidtNorm T ≤ R := by
  have hreal : (complexHilbertSchmidtEnergy T).toReal ≤ R ^ 2 := by
    have hm := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    simpa only [ENNReal.toReal_ofReal (sq_nonneg R)] using hm
  exact (Real.sqrt_le_sqrt hreal).trans_eq (Real.sqrt_sq hR)

end NlsGge.Pilot
