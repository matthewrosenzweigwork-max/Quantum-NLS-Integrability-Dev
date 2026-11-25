import QuantumNLS.Ext005PairBounds
import QuantumNLS.IntrinsicContact

/-! Physical two-particle contraction on each completed bosonic sector.
The full Fock-space form and its time dependence are separate obligations. -/
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace
namespace QuantumNLS.Ext005PairSector
open QuantumNLS.TensorCarrier QuantumNLS.PhysicalTensor
open QuantumNLS.BetheCoefficientTransform QuantumNLS.IntrinsicContact
variable {L : ℝ} [Fact (0 < L)]

/-- Contract the first two tensor factors with the physical two-particle kernel,
then project the remaining factors onto the bosonic sector. -/
def contraction (b : HN L 2) (n : ℕ) : HN L (2 + n) →L[ℂ] HN L n :=
  (physSector L n).orthogonalProjectionOnto ∘L
    contractL (F := HilbertTensorPower ℂ (L2T L) n) (b : HilbertTensorPower ℂ (L2T L) 2) ∘L
    (splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n).toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (physSector L (2 + n)).subtypeL

/-- The two-particle annihilation block, with the bosonic normalization. -/
def annihilation (b : HN L 2) (n : ℕ) : HN L (2 + n) →L[ℂ] HN L n :=
  (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) : ℂ) • contraction b n

/-- Creation is the Hilbert-space adjoint of physical annihilation. -/
def creation (b : HN L 2) (n : ℕ) : HN L n →L[ℂ] HN L (2 + n) :=
  (annihilation b n).adjoint

theorem contraction_bound (b : HN L 2) (n : ℕ) (x : HN L (2 + n)) :
    ‖contraction b n x‖ ≤ ‖b‖ * ‖x‖ := by
  unfold contraction
  simp only [ContinuousLinearMap.comp_apply]
  calc
    _ ≤ ‖contractL (F := HilbertTensorPower ℂ (L2T L) n)
      (b : HilbertTensorPower ℂ (L2T L) 2)
      (splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n x)‖ :=
      Submodule.norm_orthogonalProjectionOnto_apply_le _ _
    _ ≤ ‖contractL (F := HilbertTensorPower ℂ (L2T L) n)
      (b : HilbertTensorPower ℂ (L2T L) 2)‖ *
      ‖splitIsometry (𝕜 := ℂ) (E := L2T L) 2 n x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖b‖ * ‖x‖ := by
      have h : ‖contractL (F := HilbertTensorPower ℂ (L2T L) n)
          (b : HilbertTensorPower ℂ (L2T L) 2)‖ ≤ ‖b‖ := by
        rw [contractL, ContinuousLinearMap.adjoint.norm_map]
        apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
        intro y
        simp [htmulR_apply, norm_htmul]
      simpa using mul_le_mul_of_nonneg_right h (norm_nonneg x)

theorem annihilation_bound (b : HN L 2) (n : ℕ) (x : HN L (2 + n)) :
    ‖annihilation b n x‖ ≤
      ‖b‖ * Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x‖ := by
  simp only [annihilation, smul_apply, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := contraction_bound b n x
  nlinarith [Real.sqrt_nonneg (((n : ℝ) + 1) * ((n : ℝ) + 2)), norm_nonneg b]

/-- Sector matrix element of the physical annihilation block. -/
def pairTerm (b : HN L 2) (x : QuantumNLS.Ext005Moments.momentDomain (L := L) 1)
    (n : ℕ) : ℂ := ⟪x.val n, annihilation b n (x.val (2 + n))⟫_ℂ

/-- The annihilation form is the convergent sum of the physical sector blocks. -/
def pairForm (b : HN L 2) (x : QuantumNLS.Ext005Moments.momentDomain (L := L) 1) : ℂ :=
  ∑' n, pairTerm b x n

/-- The physical sector construction discharges the previously conditional
pair-block estimate, and the full annihilation form obeys the first-moment bound. -/
theorem pairForm_bound (b : HN L 2)
    (x : QuantumNLS.Ext005Moments.momentDomain (L := L) 1) :
    Summable (pairTerm b x) ∧
      ‖pairForm b x‖ ≤ ‖b‖ * ‖QuantumNLS.Ext005Moments.momentRoot 1 x‖ ^ 2 := by
  apply QuantumNLS.Ext005PairBounds.physical_pair_form_of_sector_bound x
    (pairTerm b x) ‖b‖ (norm_nonneg b)
  intro n
  calc
    ‖pairTerm b x n‖ ≤ ‖x.val n‖ * ‖annihilation b n (x.val (2 + n))‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖x.val n‖ * (‖b‖ * Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) *
        ‖x.val (2 + n)‖) :=
      mul_le_mul_of_nonneg_left (annihilation_bound b n _) (norm_nonneg _)
    _ = ‖b‖ * (Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) *
        ‖x.val n‖ * ‖x.val (n + 2)‖) := by rw [Nat.add_comm 2 n]; ring

/-- The adjoint block has the same norm bound as annihilation. -/
theorem creation_bound (b : HN L 2) (n : ℕ) (x : HN L n) :
    ‖creation b n x‖ ≤
      ‖b‖ * Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) * ‖x‖ := by
  have h : ‖annihilation b n‖ ≤
      ‖b‖ * Real.sqrt (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    exact annihilation_bound b n y
  calc
    ‖creation b n x‖ ≤ ‖creation b n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖annihilation b n‖ * ‖x‖ := by rw [creation, ContinuousLinearMap.adjoint.norm_map]
    _ ≤ _ := mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- The diagonal pair Hamiltonian form, adding creation to annihilation. -/
def pairHamiltonian (b : HN L 2)
    (x : QuantumNLS.Ext005Moments.momentDomain (L := L) 1) : ℂ :=
  pairForm b x + star (pairForm b x)

theorem pairHamiltonian_real (b : HN L 2)
    (x : QuantumNLS.Ext005Moments.momentDomain (L := L) 1) :
    (pairHamiltonian b x).im = 0 := by
  simp [pairHamiltonian]

theorem pairHamiltonian_bound (b : HN L 2)
    (x : QuantumNLS.Ext005Moments.momentDomain (L := L) 1) :
    ‖pairHamiltonian b x‖ ≤ 2 * ‖b‖ * ‖QuantumNLS.Ext005Moments.momentRoot 1 x‖ ^ 2 := by
  have h := (pairForm_bound b x).2
  calc
    ‖pairHamiltonian b x‖ ≤ ‖pairForm b x‖ + ‖star (pairForm b x)‖ := norm_add_le _ _
    _ = 2 * ‖pairForm b x‖ := by simp; ring
    _ ≤ _ := by nlinarith

#print axioms QuantumNLS.Ext005PairSector.creation_bound
#print axioms QuantumNLS.Ext005PairSector.pairHamiltonian_real
#print axioms QuantumNLS.Ext005PairSector.pairHamiltonian_bound
#print axioms QuantumNLS.Ext005PairSector.pairForm_bound
#print axioms QuantumNLS.Ext005PairSector.contraction_bound
#print axioms QuantumNLS.Ext005PairSector.annihilation_bound
end QuantumNLS.Ext005PairSector
