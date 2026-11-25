import QuantumNLS.TerraMultiRound45Iterates
import Mathlib.Combinatorics.Enumerative.Catalan.Tree

/-! Ordered Riccati tree terms and their individual Sobolev bounds.
This checkpoint does not yet sum the trees or prove REG-007. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound45Trees
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound38SignedPicard

/-- A nil tree is a leaf; each node inserts the physical nonlinear operation. -/
def treeTerm {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (hY : 0 < |Y|)
    (κ : ℝ) (u : Ell2) : BinaryTree Unit → Ell2
  | .nil => signedCLM L Y hY u
  | .node _ left right =>
      -((κ / L : ℂ) • signedCLM L Y hY
        (mulBil hL ha (jEll u) (mulBil hL ha
          (treeTerm hL ha hY κ u left) (treeTerm hL ha hY κ u right))))

/-- A single ordered tree has one free-resolvent factor per vertex and
one field factor at each leaf or internal vertex. -/
theorem tree_term_bound {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u : Ell2) (t : BinaryTree Unit) :
    ‖treeTerm hL ha hY κ u t‖ ≤
      (‖u‖ * |Y|⁻¹) *
      (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) ^ t.numNodes := by
  have hc : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hy : 0 ≤ |Y|⁻¹ := inv_nonneg.mpr hY.le
  have hq : 0 ≤ |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2 := by positivity
  induction t with
  | nil =>
      simpa [treeTerm, BinaryTree.numNodes, mul_comm] using norm_signedCLM_le L Y hY u
  | node v l r ihl ihr =>
      have hbil := norm_mulBil_le hL ha (jEll u)
        (mulBil hL ha (treeTerm hL ha hY κ u l) (treeTerm hL ha hY κ u r))
      have hinner := norm_mulBil_le hL ha (treeTerm hL ha hY κ u l)
        (treeTerm hL ha hY κ u r)
      have hres := norm_signedCLM_le L Y hY
        (mulBil hL ha (jEll u) (mulBil hL ha
          (treeTerm hL ha hY κ u l) (treeTerm hL ha hY κ u r)))
      have hb : ‖treeTerm hL ha hY κ u (.node v l r)‖ ≤
          (|κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖) *
            (‖treeTerm hL ha hY κ u l‖ * ‖treeTerm hL ha hY κ u r‖) := by
        simp only [treeTerm, norm_neg, norm_smul, ← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs]
        rw [norm_jEll] at hbil
        calc
          _ ≤ |κ / L| * (|Y|⁻¹ * ‖mulBil hL ha (jEll u) (mulBil hL ha
              (treeTerm hL ha hY κ u l) (treeTerm hL ha hY κ u r))‖) := by gcongr
          _ ≤ |κ / L| * (|Y|⁻¹ * (Cmul L a * ‖u‖ * (Cmul L a *
              (‖treeTerm hL ha hY κ u l‖ * ‖treeTerm hL ha hY κ u r‖)))) := by
                gcongr
                exact hbil.trans (by gcongr; simpa only [mul_assoc] using hinner)
          _ = _ := by ring
      calc
        _ ≤ (|κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖) *
            (‖treeTerm hL ha hY κ u l‖ * ‖treeTerm hL ha hY κ u r‖) := hb
        _ ≤ (|κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖) *
            (((‖u‖ * |Y|⁻¹) * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) ^ l.numNodes) *
             ((‖u‖ * |Y|⁻¹) * (|κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 2 * |Y|⁻¹ ^ 2) ^ r.numNodes)) := by
              gcongr
        _ = _ := by simp only [BinaryTree.numNodes, pow_add, pow_succ]; ring

#print axioms tree_term_bound
end QuantumNLS.TerraMultiRound45Trees
