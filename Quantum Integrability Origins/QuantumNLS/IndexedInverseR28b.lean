import QuantumNLS.LOCAL009R23Final
import QuantumNLS.KernelFactorialBound

/-! LOCAL-016: the larger inverse disk and the ordered-kernel estimate on
all source tubes. These are quantitative ingredients, not a period claim. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Complex Set Metric Filter Topology
open scoped Nat
namespace QuantumNLS.IndexedInverseR28b
open Ext025A7 LOCAL009R22Geometry
variable {L κ : ℝ} [Fact (0 < L)]

def tube (L : ℝ) (n : ℤ) : Set ℂ :=
  band (2*Real.pi*n/L) (Real.pi/(2*L))

def W (κ : ℝ) : ℝ := 1/(1000*κ)
def rstar : ℝ := 3/8000

theorem W_pos (hκ : 0 < κ) : 0 < W κ := by unfold W; positivity

theorem W_small (hκ : 0 < κ) : κ*W κ = 1/1000 := by
  unfold W
  field_simp [hκ.ne']

theorem exp_abs_tube (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    Real.exp (L*|z.im|) < 8 := by
  have hL : 0 < L := Fact.out
  have hi := (le_max_right _ _).trans_lt hz.2
  have hib : L*|z.im| < 2 := by
    have h1 := mul_lt_mul_of_pos_right hi hL
    have h2 : 9*(Real.pi/(2*L))/8*L = 9*Real.pi/16 := by field_simp; ring
    rw [h2] at h1
    nlinarith [Real.pi_lt_d2]
  have he := Real.exp_one_lt_d9
  have hepos := Real.exp_pos 1
  have heq : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [show (2 : ℝ) = 1+1 by norm_num,Real.exp_add]
  have hexp2 : Real.exp 2 < 8 := by rw [heq]; nlinarith
  exact (Real.exp_lt_exp.mpr hib).trans hexp2

/-- The precise printed factorial bound, uniform in label and real part. -/
theorem ordered_kernel_bound (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) (p : ℕ) :
    ‖NormalizedTransfer.orderedKernel L p z‖ ≤ 16*L^p/(p.factorial : ℝ) := by
  have hL : 0 < L := Fact.out
  have hf : ((p.factorial : ℕ) : ℝ)^2 ≤ (((2*p).factorial : ℕ) : ℝ) := by
    have hh := Nat.le_of_dvd (Nat.factorial_pos (p+p))
      (Nat.factorial_mul_factorial_dvd_factorial_add p p)
    have hh' : p.factorial*p.factorial ≤ (2*p).factorial := by simpa [two_mul] using hh
    rw [pow_two]
    exact_mod_cast hh'
  have hs : (p.factorial : ℝ) ≤ Real.sqrt (((2*p).factorial : ℕ) : ℝ) :=
    Real.le_sqrt_of_sq_le hf
  have hp : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
  have he := (exp_abs_tube n hz).le
  have hk := KernelFactorialBound.norm_physicalKernel_le_fact (L := L) p z
  change ‖NormalizedTransfer.orderedKernel L p z‖ ≤ _ at hk
  unfold KernelFactorialBound.hsConst at hk
  calc
    _ ≤ 2*(Real.exp (L*|z.im|)*L^p/Real.sqrt (((2*p).factorial : ℕ) : ℝ)) := hk
    _ ≤ 2*(8*L^p/(p.factorial : ℝ)) := by gcongr
    _ = _ := by ring

/-- The source target radius 3/8000 fits the larger inverse disk. -/
theorem target_margin (hκ : 0 < κ) (n : ℤ) {z y : ℂ}
    (hz : z ∈ tube L n) (hy : ‖y-spectralMap κ L z 0‖ < rstar) :
    ‖y-spectralMap κ L z 0‖ < 3/4*‖spectralLinear κ L z‖*W κ := by
  have hg := source_gap_bound (Fact.out : 0 < L) n hz
  have hD : κ/2 ≤ ‖spectralLinear κ L z‖ := by
    rw [spectralLinear_norm,abs_of_pos hκ]
    nlinarith
  have hw := W_pos hκ
  have he : 3/4*(κ/2)*W κ = rstar := by
    unfold W rstar
    field_simp [hκ.ne']
    ring
  exact hy.trans_le (by rw [← he]; gcongr)

/-- Unique inverse, joint analyticity and full scalar derivative on the
larger source disk. Every quantitative premise is proved on the source tube. -/
theorem inverse_disk (hκ : 0 < κ) (n : ℤ) {z y : ℂ}
    (hz : z ∈ tube L n) (hy : ‖y-spectralMap κ L z 0‖ < rstar) :
    spectralInverse κ L (W κ) z y ∈ ball (0 : ℂ) (W κ) ∧
    spectralMap κ L z (spectralInverse κ L (W κ) z y) = y ∧
    (∀ w ∈ closedBall (0 : ℂ) (W κ), spectralMap κ L z w = y →
      w = spectralInverse κ L (W κ) z y) ∧
    AnalyticAt ℂ (fun p : ℂ × ℂ => spectralInverse κ L (W κ) p.1 p.2) (z,y) ∧
    HasDerivAt (spectralInverse κ L (W κ) z)
      (spectralDerivative κ L z (spectralInverse κ L (W κ) z y))⁻¹ y := by
  have hh := local009_application κ L hκ (W_pos hκ) (W_small hκ).le
    (band_open _ _) (fun v hv => source_phase_bound (Fact.out : 0 < L) n hv)
    (fun v hv => source_gap_bound (Fact.out : 0 < L) n hv) hz (target_margin hκ n hz hy)
  exact ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩

theorem inverse_center (hκ : 0 < κ) (n : ℤ) {z : ℂ} (hz : z ∈ tube L n) :
    spectralInverse κ L (W κ) z (spectralMap κ L z 0) = 0 := by
  exact local009_inverse_center κ L hκ (W_pos hκ) (W_small hκ).le
    (band_open _ _) (fun v hv => source_phase_bound (Fact.out : 0 < L) n hv)
    (fun v hv => source_gap_bound (Fact.out : 0 < L) n hv) hz

end QuantumNLS.IndexedInverseR28b
#print axioms QuantumNLS.IndexedInverseR28b.ordered_kernel_bound
#print axioms QuantumNLS.IndexedInverseR28b.inverse_disk
#print axioms QuantumNLS.IndexedInverseR28b.inverse_center
