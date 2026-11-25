import NlsGge.Schur.FreeDomainPointwise
import NlsGge.Analysis.H1Fourier

/-! NEW-F02.02: the actual proper free domain implies the H1 coefficient
sum with weight 1+m², retaining both components and the zero frequency.
This is an input to continuous trace reconstruction, not yet weak-domain iff. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal
namespace NlsGge.Schur

lemma freeWeightedCoordinates_norm_sq (n : ℤ) (x : SectorSquare n)
    (i : Bool × Sector n) :
    ‖freeWeightedCoordinates n x i‖ ^ 2 =
      Real.pi ^ 2 * ((i.2.val : ℝ) ^ 2 * ‖x i‖ ^ 2) := by
  simp only [freeWeightedCoordinates, spectralCenter, norm_mul,
    Complex.norm_intCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_pow, sq_abs]
  ring

lemma freeDomain_frequency_sq_summable (n : ℤ) (x : SectorSquare n)
    (hx : x ∈ freeWeightedDomainPointwise n) :
    Summable (fun i : Bool × Sector n => (i.2.val : ℝ) ^ 2 * ‖x i‖ ^ 2) := by
  have hd : Summable (fun i => ‖freeWeightedCoordinates n x i‖ ^ 2) := by
    simpa using (show Memℓp (freeWeightedCoordinates n x) 2 from hx).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have h := hd.mul_left ((Real.pi ^ 2)⁻¹)
  apply h.congr
  intro i
  rw [freeWeightedCoordinates_norm_sq]
  field_simp [ne_of_gt Real.pi_pos]

lemma freeDomain_h1_coefficients_summable (n : ℤ) (x : SectorSquare n)
    (hx : x ∈ freeWeightedDomainPointwise n) :
    Summable (fun i : Bool × Sector n =>
      (1 + (i.2.val : ℝ) ^ 2) * ‖x i‖ ^ 2) := by
  have hu : Summable (fun i => ‖x i‖ ^ 2) := by
    simpa using (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  apply (hu.add (freeDomain_frequency_sq_summable n x hx)).congr
  intro i
  ring

lemma freeDomain_component_h1_coefficients_summable
    (n : ℤ) (x : SectorSquare n) (hx : x ∈ freeWeightedDomainPointwise n)
    (upper : Bool) :
    Summable (fun m : Sector n => (1 + (m.val : ℝ) ^ 2) * ‖x (upper,m)‖ ^ 2) := by
  have hinj : Function.Injective (fun m : Sector n => (upper,m)) := by
    intro a b hab
    exact congrArg Prod.snd hab
  have hs := freeDomain_h1_coefficients_summable n x hx
  have ht : Summable ((fun i : Bool × Sector n =>
      (1 + (i.2.val : ℝ) ^ 2) * ‖x i‖ ^ 2) ∘
        (fun m : Sector n => (upper,m))) := hs.comp_injective hinj
  exact ht

end NlsGge.Schur
