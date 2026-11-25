import Mathlib
import NlsGge.Atomic.G1.G1004
import NlsGge.Atomic.Volterra
import NlsGge.GK38.PairPotential
import NlsGge.Atomic.G1.G1005

/- G1-010 pre-approval proof candidate 01 (proof development).  Statement verbatim from proof development's
   G1-010_COMMAND01.  Route: write M(t) = E(t) A(t) with A = 1 + K, K the primitive of the integrable
   kernel k = E(-s) Φ̃(s) M(s) (as in G1-005); the entries of A are absolutely continuous, K' = k a.e.
   (Lebesgue differentiation), and k = B A with B off-diagonal, so (det A)' = 0 a.e.; det A is
   constant (AC + zero derivative a.e.), equal to 1 at 0, and det M = det E * det A = det A.
   Invertibility of M is never assumed.  G1-005 content is copied as private lemmas. -/

set_option autoImplicit false

open MeasureTheory Filter Topology Set NlsGge.Atomic.Volterra NlsGge.GK38 NlsGge.SpectralFoundations
  NlsGge.Atomic.G1004GenT

open NlsGge.Atomic.G1005 NlsGge.Atomic.G1005Aux

namespace NlsGge.Atomic.G1010

noncomputable section

/-! ### Copied from G1-005 (private) -/

def kerEnt (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) (s : ℝ) : ℂ :=
  (freeE z (-s) * potCoeff38 φ s * ext38T hT (fundContT φ z hT) s) i j

/-- Its primitive. -/
def Kint (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) (t : ℝ) : ℂ :=
  ∫ s in (0 : ℝ)..t, kerEnt φ z hT i j s

/-- `A = 1 + K`. -/
def Aent (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) (t : ℝ) : ℂ :=
  (if i = j then 1 else 0) + Kint φ z hT i j t

theorem kerEnt_integrable (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    IntervalIntegrable (kerEnt φ z hT i j) volume 0 T := by
  have hKc : Continuous fun s : ℝ => freeE z (-s) := (continuous_freeE z).comp continuous_neg
  exact intervalIntegrable_triple_entryT φ hT hKc (continuous_ext38T hT _) i j

theorem Aent_ac (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t => Aent φ z hT i j t) 0 T := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => (if i = j then (1 : ℂ) else 0)) 0 T :=
    (contDiff_const.contDiffOn (s := Set.uIcc (0 : ℝ) T) (n := 1)).absolutelyContinuousOnInterval
  exact hc.add (ac_primitive_complex (kerEnt_integrable φ z hT i j))

theorem Aent_zero (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (i j : Fin 2) :
    Aent φ z hT i j 0 = if i = j then 1 else 0 := by
  simp [Aent, Kint]

theorem freeE_diag (z : ℂ) (t : ℝ) (i j : Fin 2) :
    freeE z t i j = freeE z t i i * (if i = j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> simp [freeE]

theorem Mf_eq (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (i j : Fin 2) :
    ext38T hT (fundContT φ z hT) t i j = freeE z t i i * Aent φ z hT i j t := by
  rw [ext38T_of_mem hT _ ht, fundContT_entry_eq φ z hT ht i j]
  have h1 := congrArg (fun X : PairMat38 => X i j) (volterraFunT_eq φ z hT (fundContT φ z hT) t)
  simp only [volterraFunT_apply, freeE_mul_apply] at h1
  rw [h1, freeE_diag z t i j, Aent, mul_add]
  rfl

theorem ker_rows (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ b2 b3 : ℂ, (∀ j : Fin 2, kerEnt φ z hT 0 j t = b2 * Aent φ z hT 1 j t) ∧
      (∀ j : Fin 2, kerEnt φ z hT 1 j t = b3 * Aent φ z hT 0 j t) := by
  refine ⟨freeE z (-t) 0 0 * (Complex.I * potRepFst38 φ t) * freeE z t 1 1,
    freeE z (-t) 1 1 * (-(Complex.I * potRepSnd38 φ t)) * freeE z t 0 0, fun j => ?_, fun j => ?_⟩
  · simp only [kerEnt, Matrix.mul_apply, Fin.sum_univ_two, Mf_eq φ z hT ht]
    simp [freeE, potCoeff38]
    ring
  · simp only [kerEnt, Matrix.mul_apply, Fin.sum_univ_two, Mf_eq φ z hT ht]
    simp [freeE, potCoeff38]
    ring

/-- The determinant of `A`. -/
def detA (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : ℂ :=
  Aent φ z hT 0 0 t * Aent φ z hT 1 1 t - Aent φ z hT 0 1 t * Aent φ z hT 1 0 t

theorem detA_ac (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval (fun t => detA φ z hT t) 0 T := by
  have h := ((Aent_ac φ z hT 0 0).fun_smul (Aent_ac φ z hT 1 1)).sub
    ((Aent_ac φ z hT 0 1).fun_smul (Aent_ac φ z hT 1 0))
  refine h.congr ?_
  intro t _
  simp [detA, smul_eq_mul]

theorem detA_deriv_zero (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t : ℝ, t ∈ Set.uIcc 0 T → HasDerivAt (fun t => detA φ z hT t) 0 t := by
  have hae : ∀ᵐ t : ℝ, t ∈ Set.uIcc 0 T → ∀ i j : Fin 2,
      HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, kerEnt φ z hT i j s) (kerEnt φ z hT i j t) t := by
    have h : ∀ i j : Fin 2, ∀ᵐ t : ℝ, t ∈ Set.uIcc 0 T →
        HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, kerEnt φ z hT i j s) (kerEnt φ z hT i j t) t := by
      intro i j
      filter_upwards [(kerEnt_integrable φ z hT i j).ae_hasDerivAt_integral] with t ht htm
      exact ht htm 0 left_mem_uIcc
    have h' := ae_all_iff.2 fun i : Fin 2 => ae_all_iff.2 fun j : Fin 2 => h i j
    filter_upwards [h'] with t ht htm i j using ht i j htm
  filter_upwards [hae] with t ht htm
  have htI : t ∈ Set.Icc (0 : ℝ) T := by rwa [Set.uIcc_of_le hT] at htm
  have hA : ∀ i j : Fin 2, HasDerivAt (fun x => Aent φ z hT i j x) (kerEnt φ z hT i j t) t := by
    intro i j
    have := (hasDerivAt_const t (if i = j then (1 : ℂ) else 0)).add (ht htm i j)
    rw [zero_add] at this
    exact this
  obtain ⟨b2, b3, h2, h3⟩ := ker_rows φ z hT htI
  have hd := ((hA 0 0).mul (hA 1 1)).sub ((hA 0 1).mul (hA 1 0))
  have hv : kerEnt φ z hT 0 0 t * Aent φ z hT 1 1 t + Aent φ z hT 0 0 t * kerEnt φ z hT 1 1 t -
      (kerEnt φ z hT 0 1 t * Aent φ z hT 1 0 t + Aent φ z hT 0 1 t * kerEnt φ z hT 1 0 t) = 0 := by
    rw [h2 0, h2 1, h3 0, h3 1]
    ring
  rw [hv] at hd
  exact hd

theorem detA_eq_one (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    detA φ z hT T = 1 := by
  obtain ⟨C, hC⟩ := (detA_ac φ z hT).const_of_ae_hasDerivAt_zero (detA_deriv_zero φ z hT)
  have h0 : detA φ z hT 0 = 1 := by
    simp [detA, Aent_zero]
  have hT' : T ∈ Set.uIcc (0 : ℝ) T := right_mem_uIcc
  rw [hC T hT', ← hC 0 left_mem_uIcc, h0]

theorem G1010_det (φ : PotPair) (z : ℂ) {T : ℝ} (hT : 0 ≤ T) :
    Matrix.det (∑' n : ℕ, potentialVolterraTerm38 φ z n T) = 1 := by
  have hT' : T ∈ Set.Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  rw [tsum_matrix φ z hT hT', Matrix.det_fin_two]
  simp only [Mf_eq φ z hT hT']
  have hE : freeE z T 0 0 * freeE z T 1 1 = 1 := by
    simp only [freeE, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [← Complex.exp_add]
    simp
  have hdet := detA_eq_one φ z hT
  unfold detA at hdet
  calc freeE z T 0 0 * Aent φ z hT 0 0 T * (freeE z T 1 1 * Aent φ z hT 1 1 T) -
        freeE z T 0 0 * Aent φ z hT 0 1 T * (freeE z T 1 1 * Aent φ z hT 1 0 T)
      = (freeE z T 0 0 * freeE z T 1 1) *
        (Aent φ z hT 0 0 T * Aent φ z hT 1 1 T - Aent φ z hT 0 1 T * Aent φ z hT 1 0 T) := by ring
    _ = 1 := by rw [hE, hdet, one_mul]

theorem G1010_whole :
    ((∀ (φ : PotPair) (z : ℂ) (t : ℝ), 0 ≤ t →
      Matrix.det (∑' n : ℕ, potentialVolterraTerm38 φ z n t) = 1) : Prop) :=
  fun φ z _ ht => G1010_det φ z ht

end

end NlsGge.Atomic.G1010

