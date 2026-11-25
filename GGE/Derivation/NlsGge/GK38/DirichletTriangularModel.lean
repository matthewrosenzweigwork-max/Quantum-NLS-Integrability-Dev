import NlsGge.GK38.DirichletTriangularCalc
import NlsGge.GK38.Lib.EntireProductsC34a

/-! # D1: the concrete triangular double-root model

A single shift replaces the free zero root by a second occurrence of pi.
The exact physical characteristic is identified with that convergent model
product before its analytic order and canonical label positions are computed. -/
set_option autoImplicit false
open Filter Topology SummationFilter Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

def dirichletTriangleShift38 : Lib.L2Seq := (Real.pi : ℂ) • lp.single 2 0 (1 : ℂ)
def dirichletTriangleSeq38 : ℤ → ℂ := Lib.sigmaOf dirichletTriangleShift38

theorem dirichlet_triangle_seq_eq38 (n : ℤ) :
    dirichletTriangleSeq38 n = if n = 0 then (Real.pi : ℂ) else countingCenter38 n := by
  change (n : ℂ) * (Real.pi : ℂ) +
    (Real.pi : ℂ) * (lp.single (E := fun _ : ℤ => ℂ) 2 (0 : ℤ) (1 : ℂ) n) = _
  by_cases hn : n = 0 <;> simp [lp.single_apply, Pi.single_apply, hn, countingCenter38]

theorem dirichlet_triangle_seq_summable38 :
    Summable (fun n : ℤ => ‖dirichletTriangleSeq38 n - (n : ℂ) * (Real.pi : ℂ)‖ ^ 2) :=
  Lib.summable_dev_sigmaOf dirichletTriangleShift38

/-- This model product comes from the independent triangular matrix calculation, not muSeq. -/
theorem dirichlet_triangle_model_product38 (z : ℂ) :
    -(∏'[symmetricIcc ℤ] m : ℤ, (dirichletTriangleSeq38 m - z) / (πn m : ℂ)) =
      dirichletChar (constL2 (2 * (Real.pi : ℂ)), 0) z := by
  have homit : Lib.omitProd 0 dirichletTriangleShift38 z = Lib.sincAt 0 z := by
    have hs : dirichletTriangleShift38 = (0 : Lib.L2Seq) +
        (Real.pi : ℂ) • lp.single 2 0 (1 : ℂ) := by simp [dirichletTriangleShift38]
    rw [hs, Lib.omitProd_add_single, Lib.omitProd_zero_eq_sincAt]
  have hnormal : -(∏'[symmetricIcc ℤ] m : ℤ, (dirichletTriangleSeq38 m - z) / (πn m : ℂ)) =
      (z - (Real.pi : ℂ)) * Lib.sincAt 0 z := by
    change -(∏'[symmetricIcc ℤ] m : ℤ, Lib.prodFactor (Lib.sigmaOf dirichletTriangleShift38) z m) = _
    rw [Lib.entProd_eq_mul_omitProd 0 dirichletTriangleShift38 z, homit]
    have hsigma : Lib.sigmaOf dirichletTriangleShift38 0 = (Real.pi : ℂ) := by
      simpa [dirichletTriangleSeq38] using dirichlet_triangle_seq_eq38 0
    rw [hsigma]
    ring
  rw [hnormal]
  by_cases hz : z = 0
  · subst z
    rw [dirichlet_triangle_zero38]
    simp [Lib.sincAt]
    ring
  · rw [dirichlet_triangle_nonzero38 _ _ hz]
    simp only [Lib.sincAt, Int.cast_zero, zero_mul, ite_eq_right hz, sub_zero]
    field_simp [hz]

theorem dirichlet_triangle_model_order38 (w : ℂ) :
    analyticOrderAt (dirichletChar (constL2 (2 * (Real.pi : ℂ)), 0)) w =
      Set.encard {n : ℤ | dirichletTriangleSeq38 n = w} := by
  have he : dirichletChar (constL2 (2 * (Real.pi : ℂ)), 0) =
      -(fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ, (dirichletTriangleSeq38 m - z) / (πn m : ℂ)) :=
    funext (fun z => (dirichlet_triangle_model_product38 z).symm)
  rw [he, analyticOrderAt_neg]
  exact (Lib.product_entire dirichletTriangleSeq38 dirichlet_triangle_seq_summable38).2.2 w

/-- The model enumerates the actual triangular characteristic with every analytic occurrence. -/
theorem dirichlet_triangle_model_enumeration38 :
    RootEnumeration38 (dirichletChar (constL2 (2 * (Real.pi : ℂ)), 0)) dirichletTriangleSeq38 := by
  have hroot (n : ℤ) : dirichletChar (constL2 (2 * (Real.pi : ℂ)), 0) (dirichletTriangleSeq38 n) = 0 := by
    rw [dirichlet_triangle_seq_eq38]
    by_cases hn : n = 0
    · rw [ite_eq_left hn, dirichlet_triangle_nonzero38 _ _ (by exact_mod_cast Real.pi_ne_zero)]
      simp
    · rw [ite_eq_right hn]
      have hz : countingCenter38 n ≠ 0 := by
        intro hz
        have he : countingCenter38 n = countingCenter38 0 := by simpa [countingCenter38] using hz
        exact hn (countingCenter_injective38 he)
      rw [dirichlet_triangle_nonzero38 _ _ hz]
      simp [countingCenter38, Complex.sin_int_mul_pi]
  have hocc (z : ℂ) : {n : ℤ | dirichletTriangleSeq38 n = z}.Finite ∧
      Set.encard {n : ℤ | dirichletTriangleSeq38 n = z} =
        analyticOrderAt (dirichletChar (constL2 (2 * (Real.pi : ℂ)), 0)) z :=
    ⟨Lib.finite_roots dirichlet_triangle_seq_summable38 z, (dirichlet_triangle_model_order38 z).symm⟩
  refine ⟨hroot, ?_, hocc⟩
  intro z
  constructor
  · intro hz
    have hne : {n : ℤ | dirichletTriangleSeq38 n = z} ≠ ∅ := by
      intro he
      have ho := (hocc z).2
      rw [he, Set.encard_empty] at ho
      exact (analyticOnNhd_dirichletChar_z _ z (mem_univ _)).analyticOrderAt_eq_zero.mp ho.symm hz
    exact Set.nonempty_iff_ne_empty.mpr hne
  · rintro ⟨n, hn⟩
    simpa only [hn] using hroot n

theorem dirichlet_triangle_model_mono38 {i j : ℤ} (hij : i ≤ j) :
    complexLexLE38 (dirichletTriangleSeq38 i) (dirichletTriangleSeq38 j) := by
  have he (n : ℤ) : dirichletTriangleSeq38 n = countingCenter38 (if n = 0 then 1 else n) := by
    rw [dirichlet_triangle_seq_eq38]
    by_cases hn : n = 0 <;> simp [hn, countingCenter38]
  rw [he i, he j]
  apply countingCenter_lex_mono38
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hi, hj, ↓reduceIte] <;> omega

/-- On any certified central window, sorted canonical muSeq agrees with the actual model. -/
theorem dirichlet_triangle_central_labels38 {N : ℕ}
    (h : RootCountingAt38 (dirichletChar (constL2 (2 * (Real.pi : ℂ)), 0)) 1 N)
    (n : ℤ) (hn : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)) :
    muSeq (constL2 (2 * (Real.pi : ℂ)), 0) n = dirichletTriangleSeq38 n := by
  have hmap : (Finset.Icc (-(N : ℤ)) (N : ℤ)).val.map dirichletTriangleSeq38 =
      Lib.zeroMultiset (dirichletChar (constL2 (2 * (Real.pi : ℂ)), 0)) (ball (0 : ℂ) (countingRadius38 N)) := by
    apply rootEnumeration_window_multiset38 h dirichlet_triangle_model_enumeration38
    intro k
    rw [dirichlet_triangle_seq_eq38]
    by_cases hk : k = 0
    · subst k
      rw [ite_eq_left rfl]
      have hmem : (Real.pi : ℂ) ∈ ball (0 : ℂ) (countingRadius38 N) := by
        have hc := countingCenter_mem_central_iff38 N 1
        have hp := h.1
        have hh : |(1 : ℤ)| ≤ (N : ℤ) := by norm_num; omega
        simpa [countingCenter38] using hc.mpr hh
      simpa only [Finset.mem_Icc] using (iff_of_true hmem (by constructor <;> omega))
    · rw [ite_eq_right hk, countingCenter_mem_central_iff38, Finset.mem_Icc]
      exact abs_le
  rw [muSeq_eq_candidate38 _ h]
  apply integerWindow_unique38 _ dirichletTriangleSeq38
    (fun i j hij => criticalCandidate_mono38 h hij)
    (fun _ _ hij => dirichlet_triangle_model_mono38 hij) (-(N : ℤ)) (N : ℤ) _ hn
  rw [criticalCandidate_central_multiset38 h, hmap]

end
end NlsGge.GK38
