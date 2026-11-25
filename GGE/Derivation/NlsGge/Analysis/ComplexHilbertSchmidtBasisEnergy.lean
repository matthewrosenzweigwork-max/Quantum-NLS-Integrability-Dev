import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
NEW-F02.06 prerequisite: genuine complex Hilbert basis Parseval and rectangular
extended-real basis energy. This develops the basis-independent Hilbert–Schmidt
bridge needed for the concrete DVD operator; it does not identify physical Dirac
domains, assert the numerical DVD bound, or close NEW-F02. No real/complex factor
of two is absorbed into a definition. Every energy is nonnegative extended-real.
-/

set_option autoImplicit false
open scoped BigOperators ENNReal InnerProduct InnerProductSpace

noncomputable section

namespace NlsGge.Pilot

/-- Complex Parseval with real squared norms, valid without a countability assumption. -/
theorem hasSum_complex_norm_sq_inner_of_hilbertBasis
    {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i : ι => ‖⟪b i, x⟫_ℂ‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (b.repr x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply,
    LinearIsometryEquiv.norm_map] using h

theorem ennreal_tsum_complex_norm_sq_inner_of_hilbertBasis
    {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : HilbertBasis ι ℂ E) (x : E) :
    ∑' i : ι, ENNReal.ofReal (‖⟪b i, x⟫_ℂ‖ ^ 2) =
      ENNReal.ofReal (‖x‖ ^ 2) := by
  let h := hasSum_complex_norm_sq_inner_of_hilbertBasis b x
  calc
    ∑' i : ι, ENNReal.ofReal (‖⟪b i, x⟫_ℂ‖ ^ 2) =
        ENNReal.ofReal (∑' i : ι, ‖⟪b i, x⟫_ℂ‖ ^ 2) := by
      symm
      exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable
    _ = ENNReal.ofReal (‖x‖ ^ 2) := by rw [h.tsum_eq]

theorem complex_ennreal_basis_energy_eq_adjoint_basis
    {E F ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (d : HilbertBasis κ ℂ F) :
    ∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2) =
      ∑' k : κ, ENNReal.ofReal (‖(T†) (d k)‖ ^ 2) := by
  calc
    ∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2) =
        ∑' i : ι, ∑' k : κ,
          ENNReal.ofReal (‖⟪d k, T (b i)⟫_ℂ‖ ^ 2) := by
      apply tsum_congr
      intro i
      exact (ennreal_tsum_complex_norm_sq_inner_of_hilbertBasis d (T (b i))).symm
    _ = ∑' k : κ, ∑' i : ι,
          ENNReal.ofReal (‖⟪d k, T (b i)⟫_ℂ‖ ^ 2) := by
      exact ENNReal.tsum_comm
    _ = ∑' k : κ, ENNReal.ofReal (‖(T†) (d k)‖ ^ 2) := by
      apply tsum_congr
      intro k
      calc
        ∑' i : ι, ENNReal.ofReal (‖⟪d k, T (b i)⟫_ℂ‖ ^ 2) =
            ∑' i : ι, ENNReal.ofReal
              (‖⟪b i, (T†) (d k)⟫_ℂ‖ ^ 2) := by
          apply tsum_congr
          intro i
          have hcoeff : ‖⟪d k, T (b i)⟫_ℂ‖ = ‖⟪b i, (T†) (d k)⟫_ℂ‖ := by
            calc
              ‖⟪d k, T (b i)⟫_ℂ‖ = ‖⟪(T†) (d k), b i⟫_ℂ‖ := by
                rw [ContinuousLinearMap.adjoint_inner_left]
              _ = ‖⟪b i, (T†) (d k)⟫_ℂ‖ := norm_inner_symm _ _
          exact congrArg ENNReal.ofReal (congrArg (fun r : ℝ => r ^ 2) hcoeff)
        _ = ENNReal.ofReal (‖(T†) (d k)‖ ^ 2) :=
          ennreal_tsum_complex_norm_sq_inner_of_hilbertBasis b ((T†) (d k))

theorem complex_ennreal_source_basis_energy_eq
    {E F ι κ η : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F)
    (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (d : HilbertBasis η ℂ F) :
    ∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2) =
      ∑' j : κ, ENNReal.ofReal (‖T (c j)‖ ^ 2) := by
  calc
    ∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2) =
        ∑' k : η, ENNReal.ofReal (‖(T†) (d k)‖ ^ 2) :=
      complex_ennreal_basis_energy_eq_adjoint_basis T b d
    _ = ∑' j : κ, ENNReal.ofReal (‖T (c j)‖ ^ 2) :=
      (complex_ennreal_basis_energy_eq_adjoint_basis T c d).symm

end NlsGge.Pilot
