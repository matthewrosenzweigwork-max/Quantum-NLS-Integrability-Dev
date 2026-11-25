import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
Bounded prerequisite: an ENNReal basis-energy identity for a real rectangular
continuous linear map. This is not the real summability/HasSum theorem and
does not claim a Hilbert–Schmidt predicate or a concrete CM identification.
-/

set_option autoImplicit false
open scoped BigOperators InnerProduct InnerProductSpace

noncomputable section

namespace NlsGge.Pilot

theorem hasSum_real_sq_inner_of_hilbertBasis
    {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : HilbertBasis ι ℝ E) (x : E) :
    HasSum (fun i : ι => (⟪b i, x⟫_ℝ) ^ 2) (‖x‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner x x
  convert h using 1
  · ext i
    rw [real_inner_comm (b i) x]
    ring
  · rw [real_inner_self_eq_norm_sq]

theorem ennreal_tsum_sq_inner_of_hilbertBasis
    {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : HilbertBasis ι ℝ E) (x : E) :
    ∑' i : ι, ENNReal.ofReal ((⟪b i, x⟫_ℝ) ^ 2) =
      ENNReal.ofReal (‖x‖ ^ 2) := by
  let h := hasSum_real_sq_inner_of_hilbertBasis b x
  calc
    ∑' i : ι, ENNReal.ofReal ((⟪b i, x⟫_ℝ) ^ 2) =
        ENNReal.ofReal (∑' i : ι, (⟪b i, x⟫_ℝ) ^ 2) := by
      symm
      exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) h.summable
    _ = ENNReal.ofReal (‖x‖ ^ 2) := by rw [h.tsum_eq]

theorem ennreal_basis_energy_eq_adjoint_basis
    {E F ι κ : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F)
    (b : HilbertBasis ι ℝ E) (d : HilbertBasis κ ℝ F) :
    ∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2) =
      ∑' k : κ, ENNReal.ofReal (‖(T†) (d k)‖ ^ 2) := by
  calc
    ∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2) =
        ∑' i : ι, ∑' k : κ,
          ENNReal.ofReal ((⟪d k, T (b i)⟫_ℝ) ^ 2) := by
      apply tsum_congr
      intro i
      exact (ennreal_tsum_sq_inner_of_hilbertBasis d (T (b i))).symm
    _ = ∑' k : κ, ∑' i : ι,
          ENNReal.ofReal ((⟪d k, T (b i)⟫_ℝ) ^ 2) := by
      exact ENNReal.tsum_comm
    _ = ∑' k : κ, ENNReal.ofReal (‖(T†) (d k)‖ ^ 2) := by
      apply tsum_congr
      intro k
      calc
        ∑' i : ι, ENNReal.ofReal ((⟪d k, T (b i)⟫_ℝ) ^ 2) =
            ∑' i : ι, ENNReal.ofReal
              ((⟪b i, (T†) (d k)⟫_ℝ) ^ 2) := by
          apply tsum_congr
          intro i
          have hcoeff : ⟪d k, T (b i)⟫_ℝ = ⟪b i, (T†) (d k)⟫_ℝ := by
            calc
              ⟪d k, T (b i)⟫_ℝ = ⟪(T†) (d k), b i⟫_ℝ := by
                exact (ContinuousLinearMap.adjoint_inner_left T (b i) (d k)).symm
              _ = ⟪b i, (T†) (d k)⟫_ℝ :=
                (real_inner_comm ((T†) (d k)) (b i)).symm
          exact congrArg ENNReal.ofReal (congrArg (fun r : ℝ => r ^ 2) hcoeff)
        _ = ENNReal.ofReal (‖(T†) (d k)‖ ^ 2) :=
          ennreal_tsum_sq_inner_of_hilbertBasis b ((T†) (d k))

theorem ennreal_source_basis_energy_eq
    {E F ι κ η : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F)
    (b : HilbertBasis ι ℝ E) (c : HilbertBasis κ ℝ E)
    (d : HilbertBasis η ℝ F) :
    ∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2) =
      ∑' j : κ, ENNReal.ofReal (‖T (c j)‖ ^ 2) := by
  calc
    ∑' i : ι, ENNReal.ofReal (‖T (b i)‖ ^ 2) =
        ∑' k : η, ENNReal.ofReal (‖(T†) (d k)‖ ^ 2) :=
      ennreal_basis_energy_eq_adjoint_basis T b d
    _ = ∑' j : κ, ENNReal.ofReal (‖T (c j)‖ ^ 2) :=
      (ennreal_basis_energy_eq_adjoint_basis T c d).symm

end NlsGge.Pilot
