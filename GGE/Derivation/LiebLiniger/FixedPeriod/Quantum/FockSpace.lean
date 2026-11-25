import LiebLiniger.FixedPeriod.Quantum.SymmetricSector
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

/-!
Concrete Q0-001 carrier and coherent vectors, author candidate 2026-10-26.
UNCOMPILED: root alone owns the guarded compiler/MCP queue.

This uses actual product-L² kernels and actual permutation-fixed sectors from
TransferKernel/SymmetricSector. No coherent Gram, totality, or sector norm
identity is assumed. Here μ is the genuine one-particle measure; instantiate it
with physical length measure on T_L (total mass L), without probability
renormalization. Zero-coordinate product measure has mass one.

Totality is NOT proved by this file. It requires pure-symmetric-tensor density
and scalar power-series coefficient extraction, rather than another hypothesis.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace ComplexConjugate ENNReal

namespace LiebLiniger.FixedPeriod.Quantum

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

section PureInner
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The representative formula is exported only as an almost-everywhere equality. -/
theorem coeFn_pureTensorL2 (u : Lp ℂ 2 μ) :
    (pureTensorL2 (ι := ι) μ u : (ι → X) → ℂ) =ᵐ[Measure.pi fun _ : ι => μ]
      fun x => ∏ i, u (x i) :=
  (pureTensorFunction_memLp (ι := ι) μ u).coeFn_toLp

/-- Concrete pure-kernel inner products factor into one-particle inner products. -/
theorem inner_pureTensorL2 (u v : Lp ℂ 2 μ) :
    inner ℂ (pureTensorL2 (ι := ι) μ u) (pureTensorL2 (ι := ι) μ v) =
      (inner ℂ u v) ^ Fintype.card ι := by
  classical
  -- The L² pairings are integrable before the integral factorization is used.
  have hpair : Integrable (fun x => inner ℂ (u x) (v x)) μ :=
    L2.integrable_inner u v
  have hprod : Integrable
      (fun x : ι → X => ∏ i, inner ℂ (u (x i)) (v (x i)))
      (Measure.pi fun _ : ι => μ) :=
    Integrable.fintype_prod (fun _ : ι => hpair)
  rw [L2.inner_def]
  calc
    (∫ x, inner ℂ (pureTensorL2 μ u x) (pureTensorL2 μ v x)
        ∂Measure.pi (fun _ : ι => μ)) =
        ∫ x : ι → X, inner ℂ (∏ i, u (x i)) (∏ i, v (x i))
          ∂Measure.pi (fun _ : ι => μ) := by
      apply integral_congr_ae
      filter_upwards [coeFn_pureTensorL2 (ι := ι) μ u,
        coeFn_pureTensorL2 (ι := ι) μ v] with x hu hv
      rw [hu, hv]
    _ = ∫ x : ι → X, ∏ i, inner ℂ (u (x i)) (v (x i))
          ∂Measure.pi (fun _ : ι => μ) := by
      congr 1
      ext x
      simp only [RCLike.inner_apply, map_prod, Finset.prod_mul_distrib]
    _ = (inner ℂ u v) ^ Fintype.card ι := by
      calc
        _ = (∫ x, inner ℂ (u x) (v x) ∂μ) ^ Fintype.card ι :=
          integral_fintype_prod_eq_pow (ι := ι) (𝕜 := ℂ)
            (fun x : X => inner ℂ (u x) (v x))
        _ = _ := congrArg (fun z : ℂ => z ^ Fintype.card ι) (L2.inner_def u v).symm

/-- Scaling the one-particle vector scales a genuine n-fold product kernel
by the n-th power, with all representative equalities transported through the
coordinate evaluations. -/
theorem pureTensorL2_smul (z : ℂ) (u : Lp ℂ 2 μ) :
    pureTensorL2 (ι := ι) μ (z • u) =
      z ^ Fintype.card ι • pureTensorL2 (ι := ι) μ u := by
  classical
  have hu : ∀ᵐ x : ι → X ∂Measure.pi (fun _ : ι => μ),
      ∀ i : ι, (z • u) (x i) = z * u (x i) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [(Lp.coeFn_smul z u).comp_tendsto
      (Measure.quasiMeasurePreserving_eval (fun _ : ι => μ) i).tendsto_ae] with x hx
    simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hx
  apply Lp.ext
  filter_upwards [coeFn_pureTensorL2 (ι := ι) μ (z • u),
    Lp.coeFn_smul (z ^ Fintype.card ι) (pureTensorL2 (ι := ι) μ u),
    coeFn_pureTensorL2 (ι := ι) μ u, hu] with x hl hr hp hx
  rw [hl, hr]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hp]
  simp only [hx, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ]

/-- Actual repeated tensors, bundled in the full closed symmetric sector. -/
def pureSymmetricTensor (n : ℕ) (u : Lp ℂ 2 μ) : SymmetricSector μ n :=
  ⟨pureTensorL2 (ι := Fin n) μ u,
    (mem_symmetricSectorSpace μ n _).2 (symmetrizeL2_pureTensorL2 μ u)⟩

@[simp] theorem inner_pureSymmetricTensor (n : ℕ) (u v : Lp ℂ 2 μ) :
    inner ℂ (pureSymmetricTensor μ n u) (pureSymmetricTensor μ n v) =
      (inner ℂ u v)^n := by
  change inner ℂ (pureTensorL2 (ι := Fin n) μ u) (pureTensorL2 μ v) = _
  simpa only [Fintype.card_fin] using inner_pureTensorL2 (ι := Fin n) μ u v

@[simp] theorem pureSymmetricTensor_smul (n : ℕ) (z : ℂ) (u : Lp ℂ 2 μ) :
    pureSymmetricTensor μ n (z • u) = z^n • pureSymmetricTensor μ n u := by
  apply Subtype.ext
  change pureTensorL2 (ι := Fin n) μ (z • u) = z^n • pureTensorL2 μ u
  simpa only [Fintype.card_fin] using pureTensorL2_smul (ι := Fin n) μ z u

/-- Positive real square-root normalization, including n=0. -/
def factorialWeight (n : ℕ) : ℝ := (Real.sqrt (n.factorial : ℝ))⁻¹

theorem factorialWeight_sq (n : ℕ) :
    factorialWeight n ^ 2 = (n.factorial : ℝ)⁻¹ := by
  rw [factorialWeight, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The n-th sector of the unnormalized exponential vector. -/
def exponentialSector (n : ℕ) (u : Lp ℂ 2 μ) : SymmetricSector μ n :=
  (factorialWeight n : ℂ) • pureSymmetricTensor μ n u

@[simp] theorem exponentialSector_smul (n : ℕ) (z : ℂ) (u : Lp ℂ 2 μ) :
    exponentialSector μ n (z • u) = z^n • exponentialSector μ n u := by
  simp only [exponentialSector, pureSymmetricTensor_smul, smul_smul]
  rw [mul_comm]

/-- Exact factorial sector Gram formula; no sector identity is assumed. -/
theorem inner_exponentialSector (n : ℕ) (u v : Lp ℂ 2 μ) :
    inner ℂ (exponentialSector μ n u) (exponentialSector μ n v) =
      (inner ℂ u v)^n / (n.factorial : ℂ) := by
  change inner ℂ ((factorialWeight n : ℂ) • pureTensorL2 (ι := Fin n) μ u)
    ((factorialWeight n : ℂ) • pureTensorL2 (ι := Fin n) μ v) = _
  rw [inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ),
    Complex.conj_ofReal, inner_pureTensorL2]
  simp only [Fintype.card_fin]
  have hw : (factorialWeight n : ℂ) * (factorialWeight n : ℂ) =
      (n.factorial : ℂ)⁻¹ := by
    calc
      _ = ((factorialWeight n ^ 2 : ℝ) : ℂ) := by push_cast; ring
      _ = (n.factorial : ℂ)⁻¹ := by rw [factorialWeight_sq]; push_cast; rfl
  calc
    (factorialWeight n : ℂ) * ((factorialWeight n : ℂ) * (inner ℂ u v)^n) =
        ((factorialWeight n : ℂ) * (factorialWeight n : ℂ)) * (inner ℂ u v)^n := by ring
    _ = (inner ℂ u v)^n / (n.factorial : ℂ) := by rw [hw]; ring

/-- The actual squared norm needed for Hilbert direct-sum membership. -/
theorem norm_exponentialSector_sq (n : ℕ) (u : Lp ℂ 2 μ) :
    ‖exponentialSector μ n u‖^2 = (‖u‖^2)^n / (n.factorial : ℝ) := by
  have hi : (inner ℂ u u)^n / (n.factorial : ℂ) =
      (((‖u‖^2)^n / (n.factorial : ℝ) : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    push_cast
    rfl
  calc
    _ = (inner ℂ (exponentialSector μ n u) (exponentialSector μ n u)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = ((inner ℂ u u)^n / (n.factorial : ℂ)).re :=
      congrArg Complex.re (inner_exponentialSector μ n u u)
    _ = _ := by rw [hi, Complex.ofReal_re]

/-- Scalar extraction is proved before any dependent Fock evaluation occurs. -/
theorem inner_exponentialSector_right (n : ℕ) (v : SymmetricSector μ n) (u : Lp ℂ 2 μ) :
    inner ℂ v (exponentialSector μ n u) =
      (factorialWeight n : ℂ) * inner ℂ v (pureSymmetricTensor μ n u) := by
  change inner ℂ v ((factorialWeight n : ℂ) • pureSymmetricTensor μ n u) = _
  exact inner_smul_right (𝕜 := ℂ) v (pureSymmetricTensor μ n u)
    (factorialWeight n : ℂ)

/-- Sector scalar extraction avoids unfolding the dependent direct sum. -/
theorem inner_exponentialSector_smul_right (n : ℕ) (v : SymmetricSector μ n)
    (z : ℂ) (u : Lp ℂ 2 μ) :
    inner ℂ v (exponentialSector μ n (z • u)) =
      z^n * inner ℂ v (exponentialSector μ n u) := by
  rw [exponentialSector_smul]
  exact inner_smul_right (𝕜 := ℂ) v (exponentialSector μ n u) (z^n)

end PureInner

/-- The genuine Hilbert direct sum of all complete symmetric sectors. -/
abbrev FockSpace := lp (fun n : ℕ => SymmetricSector μ n) 2

/-- Summability is proved before constructing an exponential vector. -/
theorem exponentialSector_memℓp (u : Lp ℂ 2 μ) :
    Memℓp (fun n : ℕ => exponentialSector μ n u) 2 := by
  apply memℓp_gen
  convert Real.summable_pow_div_factorial (‖u‖^2) using 1
  funext n
  rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num, Real.rpow_two]
  exact norm_exponentialSector_sq μ n u

/-- Unnormalized exponential vector with sector g^tensor n / sqrt(n!). -/
def exponentialVector (u : Lp ℂ 2 μ) : FockSpace μ :=
  ⟨fun n => exponentialSector μ n u, exponentialSector_memℓp μ u⟩

@[simp] theorem exponentialVector_apply (u : Lp ℂ 2 μ) (n : ℕ) :
    exponentialVector μ u n = exponentialSector μ n u := rfl

/-- Orthogonality of sectors and the complex exponential series give the exact Gram kernel. -/
theorem exponentialVector_inner (u v : Lp ℂ 2 μ) :
    inner ℂ (exponentialVector μ u) (exponentialVector μ v) =
      Complex.exp (inner ℂ u v) := by
  rw [lp.inner_eq_tsum]
  simp_rw [exponentialVector_apply, inner_exponentialSector]
  have hs : HasSum (fun n : ℕ => (inner ℂ u v)^n / (n.factorial : ℂ))
      (Complex.exp (inner ℂ u v)) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  exact hs.tsum_eq

/-- This is exp(||u||²), rather than one: the vector is unnormalized. -/
theorem exponentialVector_norm_sq (u : Lp ℂ 2 μ) :
    ‖exponentialVector μ u‖^2 = Real.exp (‖u‖^2) := by
  have hi : inner ℂ u u = ((‖u‖^2 : ℝ) : ℂ) := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using
      (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u)
  calc
    _ = (inner ℂ (exponentialVector μ u) (exponentialVector μ u)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) _
    _ = (Complex.exp (inner ℂ u u)).re := congrArg Complex.re (exponentialVector_inner μ u u)
    _ = _ := by rw [hi, Complex.exp_ofReal_re]

/-- Exact difference-norm formula used to prove norm continuity. -/
theorem exponentialVector_sub_norm_sq (u v : Lp ℂ 2 μ) :
    ‖exponentialVector μ u - exponentialVector μ v‖^2 =
      Real.exp (‖u‖^2) - 2 * (Complex.exp (inner ℂ u v)).re + Real.exp (‖v‖^2) := by
  rw [norm_sub_sq (𝕜 := ℂ), exponentialVector_norm_sq, exponentialVector_norm_sq,
    exponentialVector_inner]
  simp only [RCLike.re_eq_complex_re]

/-- Norm continuity follows from the explicit Gram formula. -/
theorem continuous_exponentialVector : Continuous (exponentialVector μ) := by
  apply continuous_iff_continuous_dist.mpr
  have hd (u v : Lp ℂ 2 μ) :
      dist (exponentialVector μ u) (exponentialVector μ v) =
        Real.sqrt (Real.exp (‖u‖^2) -
          2 * (Complex.exp (inner ℂ u v)).re + Real.exp (‖v‖^2)) := by
    rw [dist_eq_norm]
    rw [← exponentialVector_sub_norm_sq μ u v, Real.sqrt_sq (norm_nonneg _)]
  simp_rw [hd]
  fun_prop

/-- Each coherent pairing along a complex line is its actual sector series.
Its HasSum proof comes from the already-constructed Hilbert vector, so no
coefficient summability premise is introduced. -/
theorem hasSum_inner_exponentialVector_smul (ψ : FockSpace μ)
    (u : Lp ℂ 2 μ) (z : ℂ) :
    HasSum (fun n : ℕ => z^n * inner ℂ (ψ n) (exponentialSector μ n u))
      (inner ℂ ψ (exponentialVector μ (z • u))) := by
  have hterm : (fun n : ℕ => inner ℂ (ψ n) (exponentialVector μ (z • u) n)) =
      (fun n : ℕ => z^n * inner ℂ (ψ n) (exponentialSector μ n u)) := by
    funext n
    change inner ℂ (ψ n) (exponentialSector μ n (z • u)) = _
    exact inner_exponentialSector_smul_right μ n (ψ n) z u
  rw [← hterm]
  exact lp.hasSum_inner (𝕜 := ℂ) ψ (exponentialVector μ (z • u))

/-- Orthogonality to all exponential vectors forces every sector coefficient
on every pure power to vanish. This proves the analytic coefficient-extraction
step without assuming totality of the coherent family. -/
theorem exponentialVector_orthogonal_sector_coeff (ψ : FockSpace μ)
    (hψ : ∀ u : Lp ℂ 2 μ, inner ℂ ψ (exponentialVector μ u) = 0)
    (u : Lp ℂ 2 μ) (n : ℕ) :
    inner ℂ (ψ n) (exponentialSector μ n u) = 0 := by
  let c : ℕ → ℂ := fun k => inner ℂ (ψ k) (exponentialSector μ k u)
  have ha : HasFPowerSeriesAt (fun z : ℂ => inner ℂ ψ (exponentialVector μ (z • u)))
      (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    exact Filter.Eventually.of_forall fun z => by
      simpa only [zero_add, FormalMultilinearSeries.coeff_ofScalars,
        smul_eq_mul, c] using hasSum_inner_exponentialVector_smul μ ψ u z
  have hfun : (fun z : ℂ => inner ℂ ψ (exponentialVector μ (z • u))) = 0 := by
    funext z
    exact hψ (z • u)
  rw [hfun] at ha
  have hc : c = 0 :=
    (FormalMultilinearSeries.ofScalars_series_eq_zero (E := ℂ)).mp ha.eq_zero
  exact congrFun hc n

/-- Removing the positive normalization leaves genuine pure symmetric powers. -/
theorem exponentialVector_orthogonal_pureSymmetricTensor (ψ : FockSpace μ)
    (hψ : ∀ u : Lp ℂ 2 μ, inner ℂ ψ (exponentialVector μ u) = 0)
    (u : Lp ℂ 2 μ) (n : ℕ) :
    inner ℂ (ψ n) (pureSymmetricTensor μ n u) = 0 := by
  have hc := exponentialVector_orthogonal_sector_coeff μ ψ hψ u n
  rw [inner_exponentialSector_right] at hc
  have hw : (factorialWeight n : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast n.factorial_pos)))
  exact (mul_eq_zero.mp hc).resolve_left hw

/-- The vacuum is the source zero-particle vector, expressed through the
literal empty-product kernel rather than a chosen scalar representative. -/
def vacuum : FockSpace μ :=
  lp.single (E := fun n : ℕ => SymmetricSector μ n) 2 0
    (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ))

@[simp] theorem exponentialVector_zero :
    exponentialVector μ (0 : Lp ℂ 2 μ) = vacuum μ := by
  apply lp.ext
  funext n
  change exponentialSector μ n (0 : Lp ℂ 2 μ) =
    lp.single (E := fun n : ℕ => SymmetricSector μ n) 2 0
    (pureSymmetricTensor μ 0 (0 : Lp ℂ 2 μ)) n
  by_cases hn : n = 0
  · subst n
    simp [exponentialSector, factorialWeight]
  · have hz : exponentialSector μ n (0 : Lp ℂ 2 μ) = 0 := by
      have hs := norm_exponentialSector_sq μ n (0 : Lp ℂ 2 μ)
      simp [hn] at hs
      exact hs
    rw [hz, lp.single_apply_ne 2 0 _ hn]

@[simp] theorem norm_vacuum_sq : ‖vacuum μ‖^2 = 1 := by
  rw [← exponentialVector_zero, exponentialVector_norm_sq]
  simp

end LiebLiniger.FixedPeriod.Quantum
