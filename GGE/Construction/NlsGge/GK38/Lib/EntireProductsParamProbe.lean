import NlsGge.GK38.Lib.EntireProductsParam
import NlsGge.GK38.Lib.EntireProductsProbe

/-!
# L4c part 1: regression probes

1. Book Lemma C.1 at `σ̃ = 0` is the sine product; the jointly analytic map is analytic there.
2. A one-coordinate perturbation `σ̃ = t e_n`: the product is the explicit function
   `-sin z (nπ + t - z)/(nπ - z)` (affine in `t`).
3. The omitted-factor product at the omitted root: `f_n(nπ, 0) = cos(nπ)`.
4. Finite roots for a sequence with a repeated value (`σ_0 = σ_1 = 0`), the zero criterion, and
   `omitProd` at a double root (zero) versus a simple root (non-zero).
5. Sharp Lemma C.2 at a cancelling pair `a_1 = -a_{-1}`: `A = 0`, so the bound is `O(a²)`.
-/

set_option autoImplicit false

open Filter Topology SummationFilter

namespace NlsGge.GK38.Lib

noncomputable section

/-! ### 1. C.1 at `σ̃ = 0` -/

theorem sigmaOf_zero : sigmaOf (0 : L2Seq) = sigmaZero := by
  funext n; simp [sigmaOf, sigmaZero]

theorem probe_joint_sine (z : ℂ) : entProdJ (z, 0) = -Complex.sin z := by
  unfold entProdJ
  simp only [sigmaOf_zero]
  exact (hasProd_sinProd z).tprod_eq

theorem probe_joint_analytic_at_sine (z : ℂ) :
    AnalyticAt ℂ (fun p : ℂ × L2Seq => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf p.2) p.1 m)
      (z, 0) :=
  analyticOnNhd_entProd_joint (z, 0) trivial

/-! ### 2. A one-coordinate perturbation -/

theorem omitProd_zero_eq (n : ℤ) {z : ℂ} (hz : (n : ℂ) * (Real.pi : ℂ) ≠ z) :
    omitProd n 0 z = -Complex.sin z / ((n : ℂ) * (Real.pi : ℂ) - z) := by
  have h := entProd_eq_mul_omitProd n 0 z
  have h1 := probe_joint_sine z
  unfold entProdJ at h1
  rw [h1, sigmaOf_zero] at h
  have hne : (n : ℂ) * (Real.pi : ℂ) - z ≠ 0 := sub_ne_zero.mpr hz
  rw [eq_div_iff hne]
  simp only [sigmaZero] at h
  linear_combination -h

theorem probe_joint_single (n : ℤ) (t z : ℂ) (hz : (n : ℂ) * (Real.pi : ℂ) ≠ z) :
    entProdJ (z, t • lp.single 2 n (1 : ℂ))
      = -Complex.sin z * ((n : ℂ) * (Real.pi : ℂ) + t - z) / ((n : ℂ) * (Real.pi : ℂ) - z) := by
  unfold entProdJ
  rw [entProd_eq_mul_omitProd n]
  have h0 : omitProd n (t • lp.single 2 n (1 : ℂ)) z = omitProd n 0 z := by
    have := omitProd_add_single n 0 z t
    rwa [zero_add] at this
  rw [h0, omitProd_zero_eq n hz]
  have hsn : sigmaOf (t • lp.single 2 n (1 : ℂ)) n = (n : ℂ) * (Real.pi : ℂ) + t := by
    simp [sigmaOf]
  rw [hsn]
  ring

/-! ### 3. The omitted product at the omitted root -/

theorem probe_omit_at_root (n : ℤ) :
    omitProd n 0 ((n : ℂ) * (Real.pi : ℂ)) = Complex.cos ((n : ℂ) * (Real.pi : ℂ)) := by
  have hn : sigmaOf (0 : L2Seq) n = (n : ℂ) * (Real.pi : ℂ) := by simp [sigmaOf_zero, sigmaZero]
  have h1 := hasDerivAt_entProd_root n 0
  rw [hn] at h1
  have e : (fun z : ℂ => ∏'[symmetricIcc ℤ] m : ℤ, prodFactor (sigmaOf (0 : L2Seq)) z m)
      = fun z => -Complex.sin z := by
    funext z; exact probe_joint_sine z
  rw [e] at h1
  have h2 : HasDerivAt (fun z : ℂ => -Complex.sin z) (-Complex.cos ((n : ℂ) * (Real.pi : ℂ)))
      ((n : ℂ) * (Real.pi : ℂ)) := (Complex.hasDerivAt_sin _).neg
  exact neg_injective (h1.unique h2)

theorem probe_omit_at_root_ne_zero (n : ℤ) : omitProd n 0 ((n : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
  have hn : sigmaOf (0 : L2Seq) n = (n : ℂ) * (Real.pi : ℂ) := by simp [sigmaOf_zero, sigmaZero]
  have := (omitProd_root_ne_zero_iff n 0).mpr (fun m hm h => by
    simp only [sigmaOf_zero, sigmaZero] at h
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have : (m : ℂ) = n := mul_right_cancel₀ hpi h
    exact hm (by exact_mod_cast this))
  rwa [hn] at this

theorem probe_cos_ne_zero_consistent (n : ℤ) : Complex.cos ((n : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
  rw [← probe_omit_at_root]; exact probe_omit_at_root_ne_zero n

/-! ### 4. Repeated value: `σ_0 = σ_1 = 0` -/

theorem probe_roots_double_set : {n : ℤ | sigmaDouble n = 0} = {0, 1} := by
  ext n
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases h : n = 1
  · simp [sigmaDouble, h]
  · simp [sigmaDouble, h, hpi]

theorem probe_finite_roots_double : {n : ℤ | sigmaDouble n = 0}.Finite :=
  finite_roots (by simpa [prodDev] using sigmaDouble_hyp) 0

theorem probe_ncard_double : {n : ℤ | sigmaDouble n = 0}.ncard = 2 := by
  rw [probe_roots_double_set, Set.ncard_pair (by norm_num)]

theorem probe_no_roots_double_pi : {n : ℤ | sigmaDouble n = (Real.pi : ℂ)} = ∅ := by
  ext n
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases h : n = 1
  · simp [sigmaDouble, h, hpi.symm]
  · simp only [sigmaDouble, h, ↓reduceIte, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h2
    exact h (by simpa using h2)

/-- The zero criterion at both a root and a non-root of the perturbed sequence. -/
theorem probe_zero_criterion_double :
    (∏'[symmetricIcc ℤ] m : ℤ, prodFactor sigmaDouble 0 m = 0) ∧
    (∏'[symmetricIcc ℤ] m : ℤ, prodFactor sigmaDouble (Real.pi : ℂ) m ≠ 0) := by
  have hσ : Summable fun n : ℤ => ‖prodDev sigmaDouble n‖ ^ 2 := by
    simpa [prodDev] using sigmaDouble_hyp
  refine ⟨(entProd_eq_zero_iff hσ 0).mpr ⟨0, by simp [sigmaDouble]⟩, fun h => ?_⟩
  obtain ⟨n, hn⟩ := (entProd_eq_zero_iff hσ _).mp h
  have : n ∈ {n : ℤ | sigmaDouble n = (Real.pi : ℂ)} := hn
  rw [probe_no_roots_double_pi] at this
  exact this

/-- The perturbation `σ̃ = -π e_1`, so that `σ = sigmaDouble`. -/
def sDouble : L2Seq := lp.single 2 1 (-(Real.pi : ℂ))

theorem sigmaOf_sDouble : sigmaOf sDouble = sigmaDouble := by
  funext m
  by_cases h : m = 1
  · subst h
    simp [sigmaOf, sDouble, sigmaDouble]
  · simp [sigmaOf, sDouble, sigmaDouble, h]

/-- At a *double* root `0 = σ_0 = σ_1` the omitted product still vanishes ... -/
theorem probe_omit_double_root : omitProd 0 sDouble 0 = 0 := by
  rw [omitProd_eq_zero_iff]
  refine ⟨1, by norm_num, ?_⟩
  rw [sigmaOf_sDouble]; simp [sigmaDouble]

/-- ... and at a simple root `3π` it does not. -/
theorem probe_omit_simple_root : omitProd 3 sDouble ((3 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
  rw [Ne, omitProd_eq_zero_iff]
  rintro ⟨m, hm, h⟩
  rw [sigmaOf_sDouble] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases h1 : m = 1
  · simp [sigmaDouble, h1] at h
  · simp only [sigmaDouble, h1, ↓reduceIte] at h
    have := mul_right_cancel₀ hpi h
    have h3 : m = 3 := by exact_mod_cast this
    exact hm h3

/-! ### 5. Sharp C.2 at a cancelling pair -/

/-- `a_1 = 1/4`, `a_{-1} = -1/4`, all others `0`. -/
def aPair (m : ℤ) : ℂ := if m = 1 then 1 / 4 else if m = -1 then -(1 / 4) else 0

theorem aPair_tsum : ∑' m, aPair m = 0 := by
  rw [tsum_eq_sum (s := {1, -1}) (fun m hm => by
    have h1 : m ≠ 1 := fun h => hm (by simp [h])
    have h2 : m ≠ -1 := fun h => hm (by simp [h])
    simp [aPair, h1, h2])]
  simp [aPair]

theorem aPair_summable : Summable fun m => ‖aPair m‖ :=
  summable_of_ne_finset_zero (s := {1, -1}) fun m hm => by
    have h1 : m ≠ 1 := fun h => hm (by simp [h])
    have h2 : m ≠ -1 := fun h => hm (by simp [h])
    simp [aPair, h1, h2]

theorem aPair_small (m : ℤ) : ‖aPair m‖ ≤ 1 / 2 := by
  unfold aPair
  split_ifs <;> norm_num

theorem probe_sharp_pair :
    ‖(∏' m : ℤ, (1 + aPair m)) - 1‖
      ≤ ‖(0 : ℂ)‖ * Real.exp (∑' m, ‖aPair m‖)
        + (∑' m, ‖aPair m‖ ^ 2) * Real.exp ((∑' m, ‖aPair m‖) + (∑' m, ‖aPair m‖) ^ 2) := by
  have := norm_tprod_one_add_sub_one_le_sharp aPair_summable aPair_small
  rwa [aPair_tsum] at this

end

end NlsGge.GK38.Lib
