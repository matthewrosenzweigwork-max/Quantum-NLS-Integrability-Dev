import NlsGge.GK38.GradFundamentalL2

/-! # H181 supporting module (c): pairKernelL2Class38 as a bounded linear map.
Packages the landed actual-L2-class map `pairKernelL2Class38 : PairKernelCont38 → PotPair`
(GK38/GradFundamentalL2.lean) as the continuous ℂ-linear map `pairKernelL2CLM38` with norm bound
`‖pairKernelL2Class38 g‖ ≤ 2 * ‖g‖` (sup norm on C(Icc 0 1, PairVec38), sup norm on PotPair).
Additivity and homogeneity are proved from the pointwise identities of `pairKernelExt38` and from
the a.e.-free `MemLp.toLp` calculus (liftIoc is pointwise). No hypotheses are added. -/
set_option autoImplicit false
open Filter Topology MeasureTheory Set NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

/-- Sums of pointwise-equal interval kernels give sums of their L2 classes. -/
theorem intervalKernelL2Class38_add_of_eq {f g k : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hk : MemLp k 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (h : ∀ s, k s = f s + g s) :
    intervalKernelL2Class38 k hk = intervalKernelL2Class38 f hf + intervalKernelL2Class38 g hg := by
  obtain rfl : k = fun s => f s + g s := funext h
  unfold intervalKernelL2Class38
  calc (memLp_intervalKernelLift38 (fun s => f s + g s) hk).toLp
        (AddCircle.liftIoc 1 0 (fun s => f s + g s))
      = ((memLp_intervalKernelLift38 f hf).add (memLp_intervalKernelLift38 g hg)).toLp
          (AddCircle.liftIoc 1 0 f + AddCircle.liftIoc 1 0 g) :=
        MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun _ => rfl)
    _ = _ := MemLp.toLp_add _ _

/-- Scalar multiples of pointwise-scaled interval kernels give scalar multiples of their classes. -/
theorem intervalKernelL2Class38_smul_of_eq {f k : ℝ → ℂ} (c : ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hk : MemLp k 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (h : ∀ s, k s = c * f s) :
    intervalKernelL2Class38 k hk = c • intervalKernelL2Class38 f hf := by
  obtain rfl : k = fun s => c * f s := funext h
  unfold intervalKernelL2Class38
  calc (memLp_intervalKernelLift38 (fun s => c * f s) hk).toLp
        (AddCircle.liftIoc 1 0 (fun s => c * f s))
      = ((memLp_intervalKernelLift38 f hf).const_smul c).toLp (c • AddCircle.liftIoc 1 0 f) :=
        MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun _ => rfl)
    _ = c • (memLp_intervalKernelLift38 f hf).toLp (AddCircle.liftIoc 1 0 f) :=
        MemLp.toLp_const_smul c _

theorem pairKernelL2Class38_add (g h : PairKernelCont38) :
    pairKernelL2Class38 (g + h) = pairKernelL2Class38 g + pairKernelL2Class38 h := by
  unfold pairKernelL2Class38
  rw [Prod.mk_add_mk]
  refine Prod.ext ?_ ?_
  · exact intervalKernelL2Class38_add_of_eq (memLp_pairKernelExt38 g 0)
      (memLp_pairKernelExt38 h 0) (memLp_pairKernelExt38 (g + h) 0) (fun _ => rfl)
  · exact intervalKernelL2Class38_add_of_eq (memLp_pairKernelExt38 g 1)
      (memLp_pairKernelExt38 h 1) (memLp_pairKernelExt38 (g + h) 1) (fun _ => rfl)

theorem pairKernelL2Class38_smul (c : ℂ) (g : PairKernelCont38) :
    pairKernelL2Class38 (c • g) = c • pairKernelL2Class38 g := by
  unfold pairKernelL2Class38
  rw [Prod.smul_mk]
  refine Prod.ext ?_ ?_
  · exact intervalKernelL2Class38_smul_of_eq c (memLp_pairKernelExt38 g 0)
      (memLp_pairKernelExt38 (c • g) 0) (fun _ => rfl)
  · exact intervalKernelL2Class38_smul_of_eq c (memLp_pairKernelExt38 g 1)
      (memLp_pairKernelExt38 (c • g) 1) (fun _ => rfl)

/-- Norm bound: `‖φ‖² ≤ potNormSq38 φ = ∫₀¹ ‖g₁‖² + ‖g₂‖² ≤ 2‖g‖²` for `φ = pairKernelL2Class38 g`. -/
theorem norm_pairKernelL2Class38_le (g : PairKernelCont38) :
    ‖pairKernelL2Class38 g‖ ≤ 2 * ‖g‖ := by
  have hc (i : Fin 2) : Continuous (fun s => pairKernelExt38 g s i) :=
    (continuous_apply i).comp (continuous_pairKernelExt38 g)
  have hint : IntervalIntegrable
      (fun s => ‖pairKernelExt38 g s 0‖ ^ 2 + ‖pairKernelExt38 g s 1‖ ^ 2) volume 0 1 :=
    (((hc 0).norm.pow 2).add ((hc 1).norm.pow 2)).intervalIntegrable 0 1
  have hsq : potNormSq38 (pairKernelL2Class38 g) ≤ 2 * ‖g‖ ^ 2 := by
    rw [potNormSq_pairKernelL2Class38]
    have hconst : ∫ _ in (0 : ℝ)..1, 2 * ‖g‖ ^ 2 = 2 * ‖g‖ ^ 2 := by simp
    rw [← hconst]
    apply intervalIntegral.integral_mono_on zero_le_one hint
      (continuous_const.intervalIntegrable 0 1)
    intro s hs
    have p0 : ‖pairKernelExt38 g s 0‖ ^ 2 ≤ ‖g‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_pairKernelExt38_le g hs 0) 2
    have p1 : ‖pairKernelExt38 g s 1‖ ^ 2 ≤ ‖g‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_pairKernelExt38_le g hs 1) 2
    linarith
  have hn := norm_sq_le_potNormSq38 (pairKernelL2Class38 g)
  have hsq' : ‖pairKernelL2Class38 g‖ ^ 2 ≤ (2 * ‖g‖) ^ 2 := by
    nlinarith [sq_nonneg ‖g‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq'

/-- The bounded ℂ-linear map from the sup-norm space of pair kernels to the potential pairs. -/
def pairKernelL2CLM38 : PairKernelCont38 →L[ℂ] PotPair :=
  LinearMap.mkContinuous
    { toFun := pairKernelL2Class38
      map_add' := pairKernelL2Class38_add
      map_smul' := fun c g => pairKernelL2Class38_smul c g }
    2 norm_pairKernelL2Class38_le

@[simp] theorem pairKernelL2CLM38_apply (g : PairKernelCont38) :
    pairKernelL2CLM38 g = pairKernelL2Class38 g := rfl

theorem norm_pairKernelL2CLM38_le (g : PairKernelCont38) :
    ‖pairKernelL2CLM38 g‖ ≤ 2 * ‖g‖ :=
  norm_pairKernelL2Class38_le g

end
end NlsGge.GK38
