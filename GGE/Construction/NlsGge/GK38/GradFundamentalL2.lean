import NlsGge.GK38.GradFundamentalKernels

/-! # K1: actual L2 classes of measurable kernels on the physical circle.
GK Chapter I, Proposition3.1/Corollary3.2. Half-open lifts permit independent
endpoint values; representatives agree a.e., with the period-one normalization.
-/
set_option autoImplicit false
open Filter Topology MeasureTheory Set NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem physicalVolume_eq_spatial38 : (volume : Measure PhysicalCircle) = spatialMeasure := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp only [ENNReal.ofReal_one, one_smul, spatialMeasure]

theorem memLp_intervalKernelLift38 (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    MemLp (AddCircle.liftIoc 1 0 f) 2 spatialMeasure := by
  apply MemLp.haarAddCircle
  have hf' : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) (0 + 1))) := by
    simpa only [zero_add] using hf
  exact hf'.memLp_liftIoc (T := (1 : ℝ)) (t := 0)

/-- Lift an interval-L2 kernel to its actual period-one Lp equivalence class. -/
def intervalKernelL2Class38 (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) : PhysicalL2 :=
  (memLp_intervalKernelLift38 f hf).toLp (AddCircle.liftIoc 1 0 f)

theorem coverRep_intervalKernelL2Class38 {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    coverRep38 (intervalKernelL2Class38 f hf) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] f := by
  have hmem := memLp_intervalKernelLift38 f hf
  have hp : ∀ᵐ x ∂(volume : Measure PhysicalCircle),
      intervalKernelL2Class38 f hf x = AddCircle.liftIoc 1 0 f x := by
    rw [physicalVolume_eq_spatial38]
    exact hmem.coeFn_toLp
  have hreal := (AddCircle.measurePreserving_mk 1 0).quasiMeasurePreserving.ae hp
  simp only [zero_add] at hreal
  rw [← restrict_Ioc_eq_restrict_Icc]
  filter_upwards [hreal, ae_restrict_of_ae (coverRep38_ae_phys (intervalKernelL2Class38 f hf)),
    ae_restrict_mem measurableSet_Ioc] with s hs hc hm
  rw [hc, hs, AddCircle.liftIoc_coe_apply (by simpa only [zero_add] using hm)]

/-- Continuous kernels are interval-L2 before a class is constructed. -/
theorem memLp_pairKernelExt38 (g : PairKernelCont38) (i : Fin 2) :
    MemLp (fun s => pairKernelExt38 g s i) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  apply MemLp.of_bound
    (((continuous_apply i).comp (continuous_pairKernelExt38 g)).aestronglyMeasurable) ‖g‖
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact norm_pairKernelExt38_le g ⟨hs.1.le, hs.2⟩ i

def pairKernelL2Class38 (g : PairKernelCont38) : PotPair :=
  (intervalKernelL2Class38 (fun s => pairKernelExt38 g s 0) (memLp_pairKernelExt38 g 0),
    intervalKernelL2Class38 (fun s => pairKernelExt38 g s 1) (memLp_pairKernelExt38 g 1))

theorem pairKernelL2Class38_rep (g : PairKernelCont38) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      potRepFst38 (pairKernelL2Class38 g) s = pairKernelExt38 g s 0 ∧
        potRepSnd38 (pairKernelL2Class38 g) s = pairKernelExt38 g s 1 := by
  filter_upwards [coverRep_intervalKernelL2Class38 (memLp_pairKernelExt38 g 0),
    coverRep_intervalKernelL2Class38 (memLp_pairKernelExt38 g 1)] with s h0 h1
  exact ⟨h0, h1⟩


theorem intervalIntegrable_intervalKernelL2_sq38 {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    IntervalIntegrable (fun s => ‖f s‖ ^ 2) volume 0 1 := by
  apply intervalIntegrable_iff.mpr
  have hi := intervalIntegrable_iff.mp
    (intervalIntegrable_coverRep38_sq_one (intervalKernelL2Class38 f hf))
  rw [Set.uIoc_of_le zero_le_one] at hi ⊢
  unfold IntegrableOn at hi ⊢
  rw [restrict_Ioc_eq_restrict_Icc] at hi ⊢
  exact hi.congr ((coverRep_intervalKernelL2Class38 hf).mono (fun s hs => congrArg (fun w : ℂ => ‖w‖ ^ 2) hs))

theorem norm_intervalKernelL2Class38_sq {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    ‖intervalKernelL2Class38 f hf‖ ^ 2 = ∫ s in (0 : ℝ)..1, ‖f s‖ ^ 2 := by
  have _hi := intervalIntegrable_intervalKernelL2_sq38 hf
  rw [← integral_sq_coverRep38_one]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [Set.uIoc_of_le zero_le_one, restrict_Ioc_eq_restrict_Icc]
  exact (coverRep_intervalKernelL2Class38 hf).mono (fun s hs => congrArg (fun w : ℂ => ‖w‖ ^ 2) hs)

theorem potNormSq_pairKernelL2Class38 (g : PairKernelCont38) :
    potNormSq38 (pairKernelL2Class38 g) = ∫ s in (0 : ℝ)..1,
      ‖pairKernelExt38 g s 0‖ ^ 2 + ‖pairKernelExt38 g s 1‖ ^ 2 := by
  rw [intervalIntegral.integral_add
    (intervalIntegrable_intervalKernelL2_sq38 (memLp_pairKernelExt38 g 0))
    (intervalIntegrable_intervalKernelL2_sq38 (memLp_pairKernelExt38 g 1))]
  exact congrArg₂ (fun a b : ℝ => a + b)
    (norm_intervalKernelL2Class38_sq (memLp_pairKernelExt38 g 0))
    (norm_intervalKernelL2Class38_sq (memLp_pairKernelExt38 g 1))

def gradDiscrimL2 (φ : PotPair) (z : ℂ) : PotPair := pairKernelL2Class38 (gradDiscrimCont38 φ z)
def gradAntiDiscrimL2 (φ : PotPair) (z : ℂ) : PotPair := pairKernelL2Class38 (gradAntiDiscrimCont38 φ z)

theorem gradDiscrimL2_rep (φ : PotPair) (z : ℂ) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      potRepFst38 (gradDiscrimL2 φ z) s = gradDiscrim38 φ z s 0 ∧
        potRepSnd38 (gradDiscrimL2 φ z) s = gradDiscrim38 φ z s 1 := by
  filter_upwards [pairKernelL2Class38_rep (gradDiscrimCont38 φ z),
    ae_restrict_mem measurableSet_Icc] with s hs hm
  simpa only [gradDiscrimL2, gradDiscrimCont38, gradAntiDiscrimL2, gradAntiDiscrimCont38,
    pairKernelExt38_of_mem _ hm, ContinuousMap.coe_mk] using hs

theorem gradAntiDiscrimL2_rep (φ : PotPair) (z : ℂ) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      potRepFst38 (gradAntiDiscrimL2 φ z) s = gradAntiDiscrim38 φ z s 0 ∧
        potRepSnd38 (gradAntiDiscrimL2 φ z) s = gradAntiDiscrim38 φ z s 1 := by
  filter_upwards [pairKernelL2Class38_rep (gradAntiDiscrimCont38 φ z),
    ae_restrict_mem measurableSet_Icc] with s hs hm
  simpa only [gradDiscrimL2, gradDiscrimCont38, gradAntiDiscrimL2, gradAntiDiscrimCont38,
    pairKernelExt38_of_mem _ hm, ContinuousMap.coe_mk] using hs


theorem potNormSq_gradDiscrimL2 (φ : PotPair) (z : ℂ) :
    potNormSq38 (gradDiscrimL2 φ z) = ∫ s in (0 : ℝ)..1,
      ‖gradDiscrim38 φ z s 0‖ ^ 2 + ‖gradDiscrim38 φ z s 1‖ ^ 2 := by
  rw [gradDiscrimL2, potNormSq_pairKernelL2Class38]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  change ‖pairKernelExt38 _ s 0‖ ^ 2 + ‖pairKernelExt38 _ s 1‖ ^ 2 = _
  rw [pairKernelExt38_of_mem _ hs]
  rfl

theorem potNormSq_gradAntiDiscrimL2 (φ : PotPair) (z : ℂ) :
    potNormSq38 (gradAntiDiscrimL2 φ z) = ∫ s in (0 : ℝ)..1,
      ‖gradAntiDiscrim38 φ z s 0‖ ^ 2 + ‖gradAntiDiscrim38 φ z s 1‖ ^ 2 := by
  rw [gradAntiDiscrimL2, potNormSq_pairKernelL2Class38]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le zero_le_one] at hs
  change ‖pairKernelExt38 _ s 0‖ ^ 2 + ‖pairKernelExt38 _ s 1‖ ^ 2 = _
  rw [pairKernelExt38_of_mem _ hs]
  rfl

def cutoffPairKernel38 (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1) (s : ℝ) : PairVec38 :=
  if s ≤ (t : ℝ) then pairKernelExt38 g s else 0

theorem scalarCutoff_memLp38 {f : ℝ → ℂ} {t : ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    MemLp (fun s => if s ≤ t then f s else 0) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h : MemLp ((Iic t).indicator f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    MemLp.indicator measurableSet_Iic hf
  exact MemLp.ae_eq (Filter.Eventually.of_forall (fun s => by
    simp only [Set.indicator, Set.mem_Iic])) h

theorem memLp_cutoffPairKernel38 (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1) (i : Fin 2) :
    MemLp (fun s => cutoffPairKernel38 g t s i) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have heq : (fun s => cutoffPairKernel38 g t s i) =
      (fun s => if s ≤ (t : ℝ) then pairKernelExt38 g s i else 0) := by
    funext s
    unfold cutoffPairKernel38
    split_ifs <;> rfl
  rw [heq]
  exact scalarCutoff_memLp38 (memLp_pairKernelExt38 g i)

def cutoffPairKernelL2Class38 (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1) : PotPair :=
  (intervalKernelL2Class38 (fun s => cutoffPairKernel38 g t s 0) (memLp_cutoffPairKernel38 g t 0),
    intervalKernelL2Class38 (fun s => cutoffPairKernel38 g t s 1) (memLp_cutoffPairKernel38 g t 1))

theorem cutoffPairKernelL2Class38_rep (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      potRepFst38 (cutoffPairKernelL2Class38 g t) s = cutoffPairKernel38 g t s 0 ∧
        potRepSnd38 (cutoffPairKernelL2Class38 g t) s = cutoffPairKernel38 g t s 1 := by
  filter_upwards [coverRep_intervalKernelL2Class38 (memLp_cutoffPairKernel38 g t 0),
    coverRep_intervalKernelL2Class38 (memLp_cutoffPairKernel38 g t 1)] with s h0 h1
  exact ⟨h0, h1⟩

theorem potNormSq_cutoffPairKernelL2Class38 (g : PairKernelCont38) (t : Set.Icc (0 : ℝ) 1) :
    potNormSq38 (cutoffPairKernelL2Class38 g t) = ∫ s in (0 : ℝ)..1,
      ‖cutoffPairKernel38 g t s 0‖ ^ 2 + ‖cutoffPairKernel38 g t s 1‖ ^ 2 := by
  rw [intervalIntegral.integral_add
    (intervalIntegrable_intervalKernelL2_sq38 (memLp_cutoffPairKernel38 g t 0))
    (intervalIntegrable_intervalKernelL2_sq38 (memLp_cutoffPairKernel38 g t 1))]
  exact congrArg₂ (fun a b : ℝ => a + b)
    (norm_intervalKernelL2Class38_sq (memLp_cutoffPairKernel38 g t 0))
    (norm_intervalKernelL2Class38_sq (memLp_cutoffPairKernel38 g t 1))

end
end NlsGge.GK38
