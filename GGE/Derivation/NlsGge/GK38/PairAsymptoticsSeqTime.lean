import NlsGge.GK38.PairAsymptoticsSeqForcing

/-!
# F5: time Cauchy–Schwarz for the Volterra forcing

This supplies a time-independent weighted majorant from the L2 mass in time.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

def seqPotMass38 (φ : PotPair) : ℝ := ∫ s in (0 : ℝ)..1, potW38 φ s ^ 2

def seqTimeMass38 (N : PairCont38) : ℝ := ∫ s in (0 : ℝ)..1, seqMass38 N s

def seqGamma38 (φ : PotPair) (N : PairCont38) : ℝ :=
  Real.sqrt (seqPotMass38 φ) * Real.sqrt (seqTimeMass38 N)

theorem seqPotMass38_nonneg (φ : PotPair) : 0 ≤ seqPotMass38 φ :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)

theorem seqTimeMass38_nonneg (N : PairCont38) : 0 ≤ seqTimeMass38 N :=
  intervalIntegral.integral_nonneg zero_le_one (fun s _ => seqMass38_nonneg N s)

theorem seqGamma38_nonneg (φ : PotPair) (N : PairCont38) : 0 ≤ seqGamma38 φ N := by
  unfold seqGamma38
  positivity

theorem intervalIntegrable_potW38_sq (φ : PotPair) :
    IntervalIntegrable (fun s => potW38 φ s ^ 2) volume 0 1 := by
  have h1 := intervalIntegrable_coverRep38_sq_one φ.1
  have h2 := intervalIntegrable_coverRep38_sq_one φ.2
  have hd := (h1.add h2).const_mul (2 : ℝ)
  have hm : AEStronglyMeasurable (fun s => potW38 φ s ^ 2) volume :=
    (((stronglyMeasurable_coverRep38 φ.1).aestronglyMeasurable.norm.add
      (stronglyMeasurable_coverRep38 φ.2).aestronglyMeasurable.norm).pow 2)
  apply hd.mono_fun' hm.restrict
  exact Filter.Eventually.of_forall fun s => by
    change ‖potW38 φ s ^ 2‖ ≤ 2 * (‖coverRep38 φ.1 s‖ ^ 2 + ‖coverRep38 φ.2 s‖ ^ 2)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    unfold potW38 potRepFst38 potRepSnd38
    nlinarith [sq_nonneg (‖coverRep38 φ.1 s‖ - ‖coverRep38 φ.2 s‖)]

theorem seqPotMass38_le (φ : PotPair) : seqPotMass38 φ ≤ 2 * potNormSq38 φ := by
  have h1 := intervalIntegrable_coverRep38_sq_one φ.1
  have h2 := intervalIntegrable_coverRep38_sq_one φ.2
  have hd := (h1.add h2).const_mul (2 : ℝ)
  have h := intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_potW38_sq φ) hd
    (fun s _ => by
      unfold potW38 potRepFst38 potRepSnd38
      nlinarith [sq_nonneg (‖coverRep38 φ.1 s‖ - ‖coverRep38 φ.2 s‖)])
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add h1 h2,
    integral_sq_coverRep38_one, integral_sq_coverRep38_one] at h
  exact h

theorem seqGamma38_sq (φ : PotPair) (N : PairCont38) :
    seqGamma38 φ N ^ 2 = seqPotMass38 φ * seqTimeMass38 N := by
  rw [seqGamma38, mul_pow, Real.sq_sqrt (seqPotMass38_nonneg φ),
    Real.sq_sqrt (seqTimeMass38_nonneg N)]

theorem seqEntry38_le_sqrt (N : PairCont38) (s : ℝ) (i j : Fin 2) :
    ‖ext38 N s i j‖ ≤ Real.sqrt (seqMass38 N s) := by
  apply le_of_sq_le_sq ?_ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (seqMass38_nonneg N s)]
  have h00 : ‖ext38 N s 0 0‖ ^ 2 ≤ seqMass38 N s := by
    unfold seqMass38
    nlinarith [sq_nonneg ‖ext38 N s 0 1‖, sq_nonneg ‖ext38 N s 1 0‖, sq_nonneg ‖ext38 N s 1 1‖]
  have h01 : ‖ext38 N s 0 1‖ ^ 2 ≤ seqMass38 N s := by
    unfold seqMass38
    nlinarith [sq_nonneg ‖ext38 N s 0 0‖, sq_nonneg ‖ext38 N s 1 0‖, sq_nonneg ‖ext38 N s 1 1‖]
  have h10 : ‖ext38 N s 1 0‖ ^ 2 ≤ seqMass38 N s := by
    unfold seqMass38
    nlinarith [sq_nonneg ‖ext38 N s 0 0‖, sq_nonneg ‖ext38 N s 0 1‖, sq_nonneg ‖ext38 N s 1 1‖]
  have h11 : ‖ext38 N s 1 1‖ ^ 2 ≤ seqMass38 N s := by
    unfold seqMass38
    nlinarith [sq_nonneg ‖ext38 N s 0 0‖, sq_nonneg ‖ext38 N s 0 1‖, sq_nonneg ‖ext38 N s 1 0‖]
  fin_cases i <;> fin_cases j <;> first | exact h00 | exact h01 | exact h10 | exact h11

theorem seqTime38_cauchySchwarz (φ : PotPair) (N : PairCont38) :
    (∫ s in (0 : ℝ)..1, potW38 φ s * Real.sqrt (seqMass38 N s)) ≤ seqGamma38 φ N := by
  have hwm : AEStronglyMeasurable (potW38 φ) volume :=
    (stronglyMeasurable_coverRep38 φ.1).aestronglyMeasurable.norm.add
      (stronglyMeasurable_coverRep38 φ.2).aestronglyMeasurable.norm
  have hm : MemLp (potW38 φ) 2 (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hwm.restrict).mpr (by
      have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegrable_potW38_sq φ)
      change Integrable (fun s => potW38 φ s ^ 2) (volume.restrict (Set.Ioc (0 : ℝ) 1)) at hi
      simpa only [Real.norm_eq_abs, sq_abs] using
        hi)
  have hbc : Continuous (fun s => Real.sqrt (seqMass38 N s)) :=
    Real.continuous_sqrt.comp (continuous_seqMass38 N)
  have hb : MemLp (fun s => Real.sqrt (seqMass38 N s)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm hbc.aestronglyMeasurable.restrict).mpr (by
      simp only [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (seqMass38_nonneg N _)]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        ((continuous_seqMass38 N).intervalIntegrable 0 1))
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (Filter.Eventually.of_forall (potW38_nonneg φ))
    (Filter.Eventually.of_forall (fun s => Real.sqrt_nonneg (seqMass38 N s)))
    (by simpa using hm) (by simpa using hb)
  simp only [Real.rpow_two, Real.sq_sqrt (seqMass38_nonneg N _)] at h
  rw [seqGamma38, seqPotMass38, seqTimeMass38, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa only [intervalIntegral.integral_of_le zero_le_one, one_div] using h

theorem norm_volterraP_entry_time_le (φ : PotPair) (z : ℂ) (N : PairCont38)
    (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    ‖volterraP φ z N t i j‖ ≤ Real.exp (|z.im| * (t : ℝ)) * seqGamma38 φ N := by
  let β : ℝ → ℝ := fun s => Real.sqrt (seqMass38 N s)
  have hbc : Continuous β := Real.continuous_sqrt.comp (continuous_seqMass38 N)
  have hint : IntervalIntegrable (fun s => potW38 φ s * β s) volume 0 1 :=
    (intervalIntegrable_potW38 φ).mul_continuousOn hbc.continuousOn
  have hintt := hint.mono_set (uIcc_zero_subset t.2)
  have hk : Continuous (fun s : ℝ => Real.exp (|z.im| * ((t : ℝ) - s))) := by fun_prop
  have hle := norm_volterraFun_entry_le φ z N β
    (fun s _ i j => seqEntry38_le_sqrt N s i j) hint t.2 i j
  change ‖volterraP φ z N t i j‖ ≤ _ at hle
  refine hle.trans ?_
  calc (∫ s in (0 : ℝ)..(t : ℝ), Real.exp (|z.im| * ((t : ℝ) - s)) * (potW38 φ s * β s))
      ≤ ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (|z.im| * (t : ℝ)) * (potW38 φ s * β s) := by
        apply intervalIntegral.integral_mono_on t.2.1
          (hintt.continuousOn_mul hk.continuousOn) (hintt.const_mul _) ?_
        intro s hs
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im, hs.1]))
          (mul_nonneg (potW38_nonneg φ s) (Real.sqrt_nonneg _))
    _ = Real.exp (|z.im| * (t : ℝ)) * ∫ s in (0 : ℝ)..(t : ℝ), potW38 φ s * β s :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ Real.exp (|z.im| * (t : ℝ)) * ∫ s in (0 : ℝ)..1, potW38 φ s * β s := by
      apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact intervalIntegral.integral_mono_interval le_rfl t.2.1 t.2.2
        (Filter.Eventually.of_forall (fun s => mul_nonneg (potW38_nonneg φ s) (Real.sqrt_nonneg _))) hint
    _ ≤ Real.exp (|z.im| * (t : ℝ)) * seqGamma38 φ N :=
      mul_le_mul_of_nonneg_left (seqTime38_cauchySchwarz φ N) (Real.exp_pos _).le

end

end NlsGge.GK38
