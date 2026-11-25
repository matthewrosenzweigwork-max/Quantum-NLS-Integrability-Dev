import NlsGge.Spectral.GenericRoughMatrixDysonFactorial32V1
import NlsGge.Spectral.ActualPhysicalUnitDiscriminantNonrealZeroFree32V1
import NlsGge.Schur.ActualPhysicalSourceIntervalCauchySchwarz33V2
import NlsGge.Spectral.ActualPhysicalL2ZsDysonFactorialBoundV1
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory
namespace NlsGge.SpectralFoundations
open NlsGge.Schur NlsGge.Pilot NlsGge.Analysis
open CumulativePowerV3 CumulativePowerGeneralEndpointV1

theorem genericDysonIntegrand_integrable_E02_38
    (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 1) :
    ∀ (n : ℕ) (i j : Fin 2),
      ContinuousOn (fun t => genericRoughMatrixDysonTerm32 B n t i j) (Set.Icc (0 : ℝ) 1) ∧
      IntervalIntegrable
        (fun s => (B s * genericRoughMatrixDysonTerm32 B n s) i j) volume 0 1 := by
  intro n
  induction n with
  | zero =>
      intro i j
      have hc : ContinuousOn (fun t => genericRoughMatrixDysonTerm32 B 0 t i j)
          (Set.Icc (0 : ℝ) 1) := by
        simpa [genericRoughMatrixDysonTerm32] using
          (continuousOn_const : ContinuousOn
            (fun _ : ℝ => ((1 : Matrix (Fin 2) (Fin 2) ℂ) i j)) (Set.Icc (0 : ℝ) 1))
      refine ⟨hc, ?_⟩
      have hB' (k : Fin 2) : ContinuousOn (fun s => genericRoughMatrixDysonTerm32 B 0 s k j)
          (Set.uIcc (0 : ℝ) 1) := by
        simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
          (by simpa [genericRoughMatrixDysonTerm32] using
            (continuousOn_const : ContinuousOn
              (fun _ : ℝ => ((1 : Matrix (Fin 2) (Fin 2) ℂ) k j)) (Set.Icc (0 : ℝ) 1)) :
            ContinuousOn (fun s => genericRoughMatrixDysonTerm32 B 0 s k j) (Set.Icc (0 : ℝ) 1))
      have := ((hB i 0).mul_continuousOn (hB' 0)).add ((hB i 1).mul_continuousOn (hB' 1))
      simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
  | succ n ih =>
      have hint (i j : Fin 2) : IntervalIntegrable
          (fun s => (B s * genericRoughMatrixDysonTerm32 B (n + 1) s) i j) volume 0 1 := by
        have hB' (k : Fin 2) : ContinuousOn
            (fun s => genericRoughMatrixDysonTerm32 B (n + 1) s k j) (Set.uIcc (0 : ℝ) 1) := by
          have hc : ContinuousOn (fun s => genericRoughMatrixDysonTerm32 B (n + 1) s k j)
              (Set.Icc (0 : ℝ) 1) := by
            change ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t,
              (B s * genericRoughMatrixDysonTerm32 B n s) k j) (Set.Icc (0 : ℝ) 1)
            have hprim := intervalIntegral.continuousOn_primitive_interval'
              (μ := volume) (ih k j).2 (Set.left_mem_uIcc (a := (0:ℝ)) (b := 1))
            simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hprim
          simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc
        have := ((hB i 0).mul_continuousOn (hB' 0)).add ((hB i 1).mul_continuousOn (hB' 1))
        simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
      intro i j
      refine ⟨?_, hint i j⟩
      change ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t,
        (B s * genericRoughMatrixDysonTerm32 B n s) i j) (Set.Icc (0 : ℝ) 1)
      have hprim := intervalIntegral.continuousOn_primitive_interval'
        (μ := volume) (ih i j).2 (Set.left_mem_uIcc (a := (0:ℝ)) (b := 1))
      simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hprim


theorem intervalIntegrable_sub_E02_38 {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : IntervalIntegrable f volume 0 t := by
  apply hf.mono_set
  rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact Set.Icc_subset_Icc le_rfl ht.2

theorem cumulative_mono_E02_38 {q : ℝ → ℝ} (hq : IntervalIntegrable q volume 0 1)
    (hqpos : ∀ s, 0 ≤ q s) {s t : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) (hst : s ≤ t)
    (ht : t ∈ Set.Icc (0:ℝ) 1) :
    actualCumulativeRealIntegral q s ≤ actualCumulativeRealIntegral q t := by
  unfold actualCumulativeRealIntegral
  have h := intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_sub_E02_38 hq ht) (intervalIntegrable_sub_E02_38 hq hs)
  have h2 : 0 ≤ ∫ x in s..t, q x := intervalIntegral.integral_nonneg hst (fun x _ => hqpos x)
  linarith

theorem genericDysonTerm_sub_bound_E02_38
    (B B' : ℝ → Matrix (Fin 2) (Fin 2) ℂ) (q e : ℝ → ℝ)
    (hq : IntervalIntegrable q volume 0 1) (hqpos : ∀ s, 0 ≤ q s)
    (he : IntervalIntegrable e volume 0 1) (hepos : ∀ s, 0 ≤ e s)
    (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 1)
    (hB' : ∀ i k, IntervalIntegrable (fun s => B' s i k) volume 0 1)
    (hmaj : ∀ s ∈ Set.Icc (0:ℝ) 1, actualComplexMatrixEntrySup (B s) ≤ q s)
    (hmaj' : ∀ s ∈ Set.Icc (0:ℝ) 1, actualComplexMatrixEntrySup (B' s) ≤ q s)
    (hdiff : ∀ s ∈ Set.Icc (0:ℝ) 1, actualComplexMatrixEntrySup (B s - B' s) ≤ e s) :
    ∀ (n : ℕ) (t : ℝ), t ∈ Set.Icc (0:ℝ) 1 → ∀ i j : Fin 2,
      ‖genericRoughMatrixDysonTerm32 B (n+1) t i j -
          genericRoughMatrixDysonTerm32 B' (n+1) t i j‖ ≤
        (∫ s in (0:ℝ)..1, e s) *
          (((n+1:ℝ) * 2^(n+1) / (n.factorial:ℝ)) * actualCumulativeRealIntegral q t ^ n) := by
  set ε : ℝ := ∫ s in (0:ℝ)..1, e s with hε
  set Q : ℝ → ℝ := actualCumulativeRealIntegral q with hQ
  have hQnn : ∀ t, 0 ≤ t → 0 ≤ Q t := fun t h0 =>
    intervalIntegral.integral_nonneg h0 (fun s _ => hqpos s)
  have hεt : ∀ t ∈ Set.Icc (0:ℝ) 1, ∫ s in (0:ℝ)..t, e s ≤ ε := by
    intro t ht
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sub_E02_38 he ht)
      (he.mono_set (by
        rw [Set.uIcc_of_le ht.2, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Set.Icc_subset_Icc ht.1 le_rfl) : IntervalIntegrable e volume t 1)
    have h2 : 0 ≤ ∫ x in t..1, e x := intervalIntegral.integral_nonneg ht.2 (fun x _ => hepos x)
    rw [hε]; linarith
  have hε0 : 0 ≤ ε := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hepos x)
  have hfac := genericRoughMatrixDysonTerm_factorial_bound32 B q 1 hq hqpos hmaj
  have hint (B : ℝ → Matrix (Fin 2) (Fin 2) ℂ)
      (hB : ∀ i k, IntervalIntegrable (fun s => B s i k) volume 0 1) (n : ℕ) (i j : Fin 2)
      (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
      IntervalIntegrable (fun s => (B s * genericRoughMatrixDysonTerm32 B n s) i j) volume 0 t := by
    have := (genericDysonIntegrand_integrable_E02_38 B hB n i j).2
    apply this.mono_set
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact Set.Icc_subset_Icc le_rfl ht.2
  intro n
  induction n with
  | zero =>
      intro t ht i j
      have h1 := hint B hB 0 i j t ht
      have h2 := hint B' hB' 0 i j t ht
      change ‖(∫ s in (0:ℝ)..t, (B s * genericRoughMatrixDysonTerm32 B 0 s) i j) -
          ∫ s in (0:ℝ)..t, (B' s * genericRoughMatrixDysonTerm32 B' 0 s) i j‖ ≤ _
      rw [← intervalIntegral.integral_sub h1 h2]
      have hpt : ∀ s ∈ Set.Ioc (0:ℝ) t,
          ‖(B s * genericRoughMatrixDysonTerm32 B 0 s) i j -
            (B' s * genericRoughMatrixDysonTerm32 B' 0 s) i j‖ ≤ e s := by
        intro s hs
        have : (B s * genericRoughMatrixDysonTerm32 B 0 s) i j -
            (B' s * genericRoughMatrixDysonTerm32 B' 0 s) i j = (B s - B' s) i j := by
          simp [genericRoughMatrixDysonTerm32]
        rw [this]
        exact (norm_entry_le_actualComplexMatrixEntrySup _ i j).trans
          (hdiff s ⟨hs.1.le, hs.2.trans ht.2⟩)
      have := intervalIntegral.norm_integral_le_of_norm_le ht.1
        (Filter.Eventually.of_forall hpt) (intervalIntegrable_sub_E02_38 he ht)
      refine this.trans ?_
      have hQ0 : Q t ^ 0 = 1 := pow_zero _
      simp only [hQ0, Nat.factorial_zero]
      norm_num
      nlinarith [hεt t ht]
  | succ n ih =>
      intro t ht i j
      set c : ℝ := ((n+1:ℝ) * 2^(n+1) / (n.factorial:ℝ)) with hc
      set a : ℝ := (2:ℝ)^(n+1) / ((n+1).factorial : ℝ) with ha
      have hc0 : 0 ≤ c := by rw [hc]; positivity
      have ha0 : 0 ≤ a := by rw [ha]; positivity
      have h1 := hint B hB (n+1) i j t ht
      have h2 := hint B' hB' (n+1) i j t ht
      change ‖(∫ s in (0:ℝ)..t, (B s * genericRoughMatrixDysonTerm32 B (n+1) s) i j) -
          ∫ s in (0:ℝ)..t, (B' s * genericRoughMatrixDysonTerm32 B' (n+1) s) i j‖ ≤ _
      rw [← intervalIntegral.integral_sub h1 h2]
      let G : ℝ → ℝ := fun s => 2 * a * Q t ^ (n+1) * e s + 2 * (ε * c) * (q s * Q s ^ n)
      have hGint : IntervalIntegrable G volume 0 t :=
        ((intervalIntegrable_sub_E02_38 he ht).const_mul (2 * a * Q t ^ (n+1))).add
          ((intervalIntegrable_cumulativePower q 1 hq n t ht.1 ht.2).const_mul (2 * (ε * c)))
      have hpt : ∀ s ∈ Set.Ioc (0:ℝ) t,
          ‖(B s * genericRoughMatrixDysonTerm32 B (n+1) s) i j -
            (B' s * genericRoughMatrixDysonTerm32 B' (n+1) s) i j‖ ≤ G s := by
        intro s hs
        have hs1 : s ∈ Set.Icc (0:ℝ) 1 := ⟨hs.1.le, hs.2.trans ht.2⟩
        set P := genericRoughMatrixDysonTerm32 B (n+1) s with hP
        set P' := genericRoughMatrixDysonTerm32 B' (n+1) s with hP'
        have hsplit : B s * P - B' s * P' = (B s - B' s) * P + B' s * (P - P') := by
          rw [Matrix.sub_mul, Matrix.mul_sub]; abel
        have hQs : 0 ≤ Q s := hQnn s hs.1.le
        have hPsup : actualComplexMatrixEntrySup P ≤ a * Q s ^ (n+1) := by
          unfold actualComplexMatrixEntrySup
          have := hfac (n+1) s hs1
          exact max_le (max_le (this 0 0) (this 0 1)) (max_le (this 1 0) (this 1 1))
        have hdsup : actualComplexMatrixEntrySup (P - P') ≤ ε * (c * Q s ^ n) := by
          unfold actualComplexMatrixEntrySup
          have := ih s hs1
          simp only [Matrix.sub_apply]
          exact max_le (max_le (this 0 0) (this 0 1)) (max_le (this 1 0) (this 1 1))
        have hPnn : 0 ≤ actualComplexMatrixEntrySup P :=
          (norm_nonneg _).trans (norm_entry_le_actualComplexMatrixEntrySup _ 0 0)
        have hdnn : 0 ≤ actualComplexMatrixEntrySup (P - P') :=
          (norm_nonneg _).trans (norm_entry_le_actualComplexMatrixEntrySup _ 0 0)
        have hQle : Q s ^ (n+1) ≤ Q t ^ (n+1) :=
          pow_le_pow_left₀ hQs (cumulative_mono_E02_38 hq hqpos hs1 hs.2 ht) _
        have hrw : (B s * P) i j - (B' s * P') i j =
            ((B s - B' s) * P) i j + (B' s * (P - P')) i j := by
          have := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M i j) hsplit
          simpa only [Matrix.sub_apply, Matrix.add_apply] using this
        rw [hrw]
        have hA : ‖((B s - B' s) * P) i j‖ ≤ 2 * e s * (a * Q s ^ (n+1)) :=
          (norm_entry_le_actualComplexMatrixEntrySup _ i j).trans
            ((actualComplexMatrixEntrySup_mul_le _ _).trans
              (mul_le_mul (mul_le_mul_of_nonneg_left (hdiff s hs1) (by norm_num)) hPsup hPnn
                (mul_nonneg (by norm_num) (hepos s))))
        have hBd : ‖(B' s * (P - P')) i j‖ ≤ 2 * q s * (ε * (c * Q s ^ n)) :=
          (norm_entry_le_actualComplexMatrixEntrySup _ i j).trans
            ((actualComplexMatrixEntrySup_mul_le _ _).trans
              (mul_le_mul (mul_le_mul_of_nonneg_left (hmaj' s hs1) (by norm_num)) hdsup hdnn
                (mul_nonneg (by norm_num) (hqpos s))))
        have hfirst : 2 * e s * (a * Q s ^ (n+1)) ≤ 2 * a * Q t ^ (n+1) * e s := by
          have := mul_le_mul_of_nonneg_left hQle (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ha0) (hepos s))
          nlinarith [this]
        calc _ ≤ ‖((B s - B' s) * P) i j‖ + ‖(B' s * (P - P')) i j‖ := norm_add_le _ _
          _ ≤ 2 * e s * (a * Q s ^ (n+1)) + 2 * q s * (ε * (c * Q s ^ n)) := add_le_add hA hBd
          _ ≤ G s := by
            show _ ≤ 2 * a * Q t ^ (n+1) * e s + 2 * (ε * c) * (q s * Q s ^ n)
            nlinarith [hfirst]
      refine (intervalIntegral.norm_integral_le_of_norm_le ht.1
        (Filter.Eventually.of_forall hpt) hGint).trans ?_
      have hcum := intervalIntegral_cumulativePower_eq q 1 hq n t ht.1 ht.2
      have hGeq : (∫ s in (0:ℝ)..t, G s) =
          2 * a * Q t ^ (n+1) * (∫ s in (0:ℝ)..t, e s) +
            2 * (ε * c) * (Q t ^ (n+1) / (n+1:ℝ)) := by
        show (∫ s in (0:ℝ)..t, (2 * a * Q t ^ (n+1) * e s + 2 * (ε * c) * (q s * Q s ^ n))) = _
        rw [intervalIntegral.integral_add
          ((intervalIntegrable_sub_E02_38 he ht).const_mul (2 * a * Q t ^ (n+1)))
          ((intervalIntegrable_cumulativePower q 1 hq n t ht.1 ht.2).const_mul (2 * (ε * c))),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hcum]
      rw [hGeq]
      have hQt : 0 ≤ Q t ^ (n+1) := pow_nonneg (hQnn t ht.1) _
      have hconst : 2 * a + 2 * c / (n+1:ℝ) =
          ((n+1+1:ℝ) * 2^(n+1+1) / ((n+1).factorial:ℝ)) := by
        rw [ha, hc, Nat.factorial_succ]
        push_cast
        have hn1 : (n+1:ℝ) ≠ 0 := by positivity
        have hf : (n.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
        field_simp
        ring
      calc 2 * a * Q t ^ (n+1) * (∫ s in (0:ℝ)..t, e s) +
            2 * (ε * c) * (Q t ^ (n+1) / (n+1:ℝ))
          ≤ 2 * a * Q t ^ (n+1) * ε + 2 * (ε * c) * (Q t ^ (n+1) / (n+1:ℝ)) := by
            have := mul_le_mul_of_nonneg_left (hεt t ht) (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ha0) hQt)
            linarith
        _ = ε * ((2 * a + 2 * c / (n+1:ℝ)) * Q t ^ (n+1)) := by ring
        _ = _ := by rw [hconst]; push_cast; ring_nf


theorem actualComplexZsDysonTerm_eq_generic_E02_38 (U : ℝ → ℂ) (z : ℂ) (n : ℕ) :
    actualComplexZsDysonTerm U z n = genericRoughMatrixDysonTerm32 (zsCoefficientComplex U z) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext t
      ext i j
      change (∫ s in (0 : ℝ)..t, (zsCoefficientComplex U z s * actualComplexZsDysonTerm U z n s) i j) =
        ∫ s in (0 : ℝ)..t, (zsCoefficientComplex U z s * genericRoughMatrixDysonTerm32 (zsCoefficientComplex U z) n s) i j
      rw [ih]

theorem zsCoefficient_entries_integrable_E02_38 (U : ℝ → ℂ) (z : ℂ)
    (hU : IntervalIntegrable U volume 0 1) :
    ∀ i k, IntervalIntegrable (fun s => zsCoefficientComplex U z s i k) volume 0 1 := by
  have hUs : IntervalIntegrable (fun s => (starRingEnd ℂ) (U s)) volume 0 1 := by
    have hm : AEStronglyMeasurable (fun s => (starRingEnd ℂ) (U s))
        (volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
      simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1), Pi.star_apply]
        using! hU.aestronglyMeasurable.star
    exact hU.mono_fun hm (Filter.Eventually.of_forall (fun s => by simp))
  intro i k
  fin_cases i <;> fin_cases k <;> simp [zsCoefficientComplex]
  · exact hU.const_mul Complex.I
  · exact (hUs.const_mul Complex.I).neg

theorem zsCoefficient_sub_sup_E02_38 (U U' : ℝ → ℂ) (z : ℂ) (s : ℝ) :
    actualComplexMatrixEntrySup (zsCoefficientComplex U z s - zsCoefficientComplex U' z s) ≤
      ‖U s - U' s‖ := by
  have h3 : ‖(starRingEnd ℂ) (U s) - (starRingEnd ℂ) (U' s)‖ = ‖U s - U' s‖ := by
    rw [← map_sub (starRingEnd ℂ)]; exact RCLike.norm_conj _
  have h2 : ‖-(Complex.I * (starRingEnd ℂ) (U s)) + Complex.I * (starRingEnd ℂ) (U' s)‖ =
      ‖U s - U' s‖ := by
    rw [show -(Complex.I * (starRingEnd ℂ) (U s)) + Complex.I * (starRingEnd ℂ) (U' s) =
      -(Complex.I * ((starRingEnd ℂ) (U s) - (starRingEnd ℂ) (U' s))) by ring,
      norm_neg, norm_mul, Complex.norm_I, one_mul, h3]
  unfold actualComplexMatrixEntrySup
  simp [zsCoefficientComplex, ← mul_sub, h2]

theorem dysonTsum_sub_entry_E02_38 (U U' : ℝ → ℂ) (z : ℂ) (Z M : ℝ)
    (hU : IntervalIntegrable U volume 0 1) (hU' : IntervalIntegrable U' volume 0 1)
    (hz : ‖z‖ ≤ Z)
    (hM : Z + (∫ s in (0:ℝ)..1, ‖U s‖) + (∫ s in (0:ℝ)..1, ‖U' s‖) ≤ M) (i j : Fin 2) :
    ‖actualComplexZsDysonTsum U z 1 i j - actualComplexZsDysonTsum U' z 1 i j‖ ≤
      2 * (∫ s in (0:ℝ)..1, ‖U s - U' s‖) * ∑' n : ℕ, (4 * M) ^ n / (n.factorial : ℝ) := by
  set ε : ℝ := ∫ s in (0:ℝ)..1, ‖U s - U' s‖ with hε
  let q : ℝ → ℝ := fun s => Z + ‖U s‖ + ‖U' s‖
  let e : ℝ → ℝ := fun s => ‖U s - U' s‖
  have hq : IntervalIntegrable q volume 0 1 :=
    (intervalIntegrable_const.add hU.norm).add hU'.norm
  have hqpos : ∀ s, 0 ≤ q s := by
    intro s
    have hZ : 0 ≤ Z := (norm_nonneg z).trans hz
    simp only [q]; positivity
  have he : IntervalIntegrable e volume 0 1 := (hU.sub hU').norm
  have hepos : ∀ s, 0 ≤ e s := fun s => norm_nonneg _
  have hB := zsCoefficient_entries_integrable_E02_38 U z hU
  have hB' := zsCoefficient_entries_integrable_E02_38 U' z hU'
  have hmaj : ∀ s ∈ Set.Icc (0:ℝ) 1, actualComplexMatrixEntrySup (zsCoefficientComplex U z s) ≤ q s := by
    intro s _
    have := actualComplexZsCoefficient_entrySup_bound U z s Z ‖U s‖ hz le_rfl
    simp only [q]; linarith [norm_nonneg (U' s)]
  have hmaj' : ∀ s ∈ Set.Icc (0:ℝ) 1, actualComplexMatrixEntrySup (zsCoefficientComplex U' z s) ≤ q s := by
    intro s _
    have := actualComplexZsCoefficient_entrySup_bound U' z s Z ‖U' s‖ hz le_rfl
    simp only [q]; linarith [norm_nonneg (U s)]
  have hdiff : ∀ s ∈ Set.Icc (0:ℝ) 1, actualComplexMatrixEntrySup
      (zsCoefficientComplex U z s - zsCoefficientComplex U' z s) ≤ e s :=
    fun s _ => zsCoefficient_sub_sup_E02_38 U U' z s
  have hsub := genericDysonTerm_sub_bound_E02_38 _ _ q e hq hqpos he hepos hB hB' hmaj hmaj' hdiff
  have hfac := genericRoughMatrixDysonTerm_factorial_bound32 _ q 1 hq hqpos hmaj
  have hfac' := genericRoughMatrixDysonTerm_factorial_bound32 _ q 1 hq hqpos hmaj'
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨by norm_num, le_rfl⟩
  have hQ1 : actualCumulativeRealIntegral q 1 ≤ M := by
    have : actualCumulativeRealIntegral q 1 = Z + (∫ s in (0:ℝ)..1, ‖U s‖) + (∫ s in (0:ℝ)..1, ‖U' s‖) := by
      unfold actualCumulativeRealIntegral
      simp only [q]
      rw [intervalIntegral.integral_add (intervalIntegrable_const.add hU.norm) hU'.norm,
        intervalIntegral.integral_add intervalIntegrable_const hU.norm]
      simp
    linarith
  have hQ1nn : 0 ≤ actualCumulativeRealIntegral q 1 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => hqpos s)
  have hM0 : 0 ≤ M := hQ1nn.trans hQ1
  have hsum : ∀ (V : ℝ → ℂ) (hV : ∀ n (i j : Fin 2), ‖genericRoughMatrixDysonTerm32 (zsCoefficientComplex V z) n 1 i j‖ ≤
      2 ^ n / (n.factorial : ℝ) * actualCumulativeRealIntegral q 1 ^ n),
      Summable (fun n : ℕ => actualComplexZsDysonTerm V z n 1 i j) := by
    intro V hV
    refine Summable.of_norm_bounded
      ((Real.summable_pow_div_factorial (2 * M))) (fun n => ?_)
    rw [actualComplexZsDysonTerm_eq_generic_E02_38]
    refine (hV n i j).trans ?_
    rw [mul_pow]
    have := pow_le_pow_left₀ hQ1nn hQ1 n
    have hf : 0 ≤ (n.factorial : ℝ) := by positivity
    calc 2 ^ n / (n.factorial : ℝ) * actualCumulativeRealIntegral q 1 ^ n
        ≤ 2 ^ n / (n.factorial : ℝ) * M ^ n := by gcongr
      _ = 2 ^ n * M ^ n / (n.factorial : ℝ) := by ring
  have hS := hsum U (fun n i j => hfac n 1 h1 i j)
  have hS' := hsum U' (fun n i j => hfac' n 1 h1 i j)
  have hd : ∀ n : ℕ, ‖actualComplexZsDysonTerm U z (n+1) 1 i j - actualComplexZsDysonTerm U' z (n+1) 1 i j‖ ≤
      2 * ε * ((4 * M) ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [actualComplexZsDysonTerm_eq_generic_E02_38, actualComplexZsDysonTerm_eq_generic_E02_38]
    refine le_trans (hsub n 1 h1 i j) ?_
    show ε * _ ≤ _
    have hε0 : 0 ≤ ε := intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hepos x)
    have hpow := pow_le_pow_left₀ hQ1nn hQ1 n
    have hn : ((n:ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have hf : 0 < (n.factorial : ℝ) := by positivity
    have hc : (((n:ℝ)+1) * 2 ^ (n+1) / (n.factorial : ℝ)) ≤ 2 * 4 ^ n / (n.factorial : ℝ) := by
      apply div_le_div_of_nonneg_right _ hf.le
      calc ((n:ℝ)+1) * 2 ^ (n+1) ≤ 2 ^ n * 2 ^ (n+1) := by gcongr
        _ = 2 * 4 ^ n := by
          rw [pow_succ, show (4:ℝ) = 2 * 2 by norm_num, mul_pow]; ring
    calc ε * ((((n:ℝ)+1) * 2 ^ (n+1) / (n.factorial : ℝ)) * actualCumulativeRealIntegral q 1 ^ n)
        ≤ ε * ((2 * 4 ^ n / (n.factorial : ℝ)) * M ^ n) := by
          gcongr
      _ = 2 * ε * ((4 * M) ^ n / (n.factorial : ℝ)) := by
          rw [mul_pow]; ring
  have hdS : Summable (fun n : ℕ => actualComplexZsDysonTerm U z n 1 i j - actualComplexZsDysonTerm U' z n 1 i j) :=
    hS.sub hS'
  have hg : HasSum (fun n : ℕ => 2 * ε * ((4 * M) ^ n / (n.factorial : ℝ)))
      (2 * ε * ∑' n : ℕ, (4 * M) ^ n / (n.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial (4 * M)).hasSum.mul_left (2 * ε)
  show ‖(∑' n, actualComplexZsDysonTerm U z n 1 i j) - ∑' n, actualComplexZsDysonTerm U' z n 1 i j‖ ≤ _
  rw [← Summable.tsum_sub hS hS', Summable.tsum_eq_zero_add hdS]
  have h0 : actualComplexZsDysonTerm U z 0 1 i j - actualComplexZsDysonTerm U' z 0 1 i j = 0 := by
    simp [actualComplexZsDysonTerm]
  rw [h0, zero_add]
  exact tsum_of_norm_bounded hg hd


theorem cover_intervalIntegrable_unit_E02_38 (u : PhysicalL2) :
    IntervalIntegrable (fun s : ℝ => naturalPhysicalCoverL2 u (s : SpectralCircle))
      volume 0 1 := by
  apply (naturalPhysicalCoverL2_intervalIntegrable_doubled u).mono_set
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 2)]
  exact Set.Icc_subset_Icc le_rfl (by norm_num)

theorem cover_sub_integral_le_E02_38 (u u' : PhysicalL2) :
    (∫ s in (0:ℝ)..1, ‖naturalPhysicalCoverL2 u (s : SpectralCircle) -
        naturalPhysicalCoverL2 u' (s : SpectralCircle)‖) ≤ ‖u - u'‖ := by
  have hae : (fun t : ℝ => naturalPhysicalCoverL2 (u - u') (t : SpectralCircle))
      =ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      (fun t : ℝ => naturalPhysicalCoverL2 u (t : SpectralCircle) -
        naturalPhysicalCoverL2 u' (t : SpectralCircle)) := by
    rw [map_sub]
    simpa only [Pi.sub_apply] using
      spectral_ae_pullback_first_half (Lp.coeFn_sub (naturalPhysicalCoverL2 u) (naturalPhysicalCoverL2 u'))
  have h := (ae_restrict_iff' measurableSet_Ioc).1 hae
  have heq : (∫ s in (0:ℝ)..1, ‖naturalPhysicalCoverL2 u (s : SpectralCircle) -
        naturalPhysicalCoverL2 u' (s : SpectralCircle)‖) =
      ∫ s in (0:ℝ)..1, ‖naturalPhysicalCoverL2 (u - u') (s : SpectralCircle)‖ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [h] with x hx hxI
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hxI
    rw [hx hxI]
  rw [heq]
  exact actualPhysicalRawCover_subintervalIntegral_norm_le33 (u - u') 1 ⟨by norm_num, le_rfl⟩

theorem actualPhysicalUnitHalfTrace_lipschitz_E02_38 :
    ∀ R Z : ℝ, 0 ≤ R → 0 ≤ Z → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u u' : PhysicalL2, ‖u‖ ≤ R → ‖u'‖ ≤ R → ∀ z : ℂ, ‖z‖ ≤ Z →
        ‖actualPhysicalUnitHalfTrace32 u z - actualPhysicalUnitHalfTrace32 u' z‖ ≤
          C * ‖u - u'‖ := by
  intro R Z hR hZ
  set K : ℝ := ∑' n : ℕ, (4 * (Z + 2 * R)) ^ n / (n.factorial : ℝ) with hK
  have hK0 : 0 ≤ K := tsum_nonneg (fun n => by
    have : 0 ≤ 4 * (Z + 2 * R) := by positivity
    positivity)
  refine ⟨2 * K, by positivity, ?_⟩
  intro u u' hu hu' z hz
  let U : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u (s : SpectralCircle)
  let U' : ℝ → ℂ := fun s => naturalPhysicalCoverL2 u' (s : SpectralCircle)
  have hUi := cover_intervalIntegrable_unit_E02_38 u
  have hUi' := cover_intervalIntegrable_unit_E02_38 u'
  have hM : Z + (∫ s in (0:ℝ)..1, ‖U s‖) + (∫ s in (0:ℝ)..1, ‖U' s‖) ≤ Z + 2 * R := by
    have h1 := actualPhysicalRawCover_subintervalIntegral_norm_le33 u 1 ⟨by norm_num, le_rfl⟩
    have h2 := actualPhysicalRawCover_subintervalIntegral_norm_le33 u' 1 ⟨by norm_num, le_rfl⟩
    simp only [U, U']
    linarith
  have hε := cover_sub_integral_le_E02_38 u u'
  have hent := fun i j => dysonTsum_sub_entry_E02_38 U U' z Z (Z + 2 * R) hUi hUi' hz hM i j
  have hε0 : 0 ≤ ∫ s in (0:ℝ)..1, ‖U s - U' s‖ :=
    intervalIntegral.integral_nonneg (by norm_num) (fun s _ => norm_nonneg _)
  have e00 := hent 0 0
  have e11 := hent 1 1
  have hbd : 2 * (∫ s in (0:ℝ)..1, ‖U s - U' s‖) * K ≤ 2 * K * ‖u - u'‖ := by
    have := mul_le_mul_of_nonneg_left hε hK0
    nlinarith
  unfold actualPhysicalUnitHalfTrace32
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two]
  have hdiv : ∀ a b : ℂ, a / 2 - b / 2 = (a - b) / 2 := fun a b => by ring
  rw [hdiv, norm_div, show ‖(2:ℂ)‖ = 2 by simp]
  set A := actualComplexZsDysonTsum U z 1 with hA
  set A' := actualComplexZsDysonTsum U' z 1 with hA'
  have : ‖A 0 0 + A 1 1 - (A' 0 0 + A' 1 1)‖ ≤ ‖A 0 0 - A' 0 0‖ + ‖A 1 1 - A' 1 1‖ := by
    rw [show A 0 0 + A 1 1 - (A' 0 0 + A' 1 1) = (A 0 0 - A' 0 0) + (A 1 1 - A' 1 1) by ring]
    exact norm_add_le _ _
  rw [div_le_iff₀ (by norm_num)]
  linarith

end NlsGge.SpectralFoundations
end
