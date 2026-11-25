import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB6AC

/-! # Track B, package 3: Fejér pairing on the unit circle

`fejP N a b = N⁻¹ Σ_{j,k<N} conj(a(k-j)) b(k-j)` (weights `(N-|n|)₊/N`). For integrable `h, G`,
`fejP N ĥ Ĝ = ∬ Φ_N(x,z) conj(h x) G z` with the nonnegative Fejér kernel
`Φ_N(x,z) = N⁻¹ |Σ_{k<N} e_k(x) conj(e_k(z))|²` whose two marginals are `1` (`fejer_kernel_identity`,
`integral_fejK_right`, `integral_fejK_left`). The weights tend to `1` (`fejW_tendsto`).
-/

namespace LiebLiniger.FixedPeriod.ALLS.PdeB
open MeasureTheory Filter Topology NlsGge.Pilot
open scoped ComplexConjugate
set_option autoImplicit false
noncomputable section

/-- Fejér pairing of two coefficient sequences. -/
def fejP (N : ℕ) (a b : ℤ → ℂ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
    conj (a ((k : ℤ) - j)) * b ((k : ℤ) - j)

/-- Dirichlet-type kernel `Σ_{k<N} e_k(x) conj(e_k(z))`. -/
def dirK (N : ℕ) (x z : PhysicalCircle) : ℂ :=
  ∑ k ∈ Finset.range N, fourier (k : ℤ) x * conj (fourier (k : ℤ) z)

/-- Fejér kernel on `𝕋 × 𝕋`. -/
def fejK (N : ℕ) (p : PhysicalCircle × PhysicalCircle) : ℝ :=
  (N : ℝ)⁻¹ * ‖dirK N p.1 p.2‖ ^ 2

theorem fejK_nonneg (N : ℕ) (p : PhysicalCircle × PhysicalCircle) : 0 ≤ fejK N p := by
  unfold fejK; positivity

theorem norm_fourier_apply (n : ℤ) (x : PhysicalCircle) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

theorem conj_fourier_mul_self (n : ℤ) (x : PhysicalCircle) :
    conj (fourier n x) * fourier n x = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_fourier_apply]
  norm_num

theorem continuous_dirK (N : ℕ) : Continuous fun p : PhysicalCircle × PhysicalCircle =>
    dirK N p.1 p.2 := by
  unfold dirK
  refine continuous_finsetSum _ fun k _ => ?_
  exact ((map_continuous (fourier (k : ℤ))).comp continuous_fst).mul
    (Complex.continuous_conj.comp ((map_continuous (fourier (k : ℤ))).comp continuous_snd))

theorem continuous_fejK (N : ℕ) : Continuous (fejK N) := by
  unfold fejK
  exact continuous_const.mul ((continuous_dirK N).norm.pow 2)

theorem norm_dirK_le (N : ℕ) (x z : PhysicalCircle) : ‖dirK N x z‖ ≤ N := by
  unfold dirK
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp

theorem fejK_le (N : ℕ) (p : PhysicalCircle × PhysicalCircle) : fejK N p ≤ N := by
  unfold fejK
  rcases Nat.eq_zero_or_pos N with h | h
  · simp [h]
  · have hN : (0 : ℝ) < N := by exact_mod_cast h
    have h1 := norm_dirK_le N p.1 p.2
    have h2 : ‖dirK N p.1 p.2‖ ^ 2 ≤ (N : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc (N : ℝ)⁻¹ * ‖dirK N p.1 p.2‖ ^ 2 ≤ (N : ℝ)⁻¹ * (N : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (N : ℝ) := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]

/-- Orthonormality of the characters for normalized Haar measure. -/
theorem integral_conj_fourier_mul (i j : ℤ) :
    ∫ x, conj (fourier i x) * fourier j x ∂spatialMeasure = if i = j then 1 else 0 := by
  have h := orthonormal_iff_ite.1 (orthonormal_fourier (T := 1)) i j
  rw [ContinuousMap.inner_toLp] at h
  rw [← h]
  unfold spatialMeasure
  exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)

theorem fourier_neg_sub (j k : ℤ) (x : PhysicalCircle) :
    fourier (-(k - j)) x = conj (fourier k x) * fourier j x := by
  rw [show -(k - j) = -k + j by ring, fourier_add, fourier_neg]

theorem physicalFourier_sub_eq (f : PhysicalCircle → ℂ) (j k : ℤ) :
    physicalFourier f (k - j) = ∫ x, conj (fourier k x) * fourier j x * f x ∂spatialMeasure := by
  unfold physicalFourier fourierCoeff spatialMeasure
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [smul_eq_mul]
  rw [fourier_neg_sub]

theorem integrable_char_mul {f : PhysicalCircle → ℂ} (hf : Integrable f spatialMeasure) (k j : ℤ) :
    Integrable (fun x => conj (fourier k x) * fourier j x * f x) spatialMeasure := by
  refine hf.bdd_mul (c := 1) ?_ (ae_of_all _ fun x => ?_)
  · exact ((Complex.continuous_conj.comp (map_continuous (fourier k))).mul
      (map_continuous (fourier j))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_conj, norm_fourier_apply, norm_fourier_apply, one_mul]

theorem integrable_char_mul' {f : PhysicalCircle → ℂ} (hf : Integrable f spatialMeasure) (k j : ℤ) :
    Integrable (fun x => fourier k x * conj (fourier j x) * conj (f x)) spatialMeasure := by
  refine (integrable_conj_fun hf).bdd_mul (c := 1) ?_ (ae_of_all _ fun x => ?_)
  · exact ((map_continuous (fourier k)).mul
      (Complex.continuous_conj.comp (map_continuous (fourier j)))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_conj, norm_fourier_apply, norm_fourier_apply, one_mul]

theorem isProbabilityMeasure_spatial : IsProbabilityMeasure spatialMeasure := by
  unfold spatialMeasure; infer_instance

attribute [local instance] isProbabilityMeasure_spatial

/-- **Kernel identity** for the Fejér pairing. -/
theorem fejer_kernel_identity (N : ℕ) {h G : PhysicalCircle → ℂ}
    (hh : Integrable h spatialMeasure) (hG : Integrable G spatialMeasure) :
    fejP N (physicalFourier h) (physicalFourier G) =
      ∫ p, (fejK N p : ℂ) * (conj (h p.1) * G p.2) ∂(spatialMeasure.prod spatialMeasure) := by
  have hterm : ∀ j k : ℕ, conj (physicalFourier h ((k : ℤ) - j)) *
      physicalFourier G ((k : ℤ) - j) =
      ∫ p, (fourier (k : ℤ) p.1 * conj (fourier (j : ℤ) p.1) * conj (h p.1)) *
        (conj (fourier (k : ℤ) p.2) * fourier (j : ℤ) p.2 * G p.2)
        ∂(spatialMeasure.prod spatialMeasure) := by
    intro j k
    have hpm := integral_prod_mul (μ := spatialMeasure) (ν := spatialMeasure)
      (fun x => fourier (k : ℤ) x * conj (fourier (j : ℤ) x) * conj (h x))
      (fun z => conj (fourier (k : ℤ) z) * fourier (j : ℤ) z * G z)
    rw [hpm, physicalFourier_sub_eq, physicalFourier_sub_eq, ← integral_conj]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [map_mul, Complex.conj_conj]
  have hint : ∀ j k : ℕ, Integrable (fun p : PhysicalCircle × PhysicalCircle =>
      (fourier (k : ℤ) p.1 * conj (fourier (j : ℤ) p.1) * conj (h p.1)) *
        (conj (fourier (k : ℤ) p.2) * fourier (j : ℤ) p.2 * G p.2))
      (spatialMeasure.prod spatialMeasure) := fun j k =>
    (integrable_char_mul' hh k j).mul_prod (integrable_char_mul hG k j)
  unfold fejP
  simp_rw [hterm]
  have hsum : (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
      ∫ p, (fourier (k : ℤ) p.1 * conj (fourier (j : ℤ) p.1) * conj (h p.1)) *
        (conj (fourier (k : ℤ) p.2) * fourier (j : ℤ) p.2 * G p.2)
        ∂(spatialMeasure.prod spatialMeasure)) =
      ∫ p, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        (fourier (k : ℤ) p.1 * conj (fourier (j : ℤ) p.1) * conj (h p.1)) *
          (conj (fourier (k : ℤ) p.2) * fourier (j : ℤ) p.2 * G p.2)
        ∂(spatialMeasure.prod spatialMeasure) := by
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ (fun k _ => hint j k)]
  rw [hsum, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  have hcast : ((fejK N p : ℝ) : ℂ) =
      (N : ℂ)⁻¹ * (dirK N p.1 p.2 * conj (dirK N p.1 p.2)) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    unfold fejK
    push_cast
    ring
  simp only
  rw [hcast, mul_assoc]
  congr 1
  unfold dirK
  conv_lhs => rw [Finset.sum_comm]
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring

theorem integrable_cont_bdd {f : PhysicalCircle → ℂ} (hf : Continuous f) (hb : ∀ x, ‖f x‖ ≤ 1) :
    Integrable f spatialMeasure := by
  have h := (integrable_const (μ := spatialMeasure) (1 : ℂ)).bdd_mul hf.aestronglyMeasurable (ae_of_all _ hb)
  simpa using h

theorem fejK_cast (N : ℕ) (p : PhysicalCircle × PhysicalCircle) :
    ((fejK N p : ℝ) : ℂ) = (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (fourier (k : ℤ) p.1 * conj (fourier (j : ℤ) p.1)) *
        (conj (fourier (k : ℤ) p.2) * fourier (j : ℤ) p.2) := by
  have hcast : ((fejK N p : ℝ) : ℂ) =
      (N : ℂ)⁻¹ * (dirK N p.1 p.2 * conj (dirK N p.1 p.2)) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    unfold fejK
    push_cast
    ring
  rw [hcast]
  congr 1
  unfold dirK
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, Complex.conj_conj]
  ring

theorem fourier_mul_conj_self (n : ℤ) (x : PhysicalCircle) :
    fourier n x * conj (fourier n x) = 1 := by
  rw [mul_comm, conj_fourier_mul_self]

/-- Right marginal of the Fejér kernel. -/
theorem integral_fejK_right (N : ℕ) (hN : 0 < N) (x : PhysicalCircle) :
    ∫ z, fejK N (x, z) ∂spatialMeasure = 1 := by
  have hc : ((∫ z, fejK N (x, z) ∂spatialMeasure : ℝ) : ℂ) = 1 := by
    rw [← integral_complex_ofReal]
    simp_rw [fejK_cast]
    have hi : ∀ k j : ℕ, Integrable (fun z : PhysicalCircle =>
        (fourier (k : ℤ) x * conj (fourier (j : ℤ) x)) *
          (conj (fourier (k : ℤ) z) * fourier (j : ℤ) z)) spatialMeasure := fun k j =>
      (integrable_cont_bdd (f := fun z => conj (fourier (k : ℤ) z) * fourier (j : ℤ) z)
        ((Complex.continuous_conj.comp (map_continuous (fourier (k : ℤ)))).mul
        (map_continuous (fourier (j : ℤ)))) (fun z => by
          simp only [norm_mul, Complex.norm_conj, norm_fourier_apply, one_mul, le_refl])).const_mul _
    rw [integral_const_mul, integral_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun j _ => hi k j))]
    have hin : ∀ k ∈ Finset.range N, (∫ z, ∑ j ∈ Finset.range N,
        (fourier (k : ℤ) x * conj (fourier (j : ℤ) x)) *
          (conj (fourier (k : ℤ) z) * fourier (j : ℤ) z) ∂spatialMeasure) = 1 := by
      intro k hk
      rw [integral_finsetSum _ (fun j _ => hi k j)]
      simp_rw [integral_const_mul, integral_conj_fourier_mul, Nat.cast_inj, mul_ite, mul_one,
        mul_zero]
      simp only [Finset.sum_ite_eq, hk, ↓reduceIte, fourier_mul_conj_self]
    rw [Finset.sum_congr rfl hin]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')
  exact_mod_cast hc

/-- Left marginal of the Fejér kernel. -/
theorem integral_fejK_left (N : ℕ) (hN : 0 < N) (z : PhysicalCircle) :
    ∫ x, fejK N (x, z) ∂spatialMeasure = 1 := by
  have hc : ((∫ x, fejK N (x, z) ∂spatialMeasure : ℝ) : ℂ) = 1 := by
    rw [← integral_complex_ofReal]
    simp_rw [fejK_cast]
    have hi : ∀ k j : ℕ, Integrable (fun x : PhysicalCircle =>
        (fourier (k : ℤ) x * conj (fourier (j : ℤ) x)) *
          (conj (fourier (k : ℤ) z) * fourier (j : ℤ) z)) spatialMeasure := fun k j =>
      (integrable_cont_bdd (f := fun x => fourier (k : ℤ) x * conj (fourier (j : ℤ) x))
        ((map_continuous (fourier (k : ℤ))).mul
        (Complex.continuous_conj.comp (map_continuous (fourier (j : ℤ))))) (fun x => by
          simp only [norm_mul, Complex.norm_conj, norm_fourier_apply, one_mul, le_refl])).mul_const _
    rw [integral_const_mul, integral_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun j _ => hi k j))]
    have hin : ∀ k ∈ Finset.range N, (∫ x, ∑ j ∈ Finset.range N,
        (fourier (k : ℤ) x * conj (fourier (j : ℤ) x)) *
          (conj (fourier (k : ℤ) z) * fourier (j : ℤ) z) ∂spatialMeasure) = 1 := by
      intro k hk
      rw [integral_finsetSum _ (fun j _ => hi k j)]
      have hx : ∀ j : ℕ, (∫ x, fourier (k : ℤ) x * conj (fourier (j : ℤ) x) ∂spatialMeasure) =
          if (j : ℤ) = k then 1 else 0 := fun j => by
        rw [← integral_conj_fourier_mul]
        exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
      simp_rw [integral_mul_const, hx, Nat.cast_inj, ite_mul, one_mul, zero_mul]
      simp only [Finset.sum_ite_eq', hk, ↓reduceIte, conj_fourier_mul_self]
    rw [Finset.sum_congr rfl hin]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast hN.ne')
  exact_mod_cast hc

/-! ### Fejér weights -/

/-- Number of pairs `(j,k) ∈ [0,N)²` with `k - j = i`. -/
def cntZ (N : ℕ) (i : ℤ) : ℤ :=
  ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, if (k : ℤ) - j = i then 1 else 0

theorem sum_range_ite_eq (M : ℕ) (m : ℤ) :
    (∑ k ∈ Finset.range M, if (k : ℤ) = m then (1 : ℤ) else 0) =
      if 0 ≤ m ∧ m < M then 1 else 0 := by
  split_ifs with h
  · have hk : m.toNat ∈ Finset.range M := by
      rw [Finset.mem_range]; omega
    rw [Finset.sum_eq_single_of_mem m.toNat hk (fun k _ hne => by split_ifs <;> omega)]
    split_ifs <;> omega
  · refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    split_ifs <;> omega

theorem cntZ_succ (N : ℕ) (i : ℤ) :
    cntZ (N + 1) i = cntZ N i + if -(N : ℤ) ≤ i ∧ i ≤ N then 1 else 0 := by
  unfold cntZ
  have hrow : (∑ k ∈ Finset.range (N + 1), if (k : ℤ) - (N : ℕ) = i then (1 : ℤ) else 0) =
      if -(N : ℤ) ≤ i ∧ i ≤ 0 then 1 else 0 := by
    have h := sum_range_ite_eq (N + 1) (N + i)
    have e : ∀ k : ℕ, ((k : ℤ) - (N : ℕ) = i) = ((k : ℤ) = N + i) := fun k => by
      apply propext; omega
    simp_rw [e, h]
    congr 1
    apply propext; push_cast; omega
  have hcol : (∑ j ∈ Finset.range N, if ((N : ℕ) : ℤ) - j = i then (1 : ℤ) else 0) =
      if 0 < i ∧ i ≤ N then 1 else 0 := by
    have h := sum_range_ite_eq N (N - i)
    have e : ∀ j : ℕ, (((N : ℕ) : ℤ) - j = i) = ((j : ℤ) = N - i) := fun j => by
      apply propext; omega
    simp_rw [e, h]
    congr 1
    apply propext; omega
  rw [Finset.sum_range_succ, Finset.sum_congr rfl (fun j _ => Finset.sum_range_succ _ N),
    Finset.sum_add_distrib, hrow, hcol, add_assoc]
  congr 1
  split_ifs <;> omega

theorem cntZ_nonneg (N : ℕ) (i : ℤ) : 0 ≤ cntZ N i :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

theorem cntZ_le (N : ℕ) (i : ℤ) : cntZ N i ≤ N := by
  induction N with
  | zero => simp [cntZ]
  | succ N ih =>
    rw [cntZ_succ]
    push_cast
    split_ifs <;> linarith

theorem cntZ_ge (N : ℕ) (i : ℤ) : (N : ℤ) - |i| ≤ cntZ N i := by
  induction N with
  | zero => simp [cntZ]
  | succ N ih =>
    by_cases h : |i| ≤ N
    · rw [cntZ_succ]
      split_ifs with h2
      · push_cast
        linarith
      · exact absurd (abs_le.1 h) h2
    · push_cast
      have := cntZ_nonneg (N + 1) i
      linarith

/-- Fejér pairing with a single mode in the first slot. -/
theorem fejP_single (N : ℕ) (i : ℤ) (b : ℤ → ℂ) :
    fejP N (fun n => if n = i then 1 else 0) b = ((N : ℝ)⁻¹ * (cntZ N i : ℝ) : ℝ) * b i := by
  unfold fejP cntZ
  push_cast
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with hc
  · rw [hc]; simp
  · simp

theorem fejW_tendsto (i : ℤ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (cntZ N i : ℝ)) atTop (𝓝 1) := by
  have hlow : Tendsto (fun N : ℕ => 1 - |(i : ℝ)| * (N : ℝ)⁻¹) atTop (𝓝 1) := by
    have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul |(i : ℝ)|
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have h := cntZ_ge N i
    have h' : (N : ℝ) - |(i : ℝ)| ≤ (cntZ N i : ℝ) := by exact_mod_cast h
    rw [show 1 - |(i : ℝ)| * (N : ℝ)⁻¹ = (N : ℝ)⁻¹ * ((N : ℝ) - |(i : ℝ)|) by field_simp]
    exact mul_le_mul_of_nonneg_left h' (by positivity)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have h' : (cntZ N i : ℝ) ≤ N := by exact_mod_cast cntZ_le N i
    calc (N : ℝ)⁻¹ * (cntZ N i : ℝ) ≤ (N : ℝ)⁻¹ * N := mul_le_mul_of_nonneg_left h' (by positivity)
      _ = 1 := inv_mul_cancel₀ hNr.ne'

theorem fejP_single_tendsto (i : ℤ) (b : ℤ → ℂ) :
    Tendsto (fun N => fejP N (fun n => if n = i then 1 else 0) b) atTop (𝓝 (b i)) := by
  simp_rw [fejP_single]
  have h := ((Complex.continuous_ofReal.tendsto 1).comp (fejW_tendsto i)).mul_const (b i)
  simpa using h

end

end LiebLiniger.FixedPeriod.ALLS.PdeB
