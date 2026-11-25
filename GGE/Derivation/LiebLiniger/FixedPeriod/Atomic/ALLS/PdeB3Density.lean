import LiebLiniger.FixedPeriod.Atomic.ALLS.PdeB3DenseIdent

/-! # Track B, step B3: a concrete Schwartz cutoff and density of dense forcings in `Lᵖ(ℝ × 𝕋)`

* `bumpC R` : a smooth compactly supported cutoff `ℝ → ℂ` with values in `[0,1]`, equal to `1` on
  `[-R,R]` and `0` outside `(-(R+1), R+1)` (a real `ContDiffBump`, complexified);
* `etaS : 𝓢(ℝ, ℂ)` : the concrete Schwartz cutoff `bumpC 1`, with `etaS t = 1` on `[-1,1]`
  (`etaS_eq_one`);
* `dense_forcing_approx` : for `1 ≤ p < ∞`, the dense forcings `denseSp S G`
  (finitely many modes, Schwartz in time) are dense in `Lᵖ(ℝ × 𝕋, dt ⊗ dx)`.
  Proof: compactly supported continuous approximation (Mathlib), Stone–Weierstrass on
  `[-(R+1), R+1] × 𝕋` for the algebra `Σ fᵢ(t) e_{kᵢ}(x)` with smooth `fᵢ`, multiplication by the
  cutoff `bumpC R` (equal to `1` where the continuous approximant lives).
-/

set_option autoImplicit false
noncomputable section

namespace LiebLiniger.FixedPeriod.ALLS.PdeB

open MeasureTheory Filter Topology NlsGge.Pilot SchwartzMap
open scoped ENNReal ContDiff ComplexConjugate

attribute [local instance] isProbabilityMeasure_spatialMeasure

/-- The real bump with inner radius `R` and outer radius `R + 1`. -/
def bumpR (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℝ) := ⟨R, R + 1, hR, by linarith⟩

/-- The complexified bump. -/
def bumpC (R : ℝ) (hR : 0 < R) (t : ℝ) : ℂ := ((bumpR R hR) t : ℂ)

theorem contDiff_bumpC (R : ℝ) (hR : 0 < R) : ContDiff ℝ ∞ (bumpC R hR) :=
  Complex.ofRealCLM.contDiff.comp (bumpR R hR).contDiff

theorem hasCompactSupport_bumpC (R : ℝ) (hR : 0 < R) : HasCompactSupport (bumpC R hR) :=
  (bumpR R hR).hasCompactSupport.comp_left Complex.ofReal_zero

theorem bumpC_eq_one (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : |t| ≤ R) : bumpC R hR t = 1 := by
  have : (bumpR R hR) t = 1 :=
    (bumpR R hR).one_of_mem_closedBall (by rw [mem_closedBall_zero_iff, Real.norm_eq_abs]; exact ht)
  simp [bumpC, this]

theorem bumpC_eq_zero (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : R + 1 ≤ |t|) : bumpC R hR t = 0 := by
  have : (bumpR R hR) t = 0 :=
    (bumpR R hR).zero_of_le_dist (by rw [dist_zero_right, Real.norm_eq_abs]; exact ht)
  simp [bumpC, this]

theorem norm_bumpC_le_one (R : ℝ) (hR : 0 < R) (t : ℝ) : ‖bumpC R hR t‖ ≤ 1 := by
  rw [bumpC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpR R hR).nonneg]
  exact (bumpR R hR).le_one

/-- **The concrete Schwartz cutoff** `η`, equal to `1` on `[-1,1]`. -/
def etaS : 𝓢(ℝ, ℂ) := (hasCompactSupport_bumpC 1 one_pos).toSchwartzMap (contDiff_bumpC 1 one_pos)

theorem etaS_apply (t : ℝ) : etaS t = bumpC 1 one_pos t := rfl

theorem etaS_eq_one {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : etaS t = 1 := by
  rw [etaS_apply]
  exact bumpC_eq_one 1 one_pos (abs_le.2 ht)

/-- The compact slab used for Stone–Weierstrass. -/
abbrev Slab (R : ℝ) : Type := Set.Icc (-(R + 1)) (R + 1) × PhysicalCircle

/-- The star subalgebra of finite sums `Σᵢ fᵢ(t) e_{kᵢ}(x)` with smooth `fᵢ`, on `Slab R`. -/
def smoothTrigAlg (R : ℝ) : StarSubalgebra ℂ C(Slab R, ℂ) where
  carrier := {P | ∃ (ι : Type) (_ : Fintype ι) (k : ι → ℤ) (f : ι → ℝ → ℂ),
    (∀ i, ContDiff ℝ ∞ (f i)) ∧ ∀ p : Slab R, P p = ∑ i, f i p.1.1 * fourier (k i) p.2}
  mul_mem' := by
    rintro P Q ⟨ι, _, k, f, hf, hP⟩ ⟨ι', _, k', f', hf', hQ⟩
    refine ⟨ι × ι', inferInstance, fun i => k i.1 + k' i.2, fun i t => f i.1 t * f' i.2 t,
      fun i => (hf i.1).mul (hf' i.2), fun p => ?_⟩
    rw [ContinuousMap.mul_apply, hP, hQ, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [fourier_add]
    ring
  one_mem' := ⟨Unit, inferInstance, fun _ => 0, fun _ _ => 1, fun _ => contDiff_const,
    fun p => by simp⟩
  add_mem' := by
    rintro P Q ⟨ι, _, k, f, hf, hP⟩ ⟨ι', _, k', f', hf', hQ⟩
    refine ⟨ι ⊕ ι', inferInstance, Sum.elim k k', Sum.elim f f',
      fun i => by cases i <;> simp [hf, hf'], fun p => ?_⟩
    rw [ContinuousMap.add_apply, hP, hQ, Fintype.sum_sum_type]
    rfl
  zero_mem' := ⟨Empty, inferInstance, fun _ => 0, fun _ _ => 0, fun _ => contDiff_const,
    fun p => by simp⟩
  algebraMap_mem' c := ⟨Unit, inferInstance, fun _ => 0, fun _ _ => c, fun _ => contDiff_const,
    fun p => by simp⟩
  star_mem' := by
    rintro P ⟨ι, _, k, f, hf, hP⟩
    refine ⟨ι, inferInstance, fun i => -k i, fun i t => conj (f i t),
      fun i => Complex.conjCLE.toContinuousLinearMap.contDiff.comp (hf i), fun p => ?_⟩
    rw [ContinuousMap.star_apply, hP, star_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fourier_neg, star_mul']
    simp only [Complex.star_def]

theorem smoothTrigAlg_separatesPoints (R : ℝ) : (smoothTrigAlg R).SeparatesPoints := by
  intro p q hpq
  by_cases h1 : p.1 = q.1
  · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext h1 h)
    let g : C(Slab R, ℂ) := ⟨fun p => fourier 1 p.2, by fun_prop⟩
    refine ⟨g, ⟨g, ⟨Unit, inferInstance, fun _ => 1, fun _ _ => 1, fun _ => contDiff_const,
      fun p => by simp [g]⟩, rfl⟩, ?_⟩
    simp only [g, ContinuousMap.coe_mk, fourier_one]
    intro h
    exact h2 (AddCircle.injective_toCircle one_ne_zero (Subtype.ext h))
  · let g : C(Slab R, ℂ) := ⟨fun p => ((p.1 : ℝ) : ℂ), by fun_prop⟩
    refine ⟨g, ⟨g, ⟨Unit, inferInstance, fun _ => 0, fun _ t => (t : ℂ),
      fun _ => Complex.ofRealCLM.contDiff, fun p => by simp [g]⟩, rfl⟩, ?_⟩
    simp only [g, ContinuousMap.coe_mk]
    intro h
    exact h1 (Subtype.ext (Complex.ofReal_injective h))

/-- Uniform approximation on the slab by elements of `smoothTrigAlg`. -/
theorem exists_smoothTrig_near (R : ℝ) (g : C(Slab R, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (ι : Type) (_ : Fintype ι) (k : ι → ℤ) (f : ι → ℝ → ℂ), (∀ i, ContDiff ℝ ∞ (f i)) ∧
      ∀ p : Slab R, ‖g p - ∑ i, f i p.1.1 * fourier (k i) p.2‖ < ε := by
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (smoothTrigAlg R) (smoothTrigAlg_separatesPoints R)
  have hg : g ∈ (smoothTrigAlg R).topologicalClosure := by rw [htop]; trivial
  rw [← SetLike.mem_coe, StarSubalgebra.topologicalClosure_coe, Metric.mem_closure_iff] at hg
  obtain ⟨b, ⟨ι, _, k, f, hf, hb⟩, hdist⟩ := hg ε hε
  refine ⟨ι, inferInstance, k, f, hf, fun p => ?_⟩
  rw [← hb p, ← dist_eq_norm]
  exact (ContinuousMap.dist_apply_le_dist p).trans_lt hdist

/-- A cut-off smooth function as a Schwartz function. -/
def cutSchwartz (R : ℝ) (hR : 0 < R) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) : 𝓢(ℝ, ℂ) :=
  ((hasCompactSupport_bumpC R hR).mul_right (f' := f)).toSchwartzMap
    ((contDiff_bumpC R hR).mul hf)

theorem cutSchwartz_apply (R : ℝ) (hR : 0 < R) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    cutSchwartz R hR f hf t = bumpC R hR t * f t := rfl

/-- Conversion of a cut-off trigonometric sum into a dense forcing. -/
theorem exists_dense_of_trig (R : ℝ) (hR : 0 < R) {ι : Type} [Fintype ι] (k : ι → ℤ)
    (f : ι → ℝ → ℂ) (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ∃ (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)), (∀ m ∉ S, G m = 0) ∧
      ∀ p : ℝ × PhysicalCircle,
        denseSp S G p = bumpC R hR p.1 * ∑ i, f i p.1 * fourier (k i) p.2 := by
  classical
  have hfm : ∀ m : ℤ, ContDiff ℝ ∞ (fun t => ∑ i ∈ Finset.univ.filter (fun i => k i = m), f i t) :=
    fun m => ContDiff.sum fun i _ => hf i
  refine ⟨Finset.univ.image k, fun m => cutSchwartz R hR _ (hfm m), fun m hm => ?_, fun p => ?_⟩
  · ext t
    have hempty : Finset.univ.filter (fun i => k i = m) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hm (h ▸ Finset.mem_image_of_mem k (Finset.mem_univ i))
    simp [cutSchwartz_apply, hempty]
  · rw [denseSp_apply, Finset.mul_sum]
    calc ∑ m ∈ Finset.univ.image k, cutSchwartz R hR _ (hfm m) p.1 * fourier m p.2
        = ∑ m ∈ Finset.univ.image k, ∑ i ∈ Finset.univ.filter (fun i => k i = m),
            bumpC R hR p.1 * (f i p.1 * fourier (k i) p.2) := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [cutSchwartz_apply, mul_assoc, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [(Finset.mem_filter.1 hi).2]
      _ = ∑ i, bumpC R hR p.1 * (f i p.1 * fourier (k i) p.2) :=
          Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_image_of_mem k (Finset.mem_univ i)) _

/-- **Density of dense forcings in `Lᵖ(ℝ × 𝕋)`**, `1 ≤ p < ∞`. -/
theorem dense_forcing_approx {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    {F : ℝ × PhysicalCircle → ℂ} (hF : MemLp F p ((volume : Measure ℝ).prod spatialMeasure))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (S : Finset ℤ) (G : ℤ → 𝓢(ℝ, ℂ)), (∀ m ∉ S, G m = 0) ∧
      eLpNorm (F - denseSp S G) p ((volume : Measure ℝ).prod spatialMeasure) ≤ ε := by
  set μ : Measure (ℝ × PhysicalCircle) := (volume : Measure ℝ).prod spatialMeasure with hμ
  have : IsLocallyFiniteMeasure spatialMeasure := IsFiniteMeasure.toIsLocallyFiniteMeasure _
  have : IsLocallyFiniteMeasure ((volume : Measure ℝ).prod spatialMeasure) :=
    Measure.prod.instIsLocallyFiniteMeasure
  have : μ.Regular := by
    rw [hμ]; exact Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
  obtain ⟨g, hgc, hgF, hgcont, -⟩ := hF.exists_hasCompactSupport_eLpNorm_sub_le hp hε2
  -- the time support of `g` is bounded
  obtain ⟨R0, hR0⟩ := ((hgc.image continuous_fst).isBounded).subset_closedBall (0 : ℝ)
  set R : ℝ := max R0 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hgz : ∀ q : ℝ × PhysicalCircle, R < |q.1| → g q = 0 := by
    intro q hq
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := hR0 (Set.mem_image_of_mem Prod.fst hmem)
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
    linarith [le_max_left R0 1]
  -- the measure of the slab
  set K : Set (ℝ × PhysicalCircle) := Set.Icc (-(R + 1)) (R + 1) ×ˢ Set.univ with hK
  have hKm : MeasurableSet K := measurableSet_Icc.prod MeasurableSet.univ
  have hμK : μ K ≠ ⊤ := by
    rw [hμ, hK, Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Icc_lt_top.ne (measure_ne_top _ _)
  set c : ℝ≥0∞ := μ K ^ p.toReal⁻¹ with hc
  have hct : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) hμK
  obtain ⟨n, hn0, hn⟩ := ENNReal.exists_nnreal_pos_mul_lt hct hε2
  -- Stone–Weierstrass on the slab
  let gX : C(Slab R, ℂ) := ⟨fun q => g (q.1.1, q.2), by fun_prop⟩
  obtain ⟨ι, _, k, f, hf, happ⟩ := exists_smoothTrig_near R gX (ε := (n : ℝ)) (by exact_mod_cast hn0)
  obtain ⟨S, G, hGS, hG⟩ := exists_dense_of_trig R hR k f hf
  refine ⟨S, G, hGS, ?_⟩
  -- `g = χ g` everywhere
  have hgχ : ∀ q : ℝ × PhysicalCircle, g q = bumpC R hR q.1 * g q := by
    intro q
    by_cases hq : |q.1| ≤ R
    · rw [bumpC_eq_one R hR hq, one_mul]
    · rw [hgz q (lt_of_not_ge hq), mul_zero]
  have hsupp : Function.support (g - denseSp S G) ⊆ K := by
    intro q hq
    refine ⟨?_, Set.mem_univ _⟩
    by_contra hqK
    apply hq
    have hq1 : R + 1 < |q.1| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hqK
      rcases hqK with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp only [Pi.sub_apply, hG q, bumpC_eq_zero R hR hq1.le, zero_mul,
      hgz q (by linarith), sub_zero]
  have hbound : ∀ q ∈ K, ‖(g - denseSp S G) q‖ ≤ (n : ℝ) := by
    intro q hq
    have h1 := happ (⟨q.1, hq.1⟩, q.2)
    rw [Pi.sub_apply, hG q, hgχ q, ← mul_sub, norm_mul]
    calc ‖bumpC R hR q.1‖ * ‖g q - ∑ i, f i q.1 * fourier (k i) q.2‖
        ≤ 1 * (n : ℝ) := by
          refine mul_le_mul (norm_bumpC_le_one R hR _) h1.le (norm_nonneg _) zero_le_one
      _ = n := one_mul _
  have hgG_meas : AEStronglyMeasurable (g - denseSp S G) μ :=
    (hgcont.sub (continuous_denseSp S G)).aestronglyMeasurable
  have hgG : eLpNorm (g - denseSp S G) p μ ≤ ε / 2 := by
    rw [← eLpNorm_restrict_eq_of_support_subset hgG_meas hsupp]
    refine (eLpNorm_le_of_ae_bound hgG_meas.restrict ((ae_restrict_iff' hKm).2 (Eventually.of_forall hbound))).trans ?_
    rw [Measure.restrict_apply_univ, ENNReal.ofReal_coe_nnreal, mul_comm]
    exact hn.le
  calc eLpNorm (F - denseSp S G) p μ = eLpNorm ((F - g) + (g - denseSp S G)) p μ := by
        congr 1; abel
    _ ≤ eLpNorm (F - g) p μ + eLpNorm (g - denseSp S G) p μ :=
        eLpNorm_add_le hp1
    _ ≤ ε / 2 + ε / 2 := add_le_add hgF hgG
    _ = ε := ENNReal.add_halves ε

end LiebLiniger.FixedPeriod.ALLS.PdeB
