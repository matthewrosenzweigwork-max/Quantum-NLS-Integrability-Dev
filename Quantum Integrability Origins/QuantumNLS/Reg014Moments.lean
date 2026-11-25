import QuantumNLS.Reg014Expansion

/-! REG-014 support: the regularized difference `D_{r,u}(Y)` as the divided difference of the
physical and free measures, its exact finite expression through the accepted REG-004
polynomial corrections and the scalar `A - A_0`, and the resulting uniform bound. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace QuantumNLS.Reg014Moments
open QuantumNLS.PhysicalTensor QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevS
open QuantumNLS.ComplexifiedSobolevField QuantumNLS.FreeLimit QuantumNLS.RootH1RatioBounds
open QuantumNLS.TerraMultiRound40ScalarParity QuantumNLS.TerraMultiRound57Collection
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59SignedCharges
open QuantumNLS.TerraMultiRound59SobolevCoordinates QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.TerraMultiRound59PolynomialProperty QuantumNLS.TerraMultiRound59REG007
open QuantumNLS.TerraMultiRound60Kernel QuantumNLS.TerraMultiRound61FiniteDivision
open QuantumNLS.TerraMultiRound61MomentRecurrence QuantumNLS.TerraMultiRound61PhysicalFree
open QuantumNLS.TerraMultiRound62FreeMoments QuantumNLS.TerraMultiRound62EqualMass
open QuantumNLS.TerraMultiRound63Division QuantumNLS.TerraMultiRound64AllMoments
open QuantumNLS.TerraMultiRound64BaseCriterion QuantumNLS.TerraMultiRound64FieldIdentity
open QuantumNLS.TerraMultiRound64FirstIdentity QuantumNLS.TerraMultiRound64FreeSobolev
open QuantumNLS.TerraMultiRound64LowerMoment QuantumNLS.RootWeightedCellsR26
open QuantumNLS.Reg014Expansion

variable {L : ℝ} [Fact (0 < L)]

/-- The regularized difference of the printed statement. -/
def Dfun (κ : ℝ) (hκ : 0 < κ) (r : ℕ) (w : L2T L) (Y : ℝ) : ℝ :=
  (∫ t : ℝ, Y ^ 2 * t ^ (2 * r) / (Y ^ 2 + t ^ 2) ∂(PhysicalQuantumMeasure.measure hκ w)) -
    ∑' n : ℤ, Y ^ 2 * (momentum L n) ^ (2 * r) / (Y ^ 2 + (momentum L n) ^ 2) *
      ‖QuantumNLS.Fourier.coeff L w n‖ ^ 2

/-- Polynomials are bounded on bounded sets. -/
theorem RealPolynomial_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : RealPolynomial f) (U : ℝ) :
    ∃ C : ℝ, ∀ x : E, ‖x‖ ≤ U → |f x| ≤ C := by
  induction hf with
  | zero => exact ⟨0, fun x _ => by simp⟩
  | diagonal n p =>
    refine ⟨‖p‖ * U ^ n, fun x hx => ?_⟩
    rw [← Real.norm_eq_abs]
    calc ‖p (fun _ => x)‖ ≤ ‖p‖ * ∏ _i : Fin n, ‖x‖ := p.le_opNorm _
      _ = ‖p‖ * ‖x‖ ^ n := by simp
      _ ≤ ‖p‖ * U ^ n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx n)
        (norm_nonneg _)
  | add h1 h2 ih1 ih2 =>
    obtain ⟨C1, hC1⟩ := ih1
    obtain ⟨C2, hC2⟩ := ih2
    exact ⟨C1 + C2, fun x hx => (abs_add_le _ _).trans (add_le_add (hC1 x hx) (hC2 x hx))⟩
  | scale c h ih =>
    obtain ⟨C, hC⟩ := ih
    exact ⟨|c| * C, fun x hx => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC x hx) (abs_nonneg c)⟩

/-- Even moments of the physical measure of an `H^n` field are finite. -/
theorem physical_moment_integrable (κ : ℝ) (hκ : 0 < κ) (n : ℕ) (hn : 1 ≤ n) (w : L2T L)
    (hw : hsq L (n : ℝ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤) :
    Integrable (fun t : ℝ => t ^ (2 * n)) (PhysicalQuantumMeasure.measure hκ w) := by
  by_cases h1 : n = 1
  · subst h1
    simpa only [mul_one] using (physical_second_iff_hsq L κ hκ w).mpr hw
  · exact ((integer_moment_induction L κ hκ n (by omega)).1 w).mpr hw

/-- The regularized kernel integrates against the free measure to the Fourier sum. -/
theorem free_kernel_sum {Y : ℝ} (hY : 0 < Y) (w : L2T L) (n : ℕ)
    (hm : Integrable (fun t : ℝ => t ^ (2 * n)) (freeMeasure L w)) :
    ∫ t, kernel (n + 1) Y t ∂(freeMeasure L w) =
      ∑' m : ℤ, Y ^ 2 * (momentum L m) ^ (2 * (n + 1)) / (Y ^ 2 + (momentum L m) ^ 2) *
        ‖QuantumNLS.Fourier.coeff L w m‖ ^ 2 := by
  have : IsFiniteMeasure (freeMeasure L w) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  have hi := kernel_integrable_succ (freeMeasure L w) n Y hY hm
  change Integrable (kernel (n + 1) Y) (Measure.sum (fun m : ℤ =>
    ENNReal.ofReal (‖QuantumNLS.Fourier.coeff L (w : AddCircle L → ℂ) m‖ ^ 2) •
      Measure.dirac (2 * Real.pi * m / L))) at hi
  have hs := hasSum_integral_measure hi
  have he := hs.tsum_eq.symm
  convert he using 1
  · rfl
  apply tsum_congr
  intro m
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  simp only [kernel]
  unfold momentum
  ring

/-- `D_{r,u}(Y)` is the divided difference of the physical and free measures. -/
theorem Dfun_eq_divided (κ : ℝ) (hκ : 0 < κ) (n : ℕ) (hn : 1 ≤ n) (w : L2T L) {Y : ℝ}
    (hY : 0 < Y) (hw : hsq L (n : ℝ) (fun k => QuantumNLS.Fourier.coeff L w k) ≠ ⊤) :
    Dfun κ hκ (n + 1) w Y =
      dividedDifference (PhysicalQuantumMeasure.measure hκ w) (freeMeasure L w) Y (n + 1) := by
  have : IsFiniteMeasure (freeMeasure L w) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  have hμn := physical_moment_integrable κ hκ n hn w hw
  have hνn : Integrable (fun t : ℝ => t ^ (2 * n)) (freeMeasure L w) :=
    (free_even_integrable_iff_hsq w n).mpr hw
  have hμ : ∀ j < n + 1, Integrable (fun t : ℝ => t ^ (2 * j))
      (PhysicalQuantumMeasure.measure hκ w) := fun j hj =>
    even_integrable_of_higher _ j n (by omega) hμn
  have hν : ∀ j < n + 1, Integrable (fun t : ℝ => t ^ (2 * j)) (freeMeasure L w) :=
    fun j hj => even_integrable_of_higher _ j n (by omega) hνn
  rw [finite_division _ _ Y hY (n + 1) hμ hν]
  unfold Dfun
  rw [← free_kernel_sum hY w n hνn]
  rfl

/-- The lower moment corrections are the retained polynomials. -/
theorem moment_diff (κ : ℝ) (hκ : 0 < κ) (r : ℕ) (hr : 2 ≤ r) (u : Hk L (r - 1)) (j : ℕ)
    (hj1 : 1 ≤ j) (hjr : j ≤ r - 1) :
    (∫ t : ℝ, t ^ (2 * j) ∂(PhysicalQuantumMeasure.measure hκ u.val)) -
      (∫ t : ℝ, t ^ (2 * j) ∂(freeMeasure L u.val)) = retainedR (L := L) r hr κ u j := by
  have hu := representative_hsq (L := L) (r - 1) u
  have hsqj : hsq L (j : ℝ) (fun k => QuantumNLS.Fourier.coeff L u.val k) ≠ ⊤ :=
    ne_top_of_le_ne_top hu (hsq_mono (by exact_mod_cast hjr) _)
  have : IsFiniteMeasure (freeMeasure L u.val) := by
    rw [← QuantumNLS.FullMass.Mmeas_zero_coupling]
    infer_instance
  have hfree : Integrable (fun t : ℝ => t ^ (2 * j)) (freeMeasure L u.val) :=
    (free_even_integrable_iff_hsq u.val j).mpr hsqj
  have hf := free_finite_moment u.val j hfree
  by_cases h1 : j = 1
  · subst h1
    have hst : ((1 : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast hjr
    obtain ⟨v, hvdef⟩ : ∃ v : Hk L 1, v = H02.mono (L := L) hst u := ⟨_, rfl⟩
    have hv : v.val = u.val := by
      rw [hvdef]
      dsimp only [H02.mono]
      exact fieldIncl_val _ _ _ _ _
    have h := first_field_identity (L := L) κ hκ v
    rw [hv] at h
    have hret : retainedR (L := L) r hr κ u 1 = R1field (L := L) κ v := by
      rw [hvdef]
      unfold retainedR
      simp only [↓reduceIte]
    rw [hret]
    have e2 : (fun t : ℝ => t ^ (2 * 1)) = (fun t : ℝ => t ^ 2) := by funext t; norm_num
    rw [e2] at hf ⊢
    rw [h, hf]
    simp only [mul_one]
    ring
  · have hj2 : 2 ≤ j := by omega
    have hst : ((j - 1 : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show j - 1 ≤ r - 1 by omega)
    obtain ⟨v, hvdef⟩ : ∃ v : Hk L (j - 1), v = H02.mono (L := L) hst u := ⟨_, rfl⟩
    have hv : v.val = u.val := by
      rw [hvdef]
      dsimp only [H02.mono]
      exact fieldIncl_val _ _ _ _ _
    have h := finite_field_identity (L := L) κ hκ j hj2 v (by rw [hv]; exact hsqj)
    rw [hv] at h
    have hret : retainedR (L := L) r hr κ u j = Rfield (L := L) j hj2 κ v := by
      rw [hvdef]
      unfold retainedR
      simp only [h1, ↓reduceIte, hj2, show j ≤ r by omega, and_self, ↓reduceDIte]
    rw [hret, h, hf]
    ring

/-- Exact algebra of the divided-difference recursion. -/
theorem D_algebra (r : ℕ) (hr : 2 ≤ r) (Y : ℝ) (hY : 0 < Y) (c d ρ : ℕ → ℝ)
    (hd : ∀ n, d (n + 1) = Y ^ 2 * (c n - d n)) (hc0 : c 0 = 0)
    (hcj : ∀ j, 1 ≤ j → j < r → c j = ρ j) (S : ℝ) (hd0 : d 0 = Y * S) :
    d r = ρ r + (-(Y ^ 2)) ^ r *
      (Y * (S - ∑ j ∈ Finset.Icc 1 r, (-1 : ℝ) ^ j * ρ j * Y⁻¹ ^ (2 * j + 1))) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hq : Y ^ 2 ≠ 0 := by positivity
  refine correction_from_expansion (Y ^ 2) hq c d hd s (ρ (s + 1)) _ ?_
  have hY0 : Y ≠ 0 := hY.ne'
  have hg : ∀ j : ℕ, Y * ((-1 : ℝ) ^ j * ρ j * Y⁻¹ ^ (2 * j + 1)) = (-(Y ^ 2))⁻¹ ^ j * ρ j := by
    intro j
    have h1 : (-(Y ^ 2))⁻¹ = -(Y⁻¹ ^ 2) := by rw [inv_neg, inv_pow]
    have h2 : (-(Y ^ 2))⁻¹ ^ j = (-1 : ℝ) ^ j * Y⁻¹ ^ (2 * j) := by
      rw [h1, neg_pow (Y⁻¹ ^ 2) j, ← pow_mul]
    have h3 : Y * Y⁻¹ ^ (2 * j + 1) = Y⁻¹ ^ (2 * j) := by
      rw [pow_succ, mul_comm (Y⁻¹ ^ (2 * j)) Y⁻¹, ← mul_assoc, mul_inv_cancel₀ hY0, one_mul]
    rw [h2]
    calc Y * ((-1 : ℝ) ^ j * ρ j * Y⁻¹ ^ (2 * j + 1))
        = (-1 : ℝ) ^ j * ρ j * (Y * Y⁻¹ ^ (2 * j + 1)) := by ring
      _ = _ := by rw [h3]; ring
  have hsumc : ∑ j ∈ Finset.range (s + 1), (-(Y ^ 2))⁻¹ ^ j * c j =
      ∑ j ∈ Finset.Icc 1 s, (-(Y ^ 2))⁻¹ ^ j * ρ j := by
    have hr' : Finset.range (s + 1) = insert 0 (Finset.Icc 1 s) := by
      ext j
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hr', Finset.sum_insert (by simp), hc0]
    simp only [mul_zero, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    rw [hcj j hj'.1 (by omega)]
  have hsumρ : Y * ∑ j ∈ Finset.Icc 1 (s + 1), (-1 : ℝ) ^ j * ρ j * Y⁻¹ ^ (2 * j + 1) =
      ∑ j ∈ Finset.Icc 1 (s + 1), (-(Y ^ 2))⁻¹ ^ j * ρ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => hg j)
  have hsplit := Finset.sum_Icc_succ_top (show 1 ≤ s + 1 by omega)
    (fun j => (-(Y ^ 2))⁻¹ ^ j * ρ j)
  rw [hd0, hsumc, mul_sub, hsumρ, hsplit]
  ring

/-- The exact formula for `D` in terms of the scalar `A - A_0`. -/
theorem D_of_scalar (κ : ℝ) (hκ : 0 < κ) (r : ℕ) (hr : 2 ≤ r) (u : Hk L (r - 1)) (x : Ell2)
    (hxu : physicalToHk (L := L) (r - 1) x = u) {Y : ℝ} (hY : 0 < Y)
    (hlog : Real.log 3 ≤ Y * L)
    (hsmall : 16 * κ * ‖fieldMap L (r - 1 : ℕ) (Nat.cast_nonneg _) x‖ ^ 2 ≤ Y) (rr : Ell2)
    (hrr : fieldMap L (r - 1 : ℕ) (Nat.cast_nonneg _) rr =
      ratioL2 hY hlog hκ.le (fieldMap L (r - 1 : ℕ) (Nat.cast_nonneg _) x) hsmall) :
    Dfun κ hκ r u.val Y = retainedR (L := L) r hr κ u r + (-(Y ^ 2)) ^ r *
      (Y * ((scalar L (r - 1 : ℕ) x rr - freeScalar (L := L) (r - 1 : ℕ) x Y).re -
        ∑ j ∈ Finset.Icc 1 r, (-1 : ℝ) ^ j * retainedR (L := L) r hr κ u j * Y⁻¹ ^ (2 * j + 1))) := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hx : fieldMap L (n + 1 - 1 : ℕ) (Nat.cast_nonneg _) x = u.val := by
    have h := physicalToHk_val_eq_fieldMap L (n + 1 - 1) (Nat.cast_nonneg _) x
    rw [hxu] at h
    exact h.symm
  have hu := representative_hsq (L := L) (n + 1 - 1) u
  simp only [Nat.add_sub_cancel] at hu
  have ha : (1 : ℝ) / 2 < ((n + 1 - 1 : ℕ) : ℝ) := by
    have h : (1 : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hn
    simp only [Nat.add_sub_cancel]
    linarith
  have hdiff := regularized_scalar_difference (L := L) ha hY hlog hκ
    (fieldMap L (n + 1 - 1 : ℕ) (Nat.cast_nonneg _) x) hsmall x rr rfl hrr
  rw [hx] at hdiff
  have hD := Dfun_eq_divided (L := L) κ hκ n hn u.val hY (by simpa using hu)
  rw [hD]
  refine D_algebra (n + 1) hr Y hY
    (fun m => ∫ t : ℝ, t ^ (2 * m) ∂(PhysicalQuantumMeasure.measure hκ u.val) -
      ∫ t : ℝ, t ^ (2 * m) ∂(freeMeasure L u.val))
    (dividedDifference (PhysicalQuantumMeasure.measure hκ u.val) (freeMeasure L u.val) Y)
    (fun j => retainedR (L := L) (n + 1) hr κ u j) ?_ ?_ ?_ _ ?_
  · intro m
    simp only [dividedDifference]
    ring
  · exact physical_free_mass hκ u.val
  · intro j hj1 hjr
    exact moment_diff κ hκ (n + 1) hr u j hj1 (by omega)
  · rw [dividedDifference]
    exact hdiff

/-- **Uniform bound for `D_{r,u}(Y)`.** -/
theorem D_uniform (κ : ℝ) (hκ : 0 < κ) (r : ℕ) (hr : 2 ≤ r) (U : ℝ) (hU : 0 ≤ U) :
    ∃ C Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ u : Hk L (r - 1), ‖u‖ ≤ U → ∀ Y : ℝ, Y₀ ≤ Y →
      |Dfun κ hκ r u.val Y| ≤ C := by
  obtain ⟨C₁, Y₁, hY₁, h₁⟩ := uniform_scalar_remainder (L := L) r hr κ hκ U hU
  obtain ⟨C₂, h₂⟩ := RealPolynomial_bounded (Rfield_polynomial (L := L) r hr κ) U
  refine ⟨C₂ + C₁, Y₁, hY₁, fun u hu Y hY => ?_⟩
  have hY1 : 1 ≤ Y := hY₁.trans hY
  set x : Ell2 := coordinates (L := L) (r - 1) u with hx_def
  have hxn : ‖x‖ ≤ U := by
    rw [hx_def, LinearIsometryEquiv.norm_map]
    exact hu
  have hxu : physicalToHk (L := L) (r - 1) x = u := physical_coordinates (r - 1) u
  obtain ⟨hY0, hlog, hsmall, rr, hident, hbound⟩ := h₁ x hxn Y hY
  have hform := D_of_scalar (L := L) κ hκ r hr u x hxu hY0 hlog hsmall rr hident
  rw [hxu] at hbound
  rw [hform]
  have hρ : |retainedR (L := L) r hr κ u r| ≤ C₂ := by
    have hst : ((r - 1 : ℕ) : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := le_rfl
    have hr1 : r ≠ 1 := by omega
    have hret : retainedR (L := L) r hr κ u r = Rfield (L := L) r hr κ (H02.mono (L := L) hst u) := by
      unfold retainedR
      simp only [hr1, ↓reduceIte, hr, le_refl, and_self, ↓reduceDIte]
    rw [hret]
    exact h₂ _ ((H02.norm_mono_le hst u).trans hu)
  have hYpos : 0 < Y := hY0
  have hpow : |(-(Y ^ 2)) ^ r * (Y * ((scalar L (r - 1 : ℕ) x rr -
      freeScalar (L := L) (r - 1 : ℕ) x Y).re - ∑ j ∈ Finset.Icc 1 r, (-1 : ℝ) ^ j *
        retainedR (L := L) r hr κ u j * Y⁻¹ ^ (2 * j + 1)))| ≤ C₁ := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_pos (pow_pos hYpos 2), abs_of_pos hYpos]
    have hb := mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ (Y ^ 2) ^ r * Y)
    have e : (Y ^ 2) ^ r * Y * (C₁ * Y⁻¹ ^ (2 * r + 1)) = C₁ := by
      have hY0' : Y ≠ 0 := hYpos.ne'
      have hpow : (Y ^ 2) ^ r * Y = Y ^ (2 * r + 1) := by rw [← pow_mul, pow_succ]
      rw [hpow, inv_pow]
      field_simp
    calc (Y ^ 2) ^ r * (Y * |(scalar L (r - 1 : ℕ) x rr - freeScalar (L := L) (r - 1 : ℕ) x Y).re -
          ∑ j ∈ Finset.Icc 1 r, (-1 : ℝ) ^ j * retainedR (L := L) r hr κ u j *
            Y⁻¹ ^ (2 * j + 1)|)
        = (Y ^ 2) ^ r * Y * |(scalar L (r - 1 : ℕ) x rr - freeScalar (L := L) (r - 1 : ℕ) x Y).re -
          ∑ j ∈ Finset.Icc 1 r, (-1 : ℝ) ^ j * retainedR (L := L) r hr κ u j *
            Y⁻¹ ^ (2 * j + 1)| := by ring
      _ ≤ _ := hb
      _ = C₁ := e
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ C₂ + C₁ := add_le_add hρ hpow

#print axioms RealPolynomial_bounded
#print axioms free_kernel_sum
#print axioms Dfun_eq_divided
#print axioms moment_diff
#print axioms D_algebra
#print axioms D_of_scalar
#print axioms D_uniform
end QuantumNLS.Reg014Moments
