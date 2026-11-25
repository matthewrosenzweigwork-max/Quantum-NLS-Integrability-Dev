import NlsGge.Atomic.KST.KST001
import NlsGge.Atomic.DM.DM048
import NlsGge.Sobolev.PeriodicBridge

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace NlsGge.Atomic.KST002

open NlsGge.Atomic.KST001
open NlsGge.Atomic.DM048
open NlsGge.Pilot

/-- The weighted Fourier-pair carrier has its genuine Hilbert norm: the outer
Bool `PiLp` uses the Euclidean two-component norm. -/
abbrev WeightedPairHilbert (W : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < W m ^ 2)] :=
  NlsGge.Atomic.DM048.WeightedPairHilbert W

/-- The Euclidean two-component ℓ² target, with no max-norm complex product. -/
abbrev PairLp := PiLp 2 (fun _ : Bool => lp (fun _ : ℤ => ℂ) 2)

/-- The same Euclidean pair space indexed first by the integer mode. -/
abbrev PairSequenceLp := lp (fun _ : ℤ => PiLp 2 (fun _ : Bool => ℂ)) 2

private def pairTranspose (x : PairLp) : ℤ → PiLp 2 (fun _ : Bool => ℂ) :=
  fun m => WithLp.toLp 2 (fun b => x b m)

set_option maxHeartbeats 600000 in
private theorem pairTranspose_mem (x : PairLp) : Memℓp (pairTranspose x) 2 := by
  have ht := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (x true)).summable
  have hf := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (x false)).summable
  have heq : (fun m : ℤ => ‖pairTranspose x m‖ ^ 2) =
      fun m => ‖x true m‖ ^ 2 + ‖x false m‖ ^ 2 := by
    funext m
    change ‖WithLp.toLp 2 (fun b => x b m)‖ ^ 2 = _
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Bool => ℂ) (WithLp.toLp 2 (fun b => x b m))]
    simp [Fintype.sum_bool]
  have hs : Summable (fun m : ℤ => ‖pairTranspose x m‖ ^ 2) := by
    rw [heq]
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using ht.add hf
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

private theorem pairUntranspose_component_mem (y : PairSequenceLp) (b : Bool) :
    Memℓp (fun m : ℤ => y m b) 2 := by
  have hy := (lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) y).summable
  have hs : Summable (fun m : ℤ => ‖y m b‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun m => sq_nonneg ‖y m b‖) (fun m => ?_)
      (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hy)
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (PiLp.norm_apply_le (y m) b)
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs

private def pairUntranspose (y : PairSequenceLp) : PairLp :=
  WithLp.toLp 2 (fun b => ⟨fun m => y m b, pairUntranspose_component_mem y b⟩)

private def pairLpInterchangeEquiv : PairLp ≃ₗ[ℂ] PairSequenceLp where
  toFun x := ⟨pairTranspose x, pairTranspose_mem x⟩
  invFun := pairUntranspose
  left_inv x := by
    apply PiLp.ext
    intro b
    apply lp.ext
    funext m
    rfl
  right_inv y := by
    apply lp.ext
    funext m
    apply PiLp.ext
    intro b
    rfl
  map_add' x y := by
    apply lp.ext
    funext m
    apply PiLp.ext
    intro b
    change x b m + y b m = x b m + y b m
    rfl
  map_smul' c x := by
    apply lp.ext
    funext m
    apply PiLp.ext
    intro b
    change c • x b m = c • x b m
    rfl

private theorem pairLpInterchange_norm_sq (x : PairLp) :
    ‖pairLpInterchangeEquiv x‖ ^ 2 = ‖x‖ ^ 2 := by
  have ht := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (x true)
  have hf := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (x false)
  have hsum₀ := (ht.summable.tsum_add hf.summable).trans (by rw [ht.tsum_eq, hf.tsum_eq])
  have hsum : (∑' m : ℤ, (‖x true m‖ ^ 2 + ‖x false m‖ ^ 2)) =
      ‖x true‖ ^ 2 + ‖x false‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsum₀
  have hpair := lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) (pairLpInterchangeEquiv x)
  calc
    ‖pairLpInterchangeEquiv x‖ ^ 2 =
        ∑' m : ℤ, ‖pairLpInterchangeEquiv x m‖ ^ 2 := by
          simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hpair.tsum_eq.symm
    _ = ∑' m : ℤ, (‖x true m‖ ^ 2 + ‖x false m‖ ^ 2) := by
      apply tsum_congr
      intro m
      have hm : ‖pairLpInterchangeEquiv x m‖ ^ 2 =
          ‖x true m‖ ^ 2 + ‖x false m‖ ^ 2 := by
        change ‖pairTranspose x m‖ ^ 2 = _
        simp [pairTranspose, PiLp.norm_sq_eq_of_L2]
      exact hm
    _ = ‖x true‖ ^ 2 + ‖x false‖ ^ 2 := hsum
    _ = ‖x‖ ^ 2 := by
      simpa only [Fintype.sum_bool] using
        (PiLp.norm_sq_eq_of_L2 (fun _ : Bool => lp (fun _ : ℤ => ℂ) 2) x).symm

/-- Canonical Hilbert-sum coordinate interchange: this is the explicit
isometry from two scalar integer `ℓ²` channels to integer modes with
Euclidean two-component fibers. -/
def pairLpCoordinateInterchange : PairLp ≃ₗᵢ[ℂ] PairSequenceLp where
  toLinearEquiv := pairLpInterchangeEquiv
  norm_map' x := by
    have h := pairLpInterchange_norm_sq x
    nlinarith [norm_nonneg (pairLpInterchangeEquiv x), norm_nonneg x]

theorem pairLpCoordinateInterchange_apply (x : PairLp) (m : ℤ) (b : Bool) :
    pairLpCoordinateInterchange x m b = x b m := rfl

/-- Multiplication by the positive weight is a complex linear isometry from
the weighted coefficient-pair Hilbert space to the Euclidean pair of scalar
`ℓ²` spaces. -/
def weightedPairIsoLp (W : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (_hW : ∀ m : ℤ, 0 < W m) : WeightedPairHilbert W ≃ₗᵢ[ℂ] PairLp :=
  LinearIsometryEquiv.piLpCongrRight 2
    (fun _ : Bool => weightedIsometry (fun m => W m ^ 2))

theorem weightedPairIsoLp_apply (W : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (hW : ∀ m : ℤ, 0 < W m) (x : WeightedPairHilbert W) (b : Bool) (m : ℤ) :
    weightedPairIsoLp W hW x b m = (W m : ℂ) * (x b : ℤ → ℂ) m := by
  change weightedIsometry (fun m => W m ^ 2) (x b) m = _
  rw [weightedIsometry_apply]
  simp only [weightedCoordinates]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (hW m)]

theorem weightedPairIsoLp_symm_apply (W : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (hW : ∀ m : ℤ, 0 < W m) (y : PairLp) (b : Bool) (m : ℤ) :
    ((weightedPairIsoLp W hW).symm y b : ℤ → ℂ) m = y b m / (W m : ℂ) := by
  change ((weightedIsometry (fun m => W m ^ 2)).symm (y b) : ℤ → ℂ) m = _
  rw [weightedIsometry_symm_apply]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (hW m)]

/-- The norm square is the literal sum of the two coefficient energies. -/
theorem weightedPairIsoLp_norm_sq (W : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (hW : ∀ m : ℤ, 0 < W m) (x : WeightedPairHilbert W) :
    ‖weightedPairIsoLp W hW x‖ ^ 2 = ∑' m : ℤ, W m ^ 2 *
      (‖(x true : ℤ → ℂ) m‖ ^ 2 + ‖(x false : ℤ → ℂ) m‖ ^ 2) := by
  rw [(weightedPairIsoLp W hW).norm_map]
  exact weightedPairHilbert_norm_sq W x

/-- The weighted pair is isometric to `ℓ²(ℤ; PiLp₂(ℂ,ℂ))`, with the
coordinate interchange proved rather than identified by notation. -/
def weightedPairIsoEuclideanLp (W : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)] (hW : ∀ m : ℤ, 0 < W m) :
    WeightedPairHilbert W ≃ₗᵢ[ℂ] PairSequenceLp :=
  (weightedPairIsoLp W hW).trans pairLpCoordinateInterchange

/-- A period-one Fourier coefficient carrier uses the doubled source label
`ω (2*m)`, retaining the source's zero odd doubled-period modes. -/
def periodOneWeight (ω : ℤ → ℝ) (m : ℤ) : ℝ := ω (2 * m)

private theorem periodOneWeight_pos (ω : ℤ → ℝ) (hω : EvenWeight ω) (m : ℤ) :
    0 < periodOneWeight ω m := by
  change 0 < ω (2 * m)
  exact lt_of_lt_of_le zero_lt_one (hω.one_le (2 * m))

/-- The two actual period-one physical fields are packaged with the Euclidean
two-component norm. -/
abbrev PhysicalPairLp := PiLp 2 (fun _ : Bool => NlsGge.Pilot.PhysicalL2)

/-- Forgetting a weight bounded below by one gives a genuine unweighted
Fourier coefficient in `ℓ²`; the comparison is performed in the weighted
Hilbert carriers, so membership is established before reconstruction. -/
def unweightedFourierComponent (W : ℤ → ℝ) (hW : ∀ m, 1 ≤ W m)
    (x : WeightedHilbert (fun m => W m ^ 2)) : lp (fun _ : ℤ => ℂ) 2 := by
  letI : Fact (∀ m : ℤ, 0 < W m ^ 2) := ⟨fun m => sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (hW m))⟩
  letI : Fact (∀ m : ℤ, 0 < (1 : ℝ)) := ⟨fun _ => by norm_num⟩
  exact weightedIsometry (fun _ : ℤ => (1 : ℝ))
    (weightedComparison (fun m => W m ^ 2) (fun _ : ℤ => (1 : ℝ)) 1 (by norm_num)
      (fun m => by nlinarith [hW m]) x)

theorem unweightedFourierComponent_apply (W : ℤ → ℝ) (hW : ∀ m, 1 ≤ W m)
    (x : WeightedHilbert (fun m => W m ^ 2)) (m : ℤ) :
    unweightedFourierComponent W hW x m = x m := by
  letI : Fact (∀ m : ℤ, 0 < W m ^ 2) := ⟨fun m => sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (hW m))⟩
  letI : Fact (∀ m : ℤ, 0 < (1 : ℝ)) := ⟨fun _ => by norm_num⟩
  change weightedCoordinates (fun _ : ℤ => (1 : ℝ))
      (weightedComparison (fun n => W n ^ 2) (fun _ : ℤ => (1 : ℝ)) 1 (by norm_num)
        (fun n => by nlinarith [hW n]) x) m = (x : ℤ → ℂ) m
  simp [weightedCoordinates, weightedComparison_apply]

/-- Reconstruct the actual physical period-one pair from an element of the
weighted Fourier carrier, one channel at a time. -/
def weightedPairPhysical (W : ℤ → ℝ) (hW : ∀ m, 1 ≤ W m)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (x : WeightedPairHilbert W) : PhysicalPairLp :=
  WithLp.toLp 2 (fun b =>
    NlsGge.Pilot.physicalFourierL2.symm
      (unweightedFourierComponent W hW (x b)))

/-- The reconstruction has exactly the original coefficient at every integer
label, including zero and negative labels. -/
theorem weightedPairPhysical_fourier (W : ℤ → ℝ) (hW : ∀ m, 1 ≤ W m)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (x : WeightedPairHilbert W) (b : Bool) (m : ℤ) :
    NlsGge.Pilot.physicalFourier (weightedPairPhysical W hW x b) m = x b m := by
  rw [← NlsGge.Pilot.physicalFourierL2_apply]
  change NlsGge.Pilot.physicalFourierL2
      (NlsGge.Pilot.physicalFourierL2.symm
        (unweightedFourierComponent W hW (x b))) m = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact unweightedFourierComponent_apply W hW (x b) m

/-- The actual physical period-one pair reconstructed from the weighted
coefficient pair. Its doubled-cover source index is exactly `2*m`. -/
def periodOnePhysicalPair (ω : ℤ → ℝ) (hω : EvenWeight ω)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : WeightedPairHilbert (periodOneWeight ω)) : PeriodicPair :=
  let hW : ∀ m : ℤ, 1 ≤ periodOneWeight ω m := fun m => hω.one_le (2 * m)
  (weightedPairPhysical (periodOneWeight ω) hW x true,
    weightedPairPhysical (periodOneWeight ω) hW x false)

theorem periodOnePhysicalPair_fourier (ω : ℤ → ℝ) (hω : EvenWeight ω)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : WeightedPairHilbert (periodOneWeight ω)) (m : ℤ) :
    physicalFourier (periodOnePhysicalPair ω hω x).1 m = x true m ∧
      physicalFourier (periodOnePhysicalPair ω hω x).2 m = x false m := by
  have hW : ∀ j : ℤ, 1 ≤ periodOneWeight ω j := fun j => hω.one_le (2 * j)
  constructor
  · simpa [periodOnePhysicalPair] using
      (weightedPairPhysical_fourier (periodOneWeight ω) hW x true m)
  · simpa [periodOnePhysicalPair] using
      (weightedPairPhysical_fourier (periodOneWeight ω) hW x false m)

theorem periodOnePhysicalPair_mode_energy (ω : ℤ → ℝ) (hω : EvenWeight ω)
    [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : WeightedPairHilbert (periodOneWeight ω)) :
    ‖x‖ ^ 2 = ∑' m : ℤ, (ω (2 * m)) ^ 2 *
      (‖physicalFourier (periodOnePhysicalPair ω hω x).1 m‖ ^ 2 +
        ‖physicalFourier (periodOnePhysicalPair ω hω x).2 m‖ ^ 2) := by
  rw [weightedPairHilbert_norm_sq]
  apply tsum_congr
  intro m
  have hcoeff := periodOnePhysicalPair_fourier ω hω x m
  simp only [periodOneWeight] at hcoeff ⊢
  rw [hcoeff.1, hcoeff.2]

theorem periodOnePhysicalPair_full_doubled_energy (ω : ℤ → ℝ)
    (hω : EvenWeight ω) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : WeightedPairHilbert (periodOneWeight ω)) :
    weightedNormSq₂ ω (periodOnePhysicalPair ω hω x) =
      ∑' m : ℤ, ENNReal.ofReal ((ω (2 * m)) ^ 2) *
        (ENNReal.ofReal (‖physicalFourier (periodOnePhysicalPair ω hω x).1 m‖ ^ 2) +
          ENNReal.ofReal (‖physicalFourier (periodOnePhysicalPair ω hω x).2 m‖ ^ 2)) := by
  rw [periodOne_weightedPair_norm ω (periodOnePhysicalPair ω hω x) hω]
  unfold weightedEvenFourierNormSq weightedPairMode
  apply tsum_congr
  intro m
  have hcoeff := periodOnePhysicalPair_fourier ω hω x m
  rw [hcoeff.1, hcoeff.2]

/-- The full doubled-cover energy of a reconstructed period-one pair is finite
and is exactly the squared norm in the genuine weighted coefficient carrier. -/
theorem periodOnePhysicalPair_full_doubled_energy_eq_norm (ω : ℤ → ℝ)
    (hω : EvenWeight ω) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : WeightedPairHilbert (periodOneWeight ω)) :
    weightedNormSq₂ ω (periodOnePhysicalPair ω hω x) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [periodOnePhysicalPair_full_doubled_energy]
  let f : ℤ → ℝ := fun m => (ω (2 * m)) ^ 2 *
    (‖(x true : ℤ → ℂ) m‖ ^ 2 + ‖(x false : ℤ → ℂ) m‖ ^ 2)
  have hsum : Summable f := by
    have hs₁ := (weightedHilbert_hasSum (fun m => periodOneWeight ω m ^ 2)
      (show WeightedHilbert (fun m => periodOneWeight ω m ^ 2) from x true)).summable
    have hs₂ := (weightedHilbert_hasSum (fun m => periodOneWeight ω m ^ 2)
      (show WeightedHilbert (fun m => periodOneWeight ω m ^ 2) from x false)).summable
    simpa [f, periodOneWeight, mul_add] using hs₁.add hs₂
  have hnonneg : ∀ m, 0 ≤ f m := by
    intro m
    dsimp [f]
    positivity
  have hterm (m : ℤ) :
      ENNReal.ofReal ((ω (2 * m)) ^ 2) *
        (ENNReal.ofReal (‖physicalFourier (periodOnePhysicalPair ω hω x).1 m‖ ^ 2) +
          ENNReal.ofReal (‖physicalFourier (periodOnePhysicalPair ω hω x).2 m‖ ^ 2)) =
      ENNReal.ofReal (f m) := by
    have hcoeff := periodOnePhysicalPair_fourier ω hω x m
    rw [hcoeff.1, hcoeff.2]
    dsimp [f]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add] <;> positivity
  calc
    _ = ∑' m : ℤ, ENNReal.ofReal (f m) := by
      apply tsum_congr
      intro m
      exact hterm m
    _ = ENNReal.ofReal (∑' m : ℤ, f m) :=
      (ENNReal.ofReal_tsum_of_nonneg hnonneg hsum).symm
    _ = ENNReal.ofReal (‖x‖ ^ 2) := by
      congr 1
      exact (weightedPairHilbert_norm_sq (periodOneWeight ω) x).symm

theorem periodOnePhysicalPair_full_doubled_energy_finite (ω : ℤ → ℝ)
    (hω : EvenWeight ω) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : WeightedPairHilbert (periodOneWeight ω)) :
    weightedNormSq₂ ω (periodOnePhysicalPair ω hω x) < ⊤ := by
  rw [periodOnePhysicalPair_full_doubled_energy_eq_norm]
  exact ENNReal.ofReal_lt_top

/-- Finite source doubled energy gives genuine real weighted square
summability of both period-one Fourier coefficient sequences. -/
theorem periodOne_coefficients_summable_of_finite_energy (ω : ℤ → ℝ)
    (hω : EvenWeight ω) (φ : PeriodicPair)
    (hfinite : weightedNormSq₂ ω φ < ⊤) :
    Summable (fun m : ℤ => (ω (2 * m)) ^ 2 *
      (‖physicalFourier φ.1 m‖ ^ 2 + ‖physicalFourier φ.2 m‖ ^ 2)) := by
  let f : ℤ → ℝ := fun m => (ω (2 * m)) ^ 2 *
    (‖physicalFourier φ.1 m‖ ^ 2 + ‖physicalFourier φ.2 m‖ ^ 2)
  have hf_nonneg : ∀ m, 0 ≤ f m := by
    intro m
    dsimp [f]
    positivity
  have hterm (m : ℤ) :
      weightedPairMode ω (2 * m) (periodTwoPairCoeff φ (2 * m)) =
        ENNReal.ofReal (f m) := by
    rw [periodOne_pair_even_coeff]
    dsimp [weightedPairMode, f]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add] <;> positivity
  have hfiniteEven : weightedEvenFourierNormSq ω φ < ⊤ := by
    rw [← periodOne_weightedPair_norm ω φ hω]
    exact hfinite
  have hevenEq : weightedEvenFourierNormSq ω φ =
      ∑' m : ℤ, ENNReal.ofReal (f m) := by
    unfold weightedEvenFourierNormSq
    apply tsum_congr
    intro m
    simpa [periodOne_pair_even_coeff] using hterm m
  have hsumLt : (∑' m : ℤ, ENNReal.ofReal (f m)) < ⊤ := by
    rw [← hevenEq]
    exact hfiniteEven
  have htoReal := ENNReal.summable_toReal (ne_of_lt hsumLt)
  simpa [f, ENNReal.toReal_ofReal, hf_nonneg] using htoReal

/-- Every finite-energy physical period-one pair is represented by an element
of the actual doubled-label weighted Hilbert pair, and reconstructed without
changing either physical field. -/
theorem periodOnePhysicalPair_exists_of_finite_energy (ω : ℤ → ℝ)
    (hω : EvenWeight ω) (φ : PeriodicPair) (hfinite : weightedNormSq₂ ω φ < ⊤) :
    letI : Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2) :=
      ⟨fun m => sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (hω.one_le (2 * m)))⟩
    ∃ x : WeightedPairHilbert (periodOneWeight ω),
      periodOnePhysicalPair ω hω x = φ := by
  let W := periodOneWeight ω
  have hW : ∀ m : ℤ, 0 < W m := fun m =>
    lt_of_lt_of_le zero_lt_one (hω.one_le (2 * m))
  letI : Fact (∀ m : ℤ, 0 < W m ^ 2) := ⟨fun m => sq_pos_of_pos (hW m)⟩
  letI : Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2) :=
    ⟨fun m => sq_pos_of_pos (lt_of_lt_of_le zero_lt_one (hω.one_le (2 * m)))⟩
  have hsum := periodOne_coefficients_summable_of_finite_energy ω hω φ hfinite
  have hs₁ : Summable (fun m : ℤ => W m ^ 2 * ‖physicalFourier φ.1 m‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hsum
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg (W m))
    exact le_add_of_nonneg_right (sq_nonneg ‖physicalFourier φ.2 m‖)
  have hs₂ : Summable (fun m : ℤ => W m ^ 2 * ‖physicalFourier φ.2 m‖ ^ 2) := by
    apply Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hsum
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg (W m))
    exact le_add_of_nonneg_left (sq_nonneg ‖physicalFourier φ.1 m‖)
  let x₁ : WeightedHilbert (fun m => W m ^ 2) :=
    ⟨physicalFourier φ.1,
      (weightedCoordinates_mem_l2_iff (fun m => W m ^ 2)
        (fun m => sq_nonneg (W m)) (physicalFourier φ.1)).2 hs₁⟩
  let x₂ : WeightedHilbert (fun m => W m ^ 2) :=
    ⟨physicalFourier φ.2,
      (weightedCoordinates_mem_l2_iff (fun m => W m ^ 2)
        (fun m => sq_nonneg (W m)) (physicalFourier φ.2)).2 hs₂⟩
  let x : WeightedPairHilbert W := WithLp.toLp 2 (fun b => if b = true then x₁ else x₂)
  have hrealize : periodOnePhysicalPair ω hω x = φ := by
    apply Prod.ext
    · apply (NlsGge.Pilot.physicalFourierL2).injective
      apply lp.ext
      funext m
      change NlsGge.Pilot.physicalFourierL2 (periodOnePhysicalPair ω hω x).1 m =
        NlsGge.Pilot.physicalFourierL2 φ.1 m
      rw [NlsGge.Pilot.physicalFourierL2_apply,
        NlsGge.Pilot.physicalFourierL2_apply]
      rw [(periodOnePhysicalPair_fourier ω hω x m).1]
      simp [x, x₁]
    · apply (NlsGge.Pilot.physicalFourierL2).injective
      apply lp.ext
      funext m
      change NlsGge.Pilot.physicalFourierL2 (periodOnePhysicalPair ω hω x).2 m =
        NlsGge.Pilot.physicalFourierL2 φ.2 m
      rw [NlsGge.Pilot.physicalFourierL2_apply,
        NlsGge.Pilot.physicalFourierL2_apply]
      rw [(periodOnePhysicalPair_fourier ω hω x m).2]
      simp [x, x₂]
  exact ⟨x, hrealize⟩

theorem periodOnePhysicalPair_odd_doubled_mode_zero (ω : ℤ → ℝ)
    (hω : EvenWeight ω) [Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2)]
    (x : WeightedPairHilbert (periodOneWeight ω)) (m : ℤ) :
    weightedPairMode ω (2 * m + 1)
      (periodTwoPairCoeff (periodOnePhysicalPair ω hω x) (2 * m + 1)) = 0 :=
  periodOne_pair_odd_weightedMode_zero ω (periodOnePhysicalPair ω hω x) m

/-- Every raw coefficient evaluation is continuous, transported from the
genuine scalar `ℓ²` coordinates through the weighted isometry. -/
theorem weightedPairEval_continuous (W : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)] (hW : ∀ m : ℤ, 0 < W m)
    (b : Bool) (m : ℤ) :
    Continuous (fun x : WeightedPairHilbert W => x b m) := by
  have hp : Continuous (fun y : PairLp => y b) :=
    (PiLp.proj (𝕜 := ℂ) (p := (2 : ℝ≥0∞))
      (β := fun _ : Bool => lp (fun _ : ℤ => ℂ) 2) b).continuous
  have heval : Continuous (fun y : lp (fun _ : ℤ => ℂ) 2 => y m) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).continuous
  have h : Continuous (fun y : PairLp => y b m) := heval.comp hp
  have hweighted : Continuous (fun x : WeightedPairHilbert W => weightedPairIsoLp W hW x b m) :=
    h.comp (weightedPairIsoLp W hW).continuous
  have hraw : (fun x : WeightedPairHilbert W => x b m) =
      fun x => (W m : ℂ)⁻¹ * (weightedPairIsoLp W hW x b m) := by
    funext x
    rw [weightedPairIsoLp_apply]
    have hWc : (W m : ℂ) ≠ 0 := by exact_mod_cast (hW m).ne'
    field_simp
  rw [hraw]
  exact continuous_const.mul hweighted

/-- The source real form with sign `ε`: its second raw Fourier sequence is
`ε` times the conjugate of the reflected first sequence. -/
def weightedPairRealForm (W : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (hW : ∀ m : ℤ, 0 < W m) (ε : ℝ) : Set (WeightedPairHilbert W) :=
  {x | ∀ m : ℤ,
    x false m = (ε : ℂ) * star (x true (-m))}

/-- The real form is bundled as a genuine real submodule of the complex
weighted Hilbert pair, with the complex space viewed by restriction of
scalars. -/
abbrev WeightedPairRealCarrier (W : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < W m ^ 2)] :=
  RestrictScalars ℝ ℂ (WeightedPairHilbert W)

def weightedPairRealFormSubmodule (W : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)] (hW : ∀ m : ℤ, 0 < W m) (ε : ℝ) :
    Submodule ℝ (WeightedPairRealCarrier W) where
  carrier := weightedPairRealForm W hW ε
  zero_mem' := by
    intro m
    change (0 : ℂ) = (ε : ℂ) * star (0 : ℂ)
    simp
  add_mem' := by
    intro x y hx hy m
    change WeightedPairHilbert W at x
    change WeightedPairHilbert W at y
    change ∀ j : ℤ, (x : WeightedPairHilbert W) false j =
      (ε : ℂ) * star ((x : WeightedPairHilbert W) true (-j)) at hx
    change ∀ j : ℤ, (y : WeightedPairHilbert W) false j =
      (ε : ℂ) * star ((y : WeightedPairHilbert W) true (-j)) at hy
    change ((x : WeightedPairHilbert W) false m + (y : WeightedPairHilbert W) false m) =
      (ε : ℂ) * star ((x : WeightedPairHilbert W) true (-m) +
        (y : WeightedPairHilbert W) true (-m))
    simp only [WithLp.ofLp_add, Pi.add_apply, hx m, hy m]
    rw [star_add]
    ring
  smul_mem' := by
    intro r x hx m
    change WeightedPairHilbert W at x
    change ∀ j : ℤ, (x : WeightedPairHilbert W) false j =
      (ε : ℂ) * star ((x : WeightedPairHilbert W) true (-j)) at hx
    change ((r : ℂ) * ((x : WeightedPairHilbert W) false m)) =
      (ε : ℂ) * star ((r : ℂ) * ((x : WeightedPairHilbert W) true (-m)))
    rw [hx m]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
    ring


/-- The coefficient real form is exactly the physical source relation
`q_m = ε conj(p_{-m})`, with no change of Fourier labels. -/
theorem periodOnePhysicalPair_realForm_iff (ω : ℤ → ℝ)
    (hω : EvenWeight ω) :
    letI : Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2) :=
      ⟨fun m => sq_pos_of_pos (periodOneWeight_pos ω hω m)⟩
    ∀ (x : WeightedPairHilbert (periodOneWeight ω)) (ε : ℝ),
      x ∈ weightedPairRealForm (periodOneWeight ω)
          (fun m => periodOneWeight_pos ω hω m) ε ↔
        ∀ m : ℤ,
          physicalFourier (periodOnePhysicalPair ω hω x).2 m =
            (ε : ℂ) * star (physicalFourier (periodOnePhysicalPair ω hω x).1 (-m)) := by
  letI : Fact (∀ m : ℤ, 0 < periodOneWeight ω m ^ 2) :=
    ⟨fun m => sq_pos_of_pos (periodOneWeight_pos ω hω m)⟩
  intro x ε
  constructor
  · intro hx m
    rw [(periodOnePhysicalPair_fourier ω hω x m).2,
      (periodOnePhysicalPair_fourier ω hω x (-m)).1]
    exact hx m
  · intro hx m
    have hm := hx m
    rw [(periodOnePhysicalPair_fourier ω hω x m).2,
      (periodOnePhysicalPair_fourier ω hω x (-m)).1] at hm
    exact hm


theorem weightedPairRealForm_isClosed (W : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)] (hW : ∀ m : ℤ, 0 < W m) (ε : ℝ) :
    IsClosed (weightedPairRealForm W hW ε) := by
  have hset : weightedPairRealForm W hW ε =
      ⋂ m : ℤ, {x | x false m = (ε : ℂ) * star (x true (-m))} := by
    ext x
    simp [weightedPairRealForm]
  rw [hset]
  refine isClosed_iInter fun m => ?_
  exact isClosed_eq (weightedPairEval_continuous W hW false m)
    (continuous_const.mul (continuous_star.comp (weightedPairEval_continuous W hW true (-m))))

theorem weightedPairRealFormSubmodule_isClosed (W : ℤ → ℝ)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)] (hW : ∀ m : ℤ, 0 < W m) (ε : ℝ) :
    IsClosed (weightedPairRealFormSubmodule W hW ε : Set (WeightedPairRealCarrier W)) :=
  weightedPairRealForm_isClosed W hW ε

/-- A closed ball in the actual joint weighted Hilbert norm. -/
abbrev WeightedPairClosedBall (W : ℤ → ℝ) [Fact (∀ m : ℤ, 0 < W m ^ 2)] (r : ℝ) :=
  Metric.closedBall (0 : WeightedPairHilbert W) r

theorem weightedPairClosedBall_complete (W : ℤ → ℝ) (hW : ∀ m : ℤ, 0 < W m)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (r : ℝ) : CompleteSpace (WeightedPairClosedBall W r) := by
  letI : CompleteSpace (WeightedPairHilbert W) := inferInstance
  exact Metric.isClosed_closedBall.completeSpace_coe

theorem weightedPairClosedBall_complete_of_center (W : ℤ → ℝ)
    (hW : ∀ m : ℤ, 0 < W m) [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (c : WeightedPairHilbert W) (r : ℝ) :
    CompleteSpace {x : WeightedPairHilbert W // dist x c ≤ r} := by
  letI : CompleteSpace (WeightedPairHilbert W) := inferInstance
  exact Metric.isClosed_closedBall.completeSpace_coe

/-- Either source real form is complete in its induced metric, by closedness
inside the complete weighted-pair carrier. -/
theorem weightedPairRealForm_complete (W : ℤ → ℝ) (hW : ∀ m : ℤ, 0 < W m)
    [Fact (∀ m : ℤ, 0 < W m ^ 2)]
    (ε : ℝ) : CompleteSpace {x : WeightedPairHilbert W // x ∈ weightedPairRealForm W hW ε} := by
  letI : CompleteSpace (WeightedPairHilbert W) := inferInstance
  letI : IsClosed (weightedPairRealForm W hW ε) := weightedPairRealForm_isClosed W hW ε
  exact IsClosed.completeSpace_coe

/-- A closed ball with its induced metric inside either real form is complete
for every center in that form and every radius. -/
theorem weightedPairRealForm_closedBall_complete (W : ℤ → ℝ)
    (hW : ∀ m : ℤ, 0 < W m) [Fact (∀ m : ℤ, 0 < W m ^ 2)] (ε : ℝ)
    (c : {x : WeightedPairHilbert W // x ∈ weightedPairRealForm W hW ε}) (r : ℝ) :
    CompleteSpace {x : {x : WeightedPairHilbert W // x ∈ weightedPairRealForm W hW ε} //
      dist x c ≤ r} := by
  letI : CompleteSpace {x : WeightedPairHilbert W // x ∈ weightedPairRealForm W hW ε} :=
    weightedPairRealForm_complete W hW ε
  exact Metric.isClosed_closedBall.completeSpace_coe

/-- Every weighted sequence carrier is complete, and so is the Euclidean pair. -/
theorem weightedPair_complete (W : ℤ → ℝ) (hW : ∀ m : ℤ, 0 < W m) :
    letI : Fact (∀ m : ℤ, 0 < W m ^ 2) := ⟨fun m => sq_pos_of_pos (hW m)⟩
    CompleteSpace (WeightedPairHilbert W) := by
  letI : Fact (∀ m : ℤ, 0 < W m ^ 2) := ⟨fun m => sq_pos_of_pos (hW m)⟩
  infer_instance

end NlsGge.Atomic.KST002
