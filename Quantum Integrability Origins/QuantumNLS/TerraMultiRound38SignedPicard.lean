import QuantumNLS.TerraMultiRound38SignedResolvent
import QuantumNLS.RiccatiPicardBall

/-! Signed Picard construction in the existing weighted Fourier model.
This is a supporting theorem, not all of REG-005. -/
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Complex Metric
namespace QuantumNLS.TerraMultiRound38SignedPicard
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiPicardBall
open QuantumNLS.TerraMultiRound38SignedResolvent QuantumNLS.RiccatiSobolevE1

def signedFun (L Y : ℝ) (x : Ell2) : ℤ → ℂ :=
  fun k => x k / ((Y : ℂ) + Complex.I * (freq L k : ℂ))

theorem mem_signedFun (L Y : ℝ) (hY : 0 < |Y|) (x : Ell2) : Memℓp (signedFun L Y x) 2 := by
  apply memℓp_gen
  rw [two_toReal]
  simp only [Real.rpow_two]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_)
    ((summable_sq x).mul_left (|Y|⁻¹ ^ 2))
  have h := signed_multiplier_bound Y (freq L k) (abs_pos.mp hY) (x k)
  show ‖x k / ((Y : ℂ) + Complex.I * (freq L k : ℂ))‖ ^ 2 ≤ |Y|⁻¹ ^ 2 * ‖x k‖ ^ 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at h2
  exact h2

def signedEll (L Y : ℝ) (hY : 0 < |Y|) (x : Ell2) : Ell2 :=
  ⟨signedFun L Y x, mem_signedFun L Y hY x⟩

theorem signedEll_add (L Y : ℝ) (hY : 0 < |Y|) (x y : Ell2) :
    signedEll L Y hY (x + y) = signedEll L Y hY x + signedEll L Y hY y := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_add, Pi.add_apply]
  show (x k + y k) / ((Y : ℂ) + Complex.I * (freq L k : ℂ)) =
    x k / ((Y : ℂ) + Complex.I * (freq L k : ℂ)) + y k / ((Y : ℂ) + Complex.I * (freq L k : ℂ))
  exact add_div _ _ _

theorem signedEll_smul (L Y : ℝ) (hY : 0 < |Y|) (r : ℂ) (x : Ell2) :
    signedEll L Y hY (r • x) = r • signedEll L Y hY x := by
  apply lp.ext
  funext k
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  show r * x k / ((Y : ℂ) + Complex.I * (freq L k : ℂ)) =
    r * (x k / ((Y : ℂ) + Complex.I * (freq L k : ℂ)))
  ring

def signedCLM (L Y : ℝ) (hY : 0 < |Y|) : Ell2 →L[ℂ] Ell2 :=
  LinearMap.mkContinuous
    { toFun := fun x => signedEll L Y hY x
      map_add' := fun x y => signedEll_add L Y hY x y
      map_smul' := fun r x => signedEll_smul L Y hY r x }
    (|Y|⁻¹)
    (fun x => norm_le_of_pointwise (inv_nonneg.2 hY.le)
      (fun k => signed_multiplier_bound Y (freq L k) (abs_pos.mp hY) (x k)))

theorem norm_signedCLM_le (L Y : ℝ) (hY : 0 < |Y|) (x : Ell2) :
    ‖signedCLM L Y hY x‖ ≤ |Y|⁻¹ * ‖x‖ :=
  norm_le_of_pointwise (y := signedCLM L Y hY x) (inv_nonneg.2 hY.le)
    (fun k => signed_multiplier_bound Y (freq L k) (abs_pos.mp hY) (x k))

/-- Riccati right-hand side `T(u,v; r) = R_z u − κ R_z (v r²)`. -/
def signedT {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {Y : ℝ} (hY : 0 < |Y|) (κ : ℝ)
    (u v r : Ell2) : Ell2 :=
  signedCLM L Y hY u - (κ : ℂ) • signedCLM L Y hY (mulBil hL ha v (mulBil hL ha r r))

theorem signedT_zero {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {Y : ℝ} (hY : 0 < |Y|)
    (κ : ℝ) (u v : Ell2) : signedT hL ha hY κ u v 0 = signedCLM L Y hY u := by
  simp [signedT]

theorem signedT_sub {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {Y : ℝ} (hY : 0 < |Y|) (κ : ℝ)
    (u v r r' : Ell2) :
    signedT hL ha hY κ u v r - signedT hL ha hY κ u v r'
      = -((κ : ℂ) • signedCLM L Y hY (mulBil hL ha v (mulBil hL ha r r - mulBil hL ha r' r'))) := by
  simp only [signedT, map_sub, smul_sub]
  abel

/-- The Lipschitz estimate `‖T r − T r'‖ ≤ (|κ| η⁻¹ C² β)(‖r‖+‖r'‖)‖r − r'‖` for `‖v‖ ≤ β`. -/
theorem norm_signedT_sub_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {Y : ℝ} (hY : 0 < |Y|)
    (κ β : ℝ) (u v r r' : Ell2) (hv : ‖v‖ ≤ β) :
    ‖signedT hL ha hY κ u v r - signedT hL ha hY κ u v r'‖
      ≤ (|κ| * |Y|⁻¹ * Cmul L a ^ 2 * β) * ((‖r‖ + ‖r'‖) * ‖r - r'‖) := by
  have hC0 : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hβ0 : 0 ≤ β := (norm_nonneg v).trans hv
  have hk0 : 0 ≤ |κ| := abs_nonneg κ
  have hW : ‖mulBil hL ha v (mulBil hL ha r r - mulBil hL ha r' r')‖
      ≤ Cmul L a * β * (Cmul L a * (‖r‖ + ‖r'‖) * ‖r - r'‖) := by
    have h1 := norm_mulBil_le hL ha v (mulBil hL ha r r - mulBil hL ha r' r')
    have h2 := norm_mulBil_sq_sub_le hL ha r r'
    have h3 : Cmul L a * ‖v‖ * ‖mulBil hL ha r r - mulBil hL ha r' r'‖
        ≤ Cmul L a * β * (Cmul L a * (‖r‖ + ‖r'‖) * ‖r - r'‖) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hv hC0) h2 (norm_nonneg _) (mul_nonneg hC0 hβ0)
    exact h1.trans h3
  rw [signedT_sub, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hR := norm_signedCLM_le L Y hY (mulBil hL ha v (mulBil hL ha r r - mulBil hL ha r' r'))
  calc |κ| * ‖signedCLM L Y hY (mulBil hL ha v (mulBil hL ha r r - mulBil hL ha r' r'))‖
      ≤ |κ| * (|Y|⁻¹ * ‖mulBil hL ha v (mulBil hL ha r r - mulBil hL ha r' r')‖) :=
        mul_le_mul_of_nonneg_left hR hk0
    _ ≤ |κ| * (|Y|⁻¹ * (Cmul L a * β * (Cmul L a * (‖r‖ + ‖r'‖) * ‖r - r'‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (inv_nonneg.2 hY.le)) hk0
    _ = (|κ| * |Y|⁻¹ * Cmul L a ^ 2 * β) * ((‖r‖ + ‖r'‖) * ‖r - r'‖) := by ring

/-- `‖T(u,v;0)‖ ≤ β/η` when `‖u‖ ≤ β`. -/
theorem norm_signedT_zero_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {Y : ℝ} (hY : 0 < |Y|)
    (κ β : ℝ) (u v : Ell2) (hu : ‖u‖ ≤ β) :
    ‖signedT hL ha hY κ u v 0‖ ≤ β / |Y| := by
  rw [signedT_zero, div_eq_inv_mul]
  exact (norm_signedCLM_le L Y hY u).trans (mul_le_mul_of_nonneg_left hu (inv_nonneg.2 hY.le))

/-- The contraction constant on the ball of radius `4β/η`: `|κ| η⁻¹ C² β · 2 · (4β/η) ≤ 1/2`. -/
theorem signed_contract_const_le {L a : ℝ} {Y : ℝ} (hY : 0 < |Y|) (κ β : ℝ)
    (hκ : 16 * |κ| * Cmul L a ^ 2 * β ^ 2 ≤ |Y| ^ 2) :
    |κ| * |Y|⁻¹ * Cmul L a ^ 2 * β * (2 * (4 * β / |Y|)) ≤ 1 / 2 := by
  have hη : |Y| ≠ 0 := hY.ne'
  have e : |κ| * |Y|⁻¹ * Cmul L a ^ 2 * β * (2 * (4 * β / |Y|))
      = (8 * |κ| * Cmul L a ^ 2 * β ^ 2) / |Y| ^ 2 := by
    field_simp
    ring
  rw [e, div_le_iff₀ (pow_pos hY 2)]
  linarith

/-- The Lipschitz constant on the ball `‖r‖ ≤ 4β/η` is `8 |κ| C² β² / η²`, i.e. `O(η⁻²)`. -/
theorem signed_lipschitz {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {Y : ℝ}
    (hY : 0 < |Y|) (κ β : ℝ) (u v r r' : Ell2) (hv : ‖v‖ ≤ β)
    (hr : ‖r‖ ≤ 4 * β / |Y|) (hr' : ‖r'‖ ≤ 4 * β / |Y|) :
    ‖signedT hL ha hY κ u v r - signedT hL ha hY κ u v r'‖
      ≤ (8 * |κ| * Cmul L a ^ 2 * β ^ 2 / |Y| ^ 2) * ‖r - r'‖ := by
  have hK0 : 0 ≤ |κ| * |Y|⁻¹ * Cmul L a ^ 2 * β := by
    have hβ0 : 0 ≤ β := (norm_nonneg v).trans hv
    positivity
  have e : (|κ| * |Y|⁻¹ * Cmul L a ^ 2 * β) * (2 * (4 * β / |Y|))
      = 8 * |κ| * Cmul L a ^ 2 * β ^ 2 / |Y| ^ 2 := by
    have hη : |Y| ≠ 0 := hY.ne'
    field_simp
    ring
  have hsum : ‖r‖ + ‖r'‖ ≤ 2 * (4 * β / |Y|) := by linarith
  calc ‖signedT hL ha hY κ u v r - signedT hL ha hY κ u v r'‖
      ≤ (|κ| * |Y|⁻¹ * Cmul L a ^ 2 * β) * ((‖r‖ + ‖r'‖) * ‖r - r'‖) :=
        norm_signedT_sub_le hL ha hY κ β u v r r' hv
    _ ≤ (|κ| * |Y|⁻¹ * Cmul L a ^ 2 * β) * ((2 * (4 * β / |Y|)) * ‖r - r'‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum (norm_nonneg _)) hK0
    _ = ((|κ| * |Y|⁻¹ * Cmul L a ^ 2 * β) * (2 * (4 * β / |Y|))) * ‖r - r'‖ := by ring
    _ = (8 * |κ| * Cmul L a ^ 2 * β ^ 2 / |Y| ^ 2) * ‖r - r'‖ := by rw [e]

/-- Existence and uniqueness of the small fixed point of the Riccati map (Banach contraction on the
closed ball of radius `4β/η`). Gives the source bound `‖r‖ ≤ 2β/η`. -/
theorem signed_fixed_exists_unique {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {Y : ℝ}
    (hY : 0 < |Y|) (κ β : ℝ) (hβ : 0 < β)
    (hκ : 16 * |κ| * Cmul L a ^ 2 * β ^ 2 ≤ |Y| ^ 2) (u v : Ell2)
    (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β) :
    ∃ r : Ell2, ‖r‖ ≤ 2 * β / |Y| ∧ signedT hL ha hY κ u v r = r ∧
      ∀ r' : Ell2, ‖r'‖ ≤ 4 * β / |Y| → signedT hL ha hY κ u v r' = r' → r' = r := by
  set ρ : ℝ := 4 * β / |Y| with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hT0 := norm_signedT_zero_le hL ha hY κ β u v hu
  -- Lipschitz with constant 1/2 on the ball of radius ρ
  have hcontr : ∀ r r' : Ell2, ‖r‖ ≤ ρ → ‖r'‖ ≤ ρ →
      ‖signedT hL ha hY κ u v r - signedT hL ha hY κ u v r'‖ ≤ (1 / 2) * ‖r - r'‖ := by
    intro r r' hr hr'
    have h := signed_lipschitz hL ha hY κ β u v r r' hv hr hr'
    have hq : 8 * |κ| * Cmul L a ^ 2 * β ^ 2 / |Y| ^ 2 ≤ 1 / 2 := by
      have hη : |Y| ≠ 0 := hY.ne'
      have e : 8 * |κ| * Cmul L a ^ 2 * β ^ 2 / |Y| ^ 2
          = (|κ| * |Y|⁻¹ * Cmul L a ^ 2 * β) * (2 * (4 * β / |Y|)) := by
        field_simp
        ring
      rw [e]
      exact signed_contract_const_le hY κ β hκ
    calc ‖signedT hL ha hY κ u v r - signedT hL ha hY κ u v r'‖
        ≤ (8 * |κ| * Cmul L a ^ 2 * β ^ 2 / |Y| ^ 2) * ‖r - r'‖ := h
      _ ≤ (1 / 2) * ‖r - r'‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
  -- self-map of the closed ball
  have hmaps : ∀ r : Ell2, ‖r‖ ≤ ρ → ‖signedT hL ha hY κ u v r‖ ≤ ρ := by
    intro r hr
    have h1 := hcontr r 0 hr (by simpa using hρ0)
    have h2 : ‖signedT hL ha hY κ u v r‖ ≤ ‖signedT hL ha hY κ u v r - signedT hL ha hY κ u v 0‖
        + ‖signedT hL ha hY κ u v 0‖ := by
      calc ‖signedT hL ha hY κ u v r‖
          = ‖(signedT hL ha hY κ u v r - signedT hL ha hY κ u v 0)
              + signedT hL ha hY κ u v 0‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [sub_zero] at h1
    have hρe : ρ = 4 * (β / |Y|) := by rw [hρdef]; ring
    have hb0 : 0 ≤ β / |Y| := div_nonneg hβ.le hY.le
    have hrr : ‖r‖ ≤ ρ := hr
    rw [hρe] at hrr ⊢
    linarith
  -- the Banach contraction on the closed ball
  haveI : CompleteSpace (closedBall (0 : Ell2) ρ) := isClosed_closedBall.completeSpace_coe
  haveI : Nonempty (closedBall (0 : Ell2) ρ) := ⟨⟨0, mem_closedBall_self hρ0⟩⟩
  let g : closedBall (0 : Ell2) ρ → closedBall (0 : Ell2) ρ :=
    fun r => ⟨signedT hL ha hY κ u v r.1, mem_closedBall_zero_iff.2
      (hmaps r.1 (mem_closedBall_zero_iff.1 r.2))⟩
  have hK : ((1 / 2 : NNReal) : ℝ) = 1 / 2 := by norm_num
  have hlip : LipschitzWith (1 / 2 : NNReal) g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hK, Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact hcontr x.1 y.1 (mem_closedBall_zero_iff.1 x.2) (mem_closedBall_zero_iff.1 y.2)
  have hg : ContractingWith (1 / 2 : NNReal) g := ⟨by norm_num, hlip⟩
  have hfix := hg.fixedPoint_isFixedPt
  set r0 : closedBall (0 : Ell2) ρ := ContractingWith.fixedPoint g hg with hr0def
  have hfix0 : signedT hL ha hY κ u v r0.1 = r0.1 := congrArg Subtype.val hfix
  have hr0ρ : ‖r0.1‖ ≤ ρ := mem_closedBall_zero_iff.1 r0.2
  refine ⟨r0.1, ?_, hfix0, ?_⟩
  · -- size bound from the contraction and ‖T 0‖ ≤ β/η
    have h2 : ‖r0.1‖ ≤ ‖signedT hL ha hY κ u v r0.1 - signedT hL ha hY κ u v 0‖
        + ‖signedT hL ha hY κ u v 0‖ := by
      calc ‖r0.1‖ = ‖signedT hL ha hY κ u v r0.1‖ := by rw [hfix0]
        _ = ‖(signedT hL ha hY κ u v r0.1 - signedT hL ha hY κ u v 0)
              + signedT hL ha hY κ u v 0‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h3 := hcontr r0.1 0 hr0ρ (by simpa using hρ0)
    rw [sub_zero] at h3
    have e2 : 2 * β / |Y| = 2 * (β / |Y|) := by ring
    rw [e2]
    linarith
  · intro r' hr' hfixr
    have h := hcontr r' r0.1 (by rw [hρdef]; exact hr') hr0ρ
    rw [hfixr, hfix0] at h
    have h0 : ‖r' - r0.1‖ = 0 := by
      have := norm_nonneg (r' - r0.1)
      linarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)


/-- At positive `Y`, the signed multiplier is the existing upper-half-plane multiplier. -/
theorem signedCLM_positive (L Y : ℝ) (hY : 0 < Y) (x : Ell2) :
    signedCLM L Y (abs_pos.mpr hY.ne') x =
      ropCLM L ((Y : ℂ) * Complex.I) (by simpa using hY) x := by
  apply lp.ext
  funext k
  change x k / ((Y : ℂ) + Complex.I * (freq L k : ℂ)) =
    x k / (Complex.I * ((freq L k : ℂ) - (Y : ℂ) * Complex.I))
  congr 1
  ring_nf
  simp [Complex.I_sq]

/-- The signed Picard map at positive `Y` is the accepted positive map. -/
theorem signedT_positive {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (hY : 0 < Y)
    (κ : ℝ) (u v r : Ell2) :
    signedT hL ha (abs_pos.mpr hY.ne') κ u v r =
      riccatiT hL ha (z := (Y : ℂ) * Complex.I) (by simpa using hY) κ u v r := by
  simp only [signedT, riccatiT, signedCLM_positive L Y hY]

/-- A uniform threshold gives signed existence and uniqueness on the model ball. -/
theorem signed_fixed_eventually {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (κ β : ℝ) (hβ : 0 < β) (u v : Ell2) (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β) :
    ∃ B : ℝ, 0 < B ∧ ∀ Y : ℝ, B ≤ |Y| →
      ∃ (hY : 0 < |Y|) (r : Ell2), ‖r‖ ≤ 2 * β / |Y| ∧
        signedT hL ha hY κ u v r = r ∧
        ∀ r' : Ell2, ‖r'‖ ≤ 4 * β / |Y| → signedT hL ha hY κ u v r' = r' → r' = r := by
  let C : ℝ := 16 * |κ| * Cmul L a ^ 2 * β ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C + 1, by linarith, ?_⟩
  intro Y hB
  have hY : 0 < |Y| := by linarith
  have hκ : 16 * |κ| * Cmul L a ^ 2 * β ^ 2 ≤ |Y| ^ 2 := by
    have hh : 0 ≤ (|Y| - 1) * |Y| := mul_nonneg (by linarith) (abs_nonneg Y)
    dsimp [C] at *
    nlinarith
  obtain ⟨r, hr, hf, huq⟩ := signed_fixed_exists_unique hL ha hY κ β hβ hκ u v hu hv
  exact ⟨hY, r, hr, hf, huq⟩

end QuantumNLS.TerraMultiRound38SignedPicard
#print axioms QuantumNLS.TerraMultiRound38SignedPicard.norm_signedCLM_le
#print axioms QuantumNLS.TerraMultiRound38SignedPicard.signed_fixed_exists_unique
#print axioms QuantumNLS.TerraMultiRound38SignedPicard.signed_fixed_eventually
#print axioms QuantumNLS.TerraMultiRound38SignedPicard.signedT_positive
