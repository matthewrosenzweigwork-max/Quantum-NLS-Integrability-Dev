import Mathlib
import QuantumNLS.RiccatiSobolevBanach

/-!
# R-3FEAD88B blocker 3, stage E3a: Picard contraction for the Riccati map on the periodic H^a space

Fixed-point form of the Riccati equation `r' = u + i z r − κ v r²` (source `values:eq:riccati-equation`):
`r = R_z(u − κ v r²)`, with `R_z = ropCLM` (stage E3-pre) and products `mulBil` (algebra, a > 1/2).
Here `T(u,v;r) := R_z u − κ R_z(v r²)` and `η := Im z > 0`, `β` a bound on `‖u‖`, `‖v‖`.

Proved here (all constants explicit):
* `norm_riccatiT_sub_le`: `‖T r − T r'‖ ≤ (|κ| η⁻¹ C² β) (‖r‖ + ‖r'‖) ‖r − r'‖`, with `C = Cmul`.
* `riccatiT_lipschitz_O_eta2`: on the ball `‖r‖, ‖r'‖ ≤ 4β/η`, the Lipschitz constant is
  `8 |κ| C² β² / η²`, which is `O(η⁻²)` (source: "Its Lipschitz constant is O(η⁻²)").
* `riccatiT_fixed_exists_unique`: if `16 |κ| C² β² ≤ η²`, then there is a fixed point `r` with
  `‖r‖ ≤ 2β/η` (source bound `‖r‖ ≤ C/Im z`, `C = 2β`), and it is the unique fixed point in the ball
  `‖r'‖ ≤ 4β/η` (Banach contraction on a complete ball; the source's uniqueness of the small solution).

Standard axioms only. No sorry, admit, native_decide, or new axioms.
-/

set_option autoImplicit false
noncomputable section
open Complex Metric

namespace QuantumNLS.RiccatiPicardBall

open QuantumNLS.RiccatiSobolevBanach

/-- Riccati right-hand side `T(u,v; r) = R_z u − κ R_z (v r²)`. -/
def riccatiT {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    (u v r : Ell2) : Ell2 :=
  ropCLM L z hz u - (κ : ℂ) • ropCLM L z hz (mulBil hL ha v (mulBil hL ha r r))

theorem riccatiT_zero {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ : ℝ) (u v : Ell2) : riccatiT hL ha hz κ u v 0 = ropCLM L z hz u := by
  simp [riccatiT]

theorem mulBil_sq_sub {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (r r' : Ell2) :
    mulBil hL ha r r - mulBil hL ha r' r' = mulBil hL ha r (r - r') + mulBil hL ha (r - r') r' := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  abel

/-- Lipschitz bound of the squared product: `‖r·r − r'·r'‖ ≤ C (‖r‖+‖r'‖) ‖r − r'‖`. -/
theorem norm_mulBil_sq_sub_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) (r r' : Ell2) :
    ‖mulBil hL ha r r - mulBil hL ha r' r'‖ ≤ Cmul L a * (‖r‖ + ‖r'‖) * ‖r - r'‖ := by
  rw [mulBil_sq_sub]
  calc ‖mulBil hL ha r (r - r') + mulBil hL ha (r - r') r'‖
      ≤ ‖mulBil hL ha r (r - r')‖ + ‖mulBil hL ha (r - r') r'‖ := norm_add_le _ _
    _ ≤ Cmul L a * ‖r‖ * ‖r - r'‖ + Cmul L a * ‖r - r'‖ * ‖r'‖ :=
        add_le_add (norm_mulBil_le hL ha _ _) (norm_mulBil_le hL ha _ _)
    _ = Cmul L a * (‖r‖ + ‖r'‖) * ‖r - r'‖ := by ring

theorem riccatiT_sub {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im) (κ : ℝ)
    (u v r r' : Ell2) :
    riccatiT hL ha hz κ u v r - riccatiT hL ha hz κ u v r'
      = -((κ : ℂ) • ropCLM L z hz (mulBil hL ha v (mulBil hL ha r r - mulBil hL ha r' r'))) := by
  simp only [riccatiT, map_sub, smul_sub]
  abel

/-- The Lipschitz estimate `‖T r − T r'‖ ≤ (|κ| η⁻¹ C² β)(‖r‖+‖r'‖)‖r − r'‖` for `‖v‖ ≤ β`. -/
theorem norm_riccatiT_sub_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ β : ℝ) (u v r r' : Ell2) (hv : ‖v‖ ≤ β) :
    ‖riccatiT hL ha hz κ u v r - riccatiT hL ha hz κ u v r'‖
      ≤ (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β) * ((‖r‖ + ‖r'‖) * ‖r - r'‖) := by
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
  rw [riccatiT_sub, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hR := norm_ropCLM_le L z hz (mulBil hL ha v (mulBil hL ha r r - mulBil hL ha r' r'))
  calc |κ| * ‖ropCLM L z hz (mulBil hL ha v (mulBil hL ha r r - mulBil hL ha r' r'))‖
      ≤ |κ| * (z.im⁻¹ * ‖mulBil hL ha v (mulBil hL ha r r - mulBil hL ha r' r')‖) :=
        mul_le_mul_of_nonneg_left hR hk0
    _ ≤ |κ| * (z.im⁻¹ * (Cmul L a * β * (Cmul L a * (‖r‖ + ‖r'‖) * ‖r - r'‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW (inv_nonneg.2 hz.le)) hk0
    _ = (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β) * ((‖r‖ + ‖r'‖) * ‖r - r'‖) := by ring

/-- `‖T(u,v;0)‖ ≤ β/η` when `‖u‖ ≤ β`. -/
theorem norm_riccatiT_zero_le {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ} (hz : 0 < z.im)
    (κ β : ℝ) (u v : Ell2) (hu : ‖u‖ ≤ β) :
    ‖riccatiT hL ha hz κ u v 0‖ ≤ β / z.im := by
  rw [riccatiT_zero, div_eq_inv_mul]
  exact (norm_ropCLM_le L z hz u).trans (mul_le_mul_of_nonneg_left hu (inv_nonneg.2 hz.le))

/-- The contraction constant on the ball of radius `4β/η`: `|κ| η⁻¹ C² β · 2 · (4β/η) ≤ 1/2`. -/
theorem contract_const_le {L a : ℝ} {z : ℂ} (hz : 0 < z.im) (κ β : ℝ)
    (hκ : 16 * |κ| * Cmul L a ^ 2 * β ^ 2 ≤ z.im ^ 2) :
    |κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (2 * (4 * β / z.im)) ≤ 1 / 2 := by
  have hη : z.im ≠ 0 := hz.ne'
  have e : |κ| * z.im⁻¹ * Cmul L a ^ 2 * β * (2 * (4 * β / z.im))
      = (8 * |κ| * Cmul L a ^ 2 * β ^ 2) / z.im ^ 2 := by
    field_simp
    ring
  rw [e, div_le_iff₀ (pow_pos hz 2)]
  linarith

/-- The Lipschitz constant on the ball `‖r‖ ≤ 4β/η` is `8 |κ| C² β² / η²`, i.e. `O(η⁻²)`. -/
theorem riccatiT_lipschitz_O_eta2 {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ}
    (hz : 0 < z.im) (κ β : ℝ) (u v r r' : Ell2) (hv : ‖v‖ ≤ β)
    (hr : ‖r‖ ≤ 4 * β / z.im) (hr' : ‖r'‖ ≤ 4 * β / z.im) :
    ‖riccatiT hL ha hz κ u v r - riccatiT hL ha hz κ u v r'‖
      ≤ (8 * |κ| * Cmul L a ^ 2 * β ^ 2 / z.im ^ 2) * ‖r - r'‖ := by
  have hK0 : 0 ≤ |κ| * z.im⁻¹ * Cmul L a ^ 2 * β := by
    have hβ0 : 0 ≤ β := (norm_nonneg v).trans hv
    positivity
  have e : (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β) * (2 * (4 * β / z.im))
      = 8 * |κ| * Cmul L a ^ 2 * β ^ 2 / z.im ^ 2 := by
    have hη : z.im ≠ 0 := hz.ne'
    field_simp
    ring
  have hsum : ‖r‖ + ‖r'‖ ≤ 2 * (4 * β / z.im) := by linarith
  calc ‖riccatiT hL ha hz κ u v r - riccatiT hL ha hz κ u v r'‖
      ≤ (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β) * ((‖r‖ + ‖r'‖) * ‖r - r'‖) :=
        norm_riccatiT_sub_le hL ha hz κ β u v r r' hv
    _ ≤ (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β) * ((2 * (4 * β / z.im)) * ‖r - r'‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum (norm_nonneg _)) hK0
    _ = ((|κ| * z.im⁻¹ * Cmul L a ^ 2 * β) * (2 * (4 * β / z.im))) * ‖r - r'‖ := by ring
    _ = (8 * |κ| * Cmul L a ^ 2 * β ^ 2 / z.im ^ 2) * ‖r - r'‖ := by rw [e]

/-- Existence and uniqueness of the small fixed point of the Riccati map (Banach contraction on the
closed ball of radius `4β/η`). Gives the source bound `‖r‖ ≤ 2β/η`. -/
theorem riccatiT_fixed_exists_unique {L a : ℝ} (hL : 0 < L) (ha : 1 / 2 < a) {z : ℂ}
    (hz : 0 < z.im) (κ β : ℝ) (hβ : 0 < β)
    (hκ : 16 * |κ| * Cmul L a ^ 2 * β ^ 2 ≤ z.im ^ 2) (u v : Ell2)
    (hu : ‖u‖ ≤ β) (hv : ‖v‖ ≤ β) :
    ∃ r : Ell2, ‖r‖ ≤ 2 * β / z.im ∧ riccatiT hL ha hz κ u v r = r ∧
      ∀ r' : Ell2, ‖r'‖ ≤ 4 * β / z.im → riccatiT hL ha hz κ u v r' = r' → r' = r := by
  set ρ : ℝ := 4 * β / z.im with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hT0 := norm_riccatiT_zero_le hL ha hz κ β u v hu
  -- Lipschitz with constant 1/2 on the ball of radius ρ
  have hcontr : ∀ r r' : Ell2, ‖r‖ ≤ ρ → ‖r'‖ ≤ ρ →
      ‖riccatiT hL ha hz κ u v r - riccatiT hL ha hz κ u v r'‖ ≤ (1 / 2) * ‖r - r'‖ := by
    intro r r' hr hr'
    have h := riccatiT_lipschitz_O_eta2 hL ha hz κ β u v r r' hv hr hr'
    have hq : 8 * |κ| * Cmul L a ^ 2 * β ^ 2 / z.im ^ 2 ≤ 1 / 2 := by
      have hη : z.im ≠ 0 := hz.ne'
      have e : 8 * |κ| * Cmul L a ^ 2 * β ^ 2 / z.im ^ 2
          = (|κ| * z.im⁻¹ * Cmul L a ^ 2 * β) * (2 * (4 * β / z.im)) := by
        field_simp
        ring
      rw [e]
      exact contract_const_le hz κ β hκ
    calc ‖riccatiT hL ha hz κ u v r - riccatiT hL ha hz κ u v r'‖
        ≤ (8 * |κ| * Cmul L a ^ 2 * β ^ 2 / z.im ^ 2) * ‖r - r'‖ := h
      _ ≤ (1 / 2) * ‖r - r'‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
  -- self-map of the closed ball
  have hmaps : ∀ r : Ell2, ‖r‖ ≤ ρ → ‖riccatiT hL ha hz κ u v r‖ ≤ ρ := by
    intro r hr
    have h1 := hcontr r 0 hr (by simpa using hρ0)
    have h2 : ‖riccatiT hL ha hz κ u v r‖ ≤ ‖riccatiT hL ha hz κ u v r - riccatiT hL ha hz κ u v 0‖
        + ‖riccatiT hL ha hz κ u v 0‖ := by
      calc ‖riccatiT hL ha hz κ u v r‖
          = ‖(riccatiT hL ha hz κ u v r - riccatiT hL ha hz κ u v 0)
              + riccatiT hL ha hz κ u v 0‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    rw [sub_zero] at h1
    have hρe : ρ = 4 * (β / z.im) := by rw [hρdef]; ring
    have hb0 : 0 ≤ β / z.im := div_nonneg hβ.le hz.le
    have hrr : ‖r‖ ≤ ρ := hr
    rw [hρe] at hrr ⊢
    linarith
  -- the Banach contraction on the closed ball
  haveI : CompleteSpace (closedBall (0 : Ell2) ρ) := isClosed_closedBall.completeSpace_coe
  haveI : Nonempty (closedBall (0 : Ell2) ρ) := ⟨⟨0, mem_closedBall_self hρ0⟩⟩
  let g : closedBall (0 : Ell2) ρ → closedBall (0 : Ell2) ρ :=
    fun r => ⟨riccatiT hL ha hz κ u v r.1, mem_closedBall_zero_iff.2
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
  have hfix0 : riccatiT hL ha hz κ u v r0.1 = r0.1 := congrArg Subtype.val hfix
  have hr0ρ : ‖r0.1‖ ≤ ρ := mem_closedBall_zero_iff.1 r0.2
  refine ⟨r0.1, ?_, hfix0, ?_⟩
  · -- size bound from the contraction and ‖T 0‖ ≤ β/η
    have h2 : ‖r0.1‖ ≤ ‖riccatiT hL ha hz κ u v r0.1 - riccatiT hL ha hz κ u v 0‖
        + ‖riccatiT hL ha hz κ u v 0‖ := by
      calc ‖r0.1‖ = ‖riccatiT hL ha hz κ u v r0.1‖ := by rw [hfix0]
        _ = ‖(riccatiT hL ha hz κ u v r0.1 - riccatiT hL ha hz κ u v 0)
              + riccatiT hL ha hz κ u v 0‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    have h3 := hcontr r0.1 0 hr0ρ (by simpa using hρ0)
    rw [sub_zero] at h3
    have e2 : 2 * β / z.im = 2 * (β / z.im) := by ring
    rw [e2]
    linarith
  · intro r' hr' hfixr
    have h := hcontr r' r0.1 (by rw [hρdef]; exact hr') hr0ρ
    rw [hfixr, hfix0] at h
    have h0 : ‖r' - r0.1‖ = 0 := by
      have := norm_nonneg (r' - r0.1)
      linarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)

end QuantumNLS.RiccatiPicardBall

#print axioms QuantumNLS.RiccatiPicardBall.riccatiT_fixed_exists_unique
#print axioms QuantumNLS.RiccatiPicardBall.riccatiT_lipschitz_O_eta2
