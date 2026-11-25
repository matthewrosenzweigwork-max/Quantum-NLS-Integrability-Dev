import Mathlib
import QuantumNLS.RB01Columns

/-! R-EC25334D (`thm:global-B01-actions`), stage RB01-5: the collective square-summable column bound.

Source (collective_actions.tex:239-256): "`Σ_n ‖A_n(w,q)χ_{n,1}‖² = (4κ/L) Σ_{n,k} |q_k|²/|w+4π(n-k)/L|² ≤ C‖q‖²`,
`Σ_n ‖A_n(w,q)χ_{n,2}‖² ≤ C‖q^♯‖²`.  The first identity follows by putting `m = 2k - n` ... In each summand `A_n`
uses its own parity ... These are bounds for bounded linear maps into `ℓ²(L²)`, not merely pointwise summability
statements."

Here `A_n(w,u)χ_{n,j} = R_{0,n}(p_n + w)(V_u χ_{n,j})` (the actual free resolvent of parity `(-1)^n`, applied to
`Vchi`; cf. `RB01Columns.adjT_chi`).  Proved, on the real slice:
* `emode_orthonormal` (the scalar modes are orthonormal) and Bessel for `û_k = ⟪e_k, u⟫`.
* `inner_chi_Vchi`: `⟪χ_{2k-n,1-j}, V_u χ_{n,j}⟫ = ±2i√κ L^{-1/2} û_k` (resp. `conj`), and same-spin entries vanish.
* `norm_sq_col`: `‖R_{0,n}(z) V_u χ_{n,j}‖² = Σ_k (2√κ L^{-1/2})² |û_k|² / |z - p_{2k-n}|²` (Parseval in `chiBasis`).
* **`column_l2`**: for `r/2 ≤ |w| ≤ r`, `Σ_n ‖R_{0,n}(p_n+w) V_u χ_{n,j}‖² ≤ (2√κ L^{-1/2})² G ‖u‖²`.
* **`colCLM`**: `u ↦ (R_{0,n}(p_n+w) V_u χ_{n,j})_{n∈ℤ}` is a bounded real-linear map `L²(0,L) → ℓ²(ℤ; L²(0,L;ℂ²))`. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Set Metric Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate
namespace QuantumNLS.RB01L2Columns
open QuantumNLS.LocalSpectral QuantumNLS.Local002 QuantumNLS.Local002Free QuantumNLS.Local002Rank
  QuantumNLS.Local002SA QuantumNLS.Local002Basis QuantumNLS.RB01FourierAction QuantumNLS.RB01SquareSmall
  QuantumNLS.RB01Resolvent QuantumNLS.RB01Columns

variable {L κ : ℝ}

/-! ### Orthonormality of the scalar modes -/

theorem emode_orthonormal [Fact (0 < L)] : Orthonormal ℂ (emode L) := by
  rw [orthonormal_iff_ite]
  intro a b
  rw [← toInterval_modeLp, ← toInterval_modeLp, LinearIsometryEquiv.inner_map_map,
    ← (QuantumNLS.Fourier.fourierL2 L).inner_map_map, QuantumNLS.Fourier.fourierL2_modeLp,
    QuantumNLS.Fourier.fourierL2_modeLp, lp.inner_single_left]
  rcases eq_or_ne a b with rfl | h
  · simp [lp.single_apply]
  · simp [lp.single_apply, Pi.single_apply, h, Ne.symm h]

/-! ### The matrix entries of `V_u` in the free basis -/

lemma exp_rate_normSq (L : ℝ) (m : ℤ) (j : Fin 2) (x : ℝ) :
    conj (Complex.exp (rate L m j * (x : ℂ))) * Complex.exp (rate L m j * (x : ℂ)) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  have : conj (rate L m j * (x : ℂ)) + rate L m j * (x : ℂ) = 0 := by
    simp only [rate, map_mul, map_div₀, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [this, Complex.exp_zero]

theorem pt_inner10 (κ L : ℝ) (w : ℂ) (k n : ℤ) (x : ℝ) :
    ⟪chiFun L (2 * k - n) 1 x, Vpt κ w (chiFun L n 0 x)⟫_ℂ =
      ((2 * Complex.I) * (Real.sqrt κ : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)) *
        (conj (emodeFun L k x) * w) := by
  have hN := exp_rate_normSq L n 0 x
  obtain ⟨h0, -⟩ := chiFun_zero_apply L n x
  rw [QuantumNLS.Local002SA.Vpt_explicit, h0]
  unfold chiFun
  rw [inner_smul_left, EuclideanSpace.inner_single_left, vec2_one, ← exp_reflect0 L k n x]
  simp only [map_one, one_mul, emodeFun, map_mul, Complex.conj_ofReal]
  linear_combination (2 * Complex.I * (Real.sqrt κ : ℂ) * w * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
    (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * conj (Complex.exp (2 * Real.pi * Complex.I * k * x / L))) * hN

theorem pt_inner01 (κ L : ℝ) (w : ℂ) (k n : ℤ) (x : ℝ) :
    ⟪chiFun L (2 * k - n) 0 x, Vpt κ w (chiFun L n 1 x)⟫_ℂ =
      (-(2 * Complex.I) * (Real.sqrt κ : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)) *
        conj (conj (emodeFun L k x) * w) := by
  have hN := exp_rate_normSq L n 1 x
  obtain ⟨h1, -⟩ := chiFun_one_apply L n x
  rw [QuantumNLS.Local002SA.Vpt_explicit, h1]
  unfold chiFun
  rw [inner_smul_left, EuclideanSpace.inner_single_left, vec2_zero, ← exp_reflect1 L k n x]
  simp only [map_one, one_mul, emodeFun, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  linear_combination (-(2 * Complex.I) * (Real.sqrt κ : ℂ) * conj w * (((Real.sqrt L)⁻¹ : ℝ) : ℂ) *
    (((Real.sqrt L)⁻¹ : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * k * x / L)) * hN

theorem pt_inner_same (κ L : ℝ) (w : ℂ) (m n : ℤ) (j : Fin 2) (x : ℝ) :
    ⟪chiFun L m j x, Vpt κ w (chiFun L n j x)⟫_ℂ = 0 := by
  unfold chiFun
  rw [inner_smul_left, EuclideanSpace.inner_single_left, QuantumNLS.Local002SA.Vpt_explicit]
  fin_cases j <;> simp

/-- The Lp inner products. -/
theorem inner_chi_Vchi (hL : 0 < L) (u : Lp ℂ 2 (μI L)) (k n : ℤ) (j : Fin 2) :
    ‖⟪chi L (2 * k - n) (flip j), Vchi κ u n j⟫_ℂ‖ =
      2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ‖⟪emode L k, u⟫_ℂ‖ := by
  have hc : ‖(2 * Complex.I) * (Real.sqrt κ : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)‖ =
      2 * Real.sqrt κ * (Real.sqrt L)⁻¹ := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (by positivity)]
    norm_num
  have hint : ∀ f g : ℝ → E2, ∀ F : H2 L, ∀ G : H2 L, (F : ℝ → E2) =ᵐ[μI L] f →
      (G : ℝ → E2) =ᵐ[μI L] g → ⟪F, G⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ ∂(μI L) := by
    intro f g F G hF hG
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hF, hG] with x a b
    rw [a, b]
  have hcoe : ((u : ℝ → ℂ)) =ᵐ[μI L] (u : ℝ → ℂ) := Filter.EventuallyEq.rfl
  have heu : ⟪emode L k, u⟫_ℂ = ∫ x, conj (emodeFun L k x) * (u : ℝ → ℂ) x ∂(μI L) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_emode L k] with x a
    rw [a]
    simp only [RCLike.inner_apply]
    try ring
  fin_cases j
  · have e := hint _ _ _ _ (memLp_chiFun L (2 * k - n) 1).coeFn_toLp (memLp_Vchi κ u n 0).coeFn_toLp
    change ‖⟪chi L (2 * k - n) 1, Vchi κ u n 0⟫_ℂ‖ = _
    unfold Vchi
    rw [show chi L (2 * k - n) 1 = (memLp_chiFun L (2 * k - n) 1).toLp _ from rfl, e]
    simp only [pt_inner10]
    rw [integral_const_mul, norm_mul, hc, ← heu]
  · have e := hint _ _ _ _ (memLp_chiFun L (2 * k - n) 0).coeFn_toLp (memLp_Vchi κ u n 1).coeFn_toLp
    change ‖⟪chi L (2 * k - n) 0, Vchi κ u n 1⟫_ℂ‖ = _
    unfold Vchi
    rw [show chi L (2 * k - n) 0 = (memLp_chiFun L (2 * k - n) 0).toLp _ from rfl, e]
    simp only [pt_inner01]
    have hc' : ‖-(2 * Complex.I) * (Real.sqrt κ : ℂ) * (((Real.sqrt L)⁻¹ : ℝ) : ℂ)‖ =
        2 * Real.sqrt κ * (Real.sqrt L)⁻¹ := by
      rw [neg_mul, neg_mul, norm_neg]; exact hc
    rw [integral_const_mul, integral_conj, norm_mul, hc', RCLike.norm_conj, ← heu]

theorem inner_chi_Vchi_same (u : Lp ℂ 2 (μI L)) (m n : ℤ) (j : Fin 2) :
    ⟪chi L m j, Vchi κ u n j⟫_ℂ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have : (fun x => ⟪(chi L m j : ℝ → E2) x, (Vchi κ u n j : ℝ → E2) x⟫_ℂ) =ᵐ[μI L] fun _ => 0 := by
    filter_upwards [(memLp_chiFun L m j).coeFn_toLp, (memLp_Vchi κ u n j).coeFn_toLp] with x a b
    change ⟪(chi L m j : ℝ → E2) x, (Vchi κ u n j : ℝ → E2) x⟫_ℂ = 0
    have a' : (chi L m j : ℝ → E2) x = chiFun L m j x := a
    have b' : (Vchi κ u n j : ℝ → E2) x = Vpt κ ((u : ℝ → ℂ) x) (chiFun L n j x) := b
    rw [a', b', pt_inner_same]
  rw [integral_congr_ae this, integral_zero]

/-! ### Parseval in the free basis -/

theorem parseval_chi (hL : 0 < L) (n : ℤ) (y : H2 L) :
    Summable (fun p : Idx n => ‖⟪chi L p.1.1 p.1.2, y⟫_ℂ‖ ^ 2) ∧
      ‖y‖ ^ 2 = ∑' p : Idx n, ‖⟪chi L p.1.1 p.1.2, y⟫_ℂ‖ ^ 2 := by
  set b := chiBasis hL n
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hc : ∀ p : Idx n, b.repr y p = ⟪chi L p.1.1 p.1.2, y⟫_ℂ := fun p => by
    rw [b.repr_apply_apply, chiBasis_apply]
  have hs := (lp.memℓp (b.repr y)).summable hp
  have hn := lp.norm_rpow_eq_tsum hp (b.repr y)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, hc, LinearIsometryEquiv.norm_map] at hs hn
  exact ⟨hs, hn⟩

/-- The reindexing `k ↦ (2k - n, 1 - j)` of the parity class. -/
def reflIdx (n : ℤ) (j : Fin 2) (k : ℤ) : Idx n := ⟨(2 * k - n, flip j), parity_reflect k n⟩

theorem reflIdx_injective (n : ℤ) (j : Fin 2) : Function.Injective (reflIdx n j) := by
  intro a b h
  have := congrArg (fun p : Idx n => p.1.1) h
  simp only [reflIdx] at this
  omega

theorem flip_cases (i j : Fin 2) (h : i ≠ j) : i = flip j := by
  fin_cases i <;> fin_cases j <;> simp_all [RB01FourierAction.flip]

/-- `‖R_{0,n}(z) V_u χ_{n,j}‖² = Σ_k |z - p_{2k-n}|^{-2} (2√κ L^{-1/2} |û_k|)²`. -/
theorem norm_sq_col (hL : 0 < L) {n : ℤ} {z : ℂ} (hz : ∀ m : ℤ, z ≠ (pm L m : ℂ))
    {R0 R0' : H2 L →L[ℂ] H2 L} (hR0 : IsResolvent L κ (fun _ => 0) (parity n) z R0)
    (hR0' : IsResolvent L κ (fun _ => 0) (parity n) (conj z) R0') (u : Lp ℂ 2 (μI L)) (j : Fin 2) :
    Summable (fun k : ℤ => ‖z - (pm L (2 * k - n) : ℂ)‖⁻¹ ^ 2 *
        (2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ‖⟪emode L k, u⟫_ℂ‖) ^ 2) ∧
      ‖R0 (Vchi κ u n j)‖ ^ 2 = ∑' k : ℤ, ‖z - (pm L (2 * k - n) : ℂ)‖⁻¹ ^ 2 *
        (2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 := by
  have hadj := free_adjoint hL hR0 hR0'
  have hcoef : ∀ p : Idx n, ‖⟪chi L p.1.1 p.1.2, R0 (Vchi κ u n j)⟫_ℂ‖ =
      ‖z - (pm L p.1.1 : ℂ)‖⁻¹ * ‖⟪chi L p.1.1 p.1.2, Vchi κ u n j⟫_ℂ‖ := by
    intro p
    have hne : conj z ≠ (pm L p.1.1 : ℂ) := fun h => hz p.1.1 (by
      rw [← Complex.conj_conj z, h, Complex.conj_ofReal])
    rw [← hadj, ContinuousLinearMap.adjoint_inner_right, res_chi hL p.1.2 hR0' p.2 hne,
      inner_smul_left, norm_mul, RCLike.norm_conj, norm_inv, conj_annulus]
  obtain ⟨hs, hpar⟩ := parseval_chi hL n (R0 (Vchi κ u n j))
  set F : Idx n → ℝ := fun p => ‖⟪chi L p.1.1 p.1.2, R0 (Vchi κ u n j)⟫_ℂ‖ ^ 2 with hF
  have hsupp : Function.support F ⊆ Set.range (reflIdx n j) := by
    intro p hp
    have hp' : ⟪chi L p.1.1 p.1.2, Vchi κ u n j⟫_ℂ ≠ 0 := by
      intro h0
      apply hp
      simp only [hF, hcoef, h0, norm_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
    have hj : p.1.2 = flip j := by
      apply flip_cases
      intro h
      apply hp'
      rw [h]; exact inner_chi_Vchi_same u _ _ _
    obtain ⟨t, ht⟩ := parity_eq_iff_even p.2.symm
    refine ⟨n + t, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · simp only [reflIdx]; omega
    · exact hj.symm
  have hval : ∀ k, F (reflIdx n j k) = ‖z - (pm L (2 * k - n) : ℂ)‖⁻¹ ^ 2 *
      (2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 := by
    intro k
    simp only [hF, hcoef, reflIdx]
    rw [inner_chi_Vchi hL u k n j, mul_pow]
  have heq := (reflIdx_injective n j).tsum_eq hsupp
  have hsum : Summable (fun k => F (reflIdx n j k)) := hs.comp_injective (reflIdx_injective n j)
  simp only [hval] at heq hsum
  exact ⟨hsum, hpar.trans heq.symm⟩

/-! ### The collective bound -/

theorem column_l2 (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) [Fact (0 < L)]
    {w : ℂ} (hw1 : r / 2 ≤ ‖w‖) (hw2 : ‖w‖ ≤ r) (u : Lp ℂ 2 (μI L)) (j : Fin 2) :
    Summable (fun n : ℤ =>
        ‖resolvent L κ (fun _ => 0) (parity n) ((pm L n : ℂ) + w) (Vchi κ u n j)‖ ^ 2) ∧
      ∑' n : ℤ, ‖resolvent L κ (fun _ => 0) (parity n) ((pm L n : ℂ) + w) (Vchi κ u n j)‖ ^ 2 ≤
        (2 * Real.sqrt κ * (Real.sqrt L)⁻¹) ^ 2 * (∑' m, gmaj r (2 * Real.pi / L - r) m) * ‖u‖ ^ 2 := by
  set a := 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ with ha
  set G := ∑' m, gmaj r (2 * Real.pi / L - r) m with hG
  set g := gmaj r (2 * Real.pi / L - r) with hg
  have hzn : ∀ n : ℤ, ‖((pm L n : ℂ) + w) - (pm L n : ℂ)‖ = ‖w‖ := fun n => by ring_nf
  have hbd : ∀ n m : ℤ, 0 < ‖((pm L n : ℂ) + w) - (pm L m : ℂ)‖ ∧
      ‖((pm L n : ℂ) + w) - (pm L m : ℂ)‖⁻¹ ^ 2 ≤ g (m - n) := fun n m =>
    inv_sq_le_gmaj (l := m) hL hr hr2 (by rw [hzn]; exact hw1) (by rw [hzn]; exact hw2)
  set Φ : ℤ → ℤ → ℝ := fun k n => ‖((pm L n : ℂ) + w) - (pm L (2 * k - n) : ℂ)‖⁻¹ ^ 2 *
    (a * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 with hΦ
  have hΦ0 : ∀ k n, 0 ≤ Φ k n := fun k n => by positivity
  have hinj : ∀ k : ℤ, Function.Injective (fun n : ℤ => (2 * k - n) - n) := fun k x y h => by
    simp only at h; omega
  have hgs : ∀ k : ℤ, Summable (fun n : ℤ => g ((2 * k - n) - n)) := fun k =>
    (summable_gmaj _ _).comp_injective (hinj k)
  have hgle : ∀ k : ℤ, ∑' n : ℤ, g ((2 * k - n) - n) ≤ G := fun k =>
    tsum_comp_le_tsum_of_inj (summable_gmaj _ _) (gmaj_nonneg _ _) (hinj k)
  have hrow : ∀ k, Summable (Φ k) := fun k =>
    Summable.of_nonneg_of_le (hΦ0 k) (fun n => mul_le_mul_of_nonneg_right (hbd n _).2 (sq_nonneg _))
      ((hgs k).mul_right _)
  have hrowle : ∀ k, ∑' n, Φ k n ≤ (a * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 * G := fun k => by
    calc ∑' n, Φ k n ≤ ∑' n, g ((2 * k - n) - n) * (a * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 :=
          (hrow k).tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (hbd n _).2 (sq_nonneg _))
            ((hgs k).mul_right _)
      _ = (∑' n, g ((2 * k - n) - n)) * (a * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 := tsum_mul_right
      _ ≤ G * (a * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 := mul_le_mul_of_nonneg_right (hgle k) (sq_nonneg _)
      _ = (a * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 * G := mul_comm _ _
  have hbes := (emode_orthonormal (L := L)).inner_products_summable (x := u)
  have hbesle := (emode_orthonormal (L := L)).tsum_inner_products_le (x := u)
  have hG0 : 0 ≤ G := tsum_nonneg (gmaj_nonneg _ _)
  have hcol : Summable (fun k => (a * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 * G) := by
    have : (fun k => (a * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 * G) = fun k => (a ^ 2 * G) * ‖⟪emode L k, u⟫_ℂ‖ ^ 2 := by
      funext k; ring
    rw [this]; exact hbes.mul_left _
  have hU : Summable (Function.uncurry Φ) := by
    refine (summable_prod_of_nonneg (fun q => hΦ0 q.1 q.2)).2 ⟨hrow, ?_⟩
    exact Summable.of_nonneg_of_le (fun k => tsum_nonneg (hΦ0 k)) hrowle hcol
  -- per label, the actual resolvent column
  have hres : ∀ n : ℤ, ∃ R0 R0' : H2 L →L[ℂ] H2 L,
      IsResolvent L κ (fun _ => 0) (parity n) ((pm L n : ℂ) + w) R0 ∧
      IsResolvent L κ (fun _ => 0) (parity n) (conj ((pm L n : ℂ) + w)) R0' := fun n => by
    have h1 : r / 2 ≤ ‖((pm L n : ℂ) + w) - (pm L n : ℂ)‖ := by rw [hzn]; exact hw1
    have h2 : ‖((pm L n : ℂ) + w) - (pm L n : ℂ)‖ ≤ r := by rw [hzn]; exact hw2
    obtain ⟨R0, hR0, -⟩ := free_res_annulus (κ := κ) hL hr hr2 h1 h2
    obtain ⟨R0', hR0', -⟩ := free_res_annulus (κ := κ) hL hr hr2 (by rwa [conj_annulus])
      (by rwa [conj_annulus])
    exact ⟨R0, R0', hR0, hR0'⟩
  have hcolumn : ∀ n : ℤ, Summable (fun k => Φ k n) ∧
      ‖resolvent L κ (fun _ => 0) (parity n) ((pm L n : ℂ) + w) (Vchi κ u n j)‖ ^ 2 =
        ∑' k, Φ k n := fun n => by
    obtain ⟨R0, R0', hR0, hR0'⟩ := hres n
    rw [resolvent_eq hR0]
    exact norm_sq_col hL (fun m => by
      have := (hbd n m).1; intro h; rw [h, sub_self, norm_zero] at this; exact lt_irrefl _ this)
      hR0 hR0' u j
  have hswap : Summable (fun q : ℤ × ℤ => Φ q.2 q.1) :=
    hU.comp_injective (i := Prod.swap) Prod.swap_injective
  have hsumn : Summable (fun n => ∑' k, Φ k n) := hswap.prod
  refine ⟨?_, ?_⟩
  · simpa only [fun n => (hcolumn n).2] using hsumn
  · calc ∑' n, ‖resolvent L κ (fun _ => 0) (parity n) ((pm L n : ℂ) + w) (Vchi κ u n j)‖ ^ 2
        = ∑' n, ∑' k, Φ k n := tsum_congr fun n => (hcolumn n).2
      _ = ∑' k, ∑' n, Φ k n := hU.tsum_comm' (fun k => hrow k) (fun n => (hcolumn n).1)
      _ ≤ ∑' k, (a * ‖⟪emode L k, u⟫_ℂ‖) ^ 2 * G :=
          (hU.prod).tsum_le_tsum hrowle hcol
      _ = a ^ 2 * G * ∑' k, ‖⟪emode L k, u⟫_ℂ‖ ^ 2 := by
          rw [← tsum_mul_left]; congr 1; funext k; ring
      _ ≤ a ^ 2 * G * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left hbesle (by positivity)

/-! ### The bounded linear column map into `ℓ²(ℤ; L²(0,L;ℂ²))` -/

theorem Vchi_real_smul (t : ℝ) (u : Lp ℂ 2 (μI L)) (m : ℤ) (j : Fin 2) :
    Vchi κ (t • u) m j = (t : ℂ) • Vchi κ u m j := by
  apply Lp.ext
  filter_upwards [(memLp_Vchi κ (t • u) m j).coeFn_toLp, (memLp_Vchi κ u m j).coeFn_toLp,
    Lp.coeFn_smul (t : ℂ) (Vchi κ u m j), Lp.coeFn_smul t u] with x a1 a2 a3 a4
  rw [a3, Pi.smul_apply]
  change _ = (t : ℂ) • (Vchi κ u m j : ℝ → E2) x
  unfold Vchi
  rw [a1, a2, a4, Pi.smul_apply, Complex.real_smul, QuantumNLS.Local002.Vpt_real_smul_pot]

/-- The column `n ↦ R_{0,n}(p_n + w) V_u χ_{n,j}`. -/
def colFun (L κ : ℝ) (w : ℂ) (j : Fin 2) (u : Lp ℂ 2 (μI L)) (n : ℤ) : H2 L :=
  resolvent L κ (fun _ => 0) (parity n) ((pm L n : ℂ) + w) (Vchi κ u n j)

theorem memℓp_col (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) [Fact (0 < L)]
    {w : ℂ} (hw1 : r / 2 ≤ ‖w‖) (hw2 : ‖w‖ ≤ r) (u : Lp ℂ 2 (μI L)) (j : Fin 2) :
    Memℓp (colFun L κ w j u) 2 := by
  apply memℓp_gen
  simpa [colFun, ENNReal.toReal_ofNat, Real.rpow_two] using
    (column_l2 (κ := κ) hL hr hr2 hw1 hw2 u j).1

/-- **The collective column map**: a bounded real-linear map `L²(0,L) → ℓ²(ℤ; L²(0,L;ℂ²))`, with
`‖·‖ ≤ 2√κ L^{-1/2} √G`. -/
def colCLM (hL : 0 < L) {r : ℝ} (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) [Fact (0 < L)]
    {w : ℂ} (hw1 : r / 2 ≤ ‖w‖) (hw2 : ‖w‖ ≤ r) (j : Fin 2) :
    Lp ℂ 2 (μI L) →L[ℝ] lp (fun _ : ℤ => H2 L) 2 :=
  LinearMap.mkContinuous
    { toFun := fun u => ⟨colFun L κ w j u, memℓp_col hL hr hr2 hw1 hw2 u j⟩
      map_add' := fun u v => by
        apply lp.ext; funext n
        show colFun L κ w j (u + v) n = colFun L κ w j u n + colFun L κ w j v n
        simp only [colFun, Vchi_add, map_add]
      map_smul' := fun t u => by
        apply lp.ext; funext n
        show colFun L κ w j (t • u) n = t • colFun L κ w j u n
        simp only [colFun, Vchi_real_smul, map_smul]
        exact Complex.coe_smul t _ }
    (2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * Real.sqrt (∑' m, gmaj r (2 * Real.pi / L - r) m))
    (fun u => by
      have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      have hn := lp.norm_rpow_eq_tsum hp (⟨colFun L κ w j u, memℓp_col hL hr hr2 hw1 hw2 u j⟩ :
        lp (fun _ : ℤ => H2 L) 2)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hn
      have hb := (column_l2 (κ := κ) hL hr hr2 hw1 hw2 u j).2
      change ‖(⟨colFun L κ w j u, memℓp_col hL hr hr2 hw1 hw2 u j⟩ : lp (fun _ : ℤ => H2 L) 2)‖ ≤ _
      have hG0 : 0 ≤ ∑' m, gmaj r (2 * Real.pi / L - r) m := tsum_nonneg (gmaj_nonneg _ _)
      have hsq : ‖(⟨colFun L κ w j u, memℓp_col hL hr hr2 hw1 hw2 u j⟩ : lp (fun _ : ℤ => H2 L) 2)‖ ^ 2 ≤
          (2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * Real.sqrt (∑' m, gmaj r (2 * Real.pi / L - r) m) *
            ‖u‖) ^ 2 := by
        rw [hn]
        refine hb.trans (le_of_eq ?_)
        rw [show (2 * Real.sqrt κ * (Real.sqrt L)⁻¹ * Real.sqrt (∑' m, gmaj r (2 * Real.pi / L - r) m) *
            ‖u‖) ^ 2 = (2 * Real.sqrt κ * (Real.sqrt L)⁻¹) ^ 2 *
            Real.sqrt (∑' m, gmaj r (2 * Real.pi / L - r) m) ^ 2 * ‖u‖ ^ 2 by ring, Real.sq_sqrt hG0]
      have hy : 0 ≤ 2 * Real.sqrt κ * (Real.sqrt L)⁻¹ *
          Real.sqrt (∑' m, gmaj r (2 * Real.pi / L - r) m) * ‖u‖ := by positivity
      nlinarith [norm_nonneg (⟨colFun L κ w j u, memℓp_col hL hr hr2 hw1 hw2 u j⟩ :
        lp (fun _ : ℤ => H2 L) 2)])

end QuantumNLS.RB01L2Columns
#print axioms QuantumNLS.RB01L2Columns.emode_orthonormal
#print axioms QuantumNLS.RB01L2Columns.inner_chi_Vchi
#print axioms QuantumNLS.RB01L2Columns.norm_sq_col
#print axioms QuantumNLS.RB01L2Columns.column_l2
#print axioms QuantumNLS.RB01L2Columns.colCLM
