import QuantumNLS.TransferProductCorrection
import QuantumNLS.Ext025A7SourceMargin

/-! LOCAL-009 stage 1. General distance-to-roots product estimate, valid on
all four sides of a separated contour, then the c=κ ε, ε N≤M expansion.
Only elementary separation and source budgets are hypotheses. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Complex Set Filter Topology Metric
namespace QuantumNLS.LOCAL009R22Transfer
open QuantumNLS.TransferProductCorrection

theorem hasDerivAt_cauchyG_separated {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hz : ∀ j, z ≠ (q j : ℂ)) :
    HasDerivAt (cauchyG N q) (-(N : ℂ)⁻¹ * ∑ j, ((z - (q j : ℂ)) ^ 2)⁻¹) z := by
  have hs : HasDerivAt (fun w : ℂ => ∑ j, (w - (q j : ℂ))⁻¹)
      (∑ j, -(1 : ℂ) / (z - (q j : ℂ)) ^ 2) z := by
    have := HasDerivAt.sum (u := Finset.univ)
      (A := fun j (w : ℂ) => (w - (q j : ℂ))⁻¹) (x := z)
      (fun j _ => ((hasDerivAt_id z).sub_const (q j : ℂ)).inv
        (sub_ne_zero.mpr (hz j)))
    convert this using 1
    · ext w; simp
    · simp
  have := hs.const_mul ((N : ℂ)⁻¹)
  unfold cauchyG
  convert this using 1
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem deriv_cauchyG_separated {N : ℕ} (q : Fin N → ℝ) {z : ℂ} (hz : ∀ j, z ≠ (q j : ℂ)) :
    deriv (cauchyG N q) z = -(N : ℂ)⁻¹ * ∑ j, ((z - (q j : ℂ)) ^ 2)⁻¹ :=
  (hasDerivAt_cauchyG_separated q hz).deriv


theorem pointwise_bound_separated (κ L : ℝ) {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M) {N : ℕ}
    (hN : (1 : ℝ) ≤ N)
    (hsmall : 2 * (|κ| / η) ≤ (N : ℝ))
    (hDsmall : (|κ| / η) ^ 2 / 2 + (|κ| / η) ^ 3 ≤ (N : ℝ))
    (q : Fin N → ℝ) {z : ℂ} (hw : ∀ j, η ≤ ‖z - (q j : ℂ)‖) (hzM : ‖exp (I * z * L)‖ ≤ M) :
    ‖transferS (κ / N) L q z -
        (fz κ L z (cauchyG N q z) -
          (κ ^ 2 / (2 * N)) * fz κ L z (cauchyG N q z) * deriv (cauchyG N q) z)‖ ≤
      Real.exp (|κ| / η) * (1 + M) *
        (((|κ| / η) ^ 2 / 2 + (|κ| / η) ^ 3) ^ 2 + (|κ| / η) ^ 3) / (N : ℝ) ^ 2 := by
  set x : ℝ := |κ| / η with hxdef
  set D : ℝ := x ^ 2 / 2 + x ^ 3 with hD
  have hx : 0 ≤ x := by positivity
  have hD0 : 0 ≤ D := by positivity
  have hz0 : ∀ j, z ≠ (q j : ℂ) := by
    intro j he
    have := hw j
    rw [he, sub_self, norm_zero] at this
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hinv : ∀ j, ‖(z - (q j : ℂ))⁻¹‖ ≤ η⁻¹ := fun j => by
    rw [norm_inv]; exact inv_anti₀ hη (hw j)
  have hinv2 : ∀ j, ‖((z - (q j : ℂ)) ^ 2)⁻¹‖ ≤ η⁻¹ ^ 2 := fun j => by
    rw [norm_inv, norm_pow, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hη (hw j)) 2
  have hNinv : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by simp
  set G : ℂ := cauchyG N q z with hG
  set S2 : ℂ := ∑ j, ((z - (q j : ℂ)) ^ 2)⁻¹ with hS2
  have hderiv : deriv (cauchyG N q) z = -(N : ℂ)⁻¹ * S2 := deriv_cauchyG_separated q hz0
  have hGb : ‖G‖ ≤ η⁻¹ := by
    calc ‖G‖ ≤ ‖(N : ℂ)⁻¹‖ * ∑ j, ‖(z - (q j : ℂ))⁻¹‖ := by
          rw [hG, cauchyG, norm_mul]; gcongr; exact norm_sum_le _ _
      _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, η⁻¹ := by
          rw [hNinv]; gcongr with j; exact hinv j
      _ = η⁻¹ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hS2b : ‖(N : ℂ)⁻¹ * S2‖ ≤ η⁻¹ ^ 2 := by
    calc ‖(N : ℂ)⁻¹ * S2‖ ≤ ‖(N : ℂ)⁻¹‖ * ∑ j, ‖((z - (q j : ℂ)) ^ 2)⁻¹‖ := by
          rw [norm_mul]; gcongr; exact norm_sum_le _ _
      _ ≤ (N : ℝ)⁻¹ * ∑ _j : Fin N, η⁻¹ ^ 2 := by
          rw [hNinv]; gcongr with j; exact hinv2 j
      _ = η⁻¹ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  -- the individual logarithm arguments
  set t : Fin N → ℂ := fun j => I * ((κ / N : ℝ) : ℂ) / (z - (q j : ℂ)) with ht_def
  have htb : ∀ j, ‖t j‖ ≤ x / N := fun j => by
    simp only [ht_def]
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_div, Nat.abs_cast]
    calc |κ| / N / ‖z - (q j : ℂ)‖ ≤ |κ| / N / η :=
          div_le_div_of_nonneg_left (by positivity) hη (hw j)
      _ = x / N := by rw [hxdef]; ring
  have hε : x / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hNpos]; linarith
  have hs1 : ∑ j, t j = I * κ * G := by
    simp only [ht_def, hG, cauchyG, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    push_cast; ring
  set a : ℂ := -((κ : ℂ) ^ 2 / (2 * N)) * (-(N : ℂ)⁻¹ * S2) with ha
  have hs2 : (∑ j, t j ^ 2) / 2 = -a := by
    have hT2 : ∑ j, t j ^ 2 = -((κ : ℂ) ^ 2 * ((N : ℂ)⁻¹) ^ 2) * S2 := by
      simp only [ht_def, hS2, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      push_cast
      rw [div_pow, mul_pow, I_sq]
      ring
    rw [hT2, ha]
    ring
  obtain ⟨Rp, hPp, hRp⟩ := prod_one_add_eq_exp t hε htb
  obtain ⟨Rm, hPm, hRm⟩ := prod_one_add_eq_exp (fun j => -t j) hε
    (fun j => by rw [norm_neg]; exact htb j)
  have hPp' : ∏ j, (1 + t j) = exp (I * κ * G) * exp (a + Rp) := by
    rw [hPp, ← Complex.exp_add]
    congr 1
    rw [hs1, hs2]; ring
  have hPm' : ∏ j, (1 + -t j) = exp (-(I * κ * G)) * exp (a + Rm) := by
    rw [hPm, ← Complex.exp_add]
    congr 1
    simp only [Finset.sum_neg_distrib, neg_sq]
    rw [hs1, hs2]; ring
  have hm : ∀ j, (1 - I * ((κ / N : ℝ) : ℂ) / (z - (q j : ℂ))) = 1 + -t j := fun j => by
    simp only [ht_def]; ring
  have hS : transferS (κ / N) L q z =
      (∏ j, (1 + t j)) + exp (I * z * L) * ∏ j, (1 + -t j) := by
    rw [transferS]
    simp only [hm]
    rfl
  have hid : transferS (κ / N) L q z -
        (fz κ L z G - (κ ^ 2 / (2 * N)) * fz κ L z G * deriv (cauchyG N q) z) =
      exp (I * κ * G) * (exp (a + Rp) - (1 + a)) +
        exp (I * z * L) * exp (-(I * κ * G)) * (exp (a + Rm) - (1 + a)) := by
    rw [hS, hPp', hPm', hderiv, ha]
    simp only [fz]
    ring
  -- norm bounds
  have hIκG : ‖I * κ * G‖ ≤ x := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |κ| * ‖G‖ ≤ |κ| * η⁻¹ := mul_le_mul_of_nonneg_left hGb (abs_nonneg _)
      _ = x := by rw [hxdef, div_eq_mul_inv]
  have hEp : ‖exp (I * κ * G)‖ ≤ Real.exp x :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr hIκG)
  have hEm : ‖exp (-(I * κ * G))‖ ≤ Real.exp x :=
    (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (by rw [norm_neg]; exact hIκG))
  have hab : ‖a‖ ≤ x ^ 2 / (2 * N) := by
    have h1 : ‖-((κ : ℂ) ^ 2 / (2 * N))‖ = κ ^ 2 / (2 * N) := by
      rw [norm_neg, norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_natCast,
        Real.norm_eq_abs, sq_abs]
      norm_num
    have h2 : ‖-(N : ℂ)⁻¹ * S2‖ ≤ η⁻¹ ^ 2 := by rw [neg_mul, norm_neg]; exact hS2b
    calc ‖a‖ = κ ^ 2 / (2 * N) * ‖-(N : ℂ)⁻¹ * S2‖ := by rw [ha, norm_mul, h1]
      _ ≤ κ ^ 2 / (2 * N) * η⁻¹ ^ 2 := by gcongr
      _ = x ^ 2 / (2 * N) := by rw [hxdef, div_pow, sq_abs]; field_simp
  have hRb : ∀ R : ℂ, ‖R‖ ≤ N * (x / N) ^ 3 → ‖R‖ ≤ x ^ 3 / (N : ℝ) ^ 2 := by
    intro R hR
    refine hR.trans (le_of_eq ?_)
    field_simp
  have hx3 : x ^ 3 / (N : ℝ) ^ 2 ≤ x ^ 3 / N :=
    div_le_div_of_nonneg_left (by positivity) hNpos (by nlinarith)
  have hDN : D / N ≤ 1 := by rw [div_le_one hNpos]; linarith
  have hsign : ∀ R : ℂ, ‖R‖ ≤ N * (x / N) ^ 3 →
      ‖exp (a + R) - (1 + a)‖ ≤ (D ^ 2 + x ^ 3) / (N : ℝ) ^ 2 := by
    intro R hR
    have hR' := hRb R hR
    have haR : ‖a + R‖ ≤ D / N := by
      calc ‖a + R‖ ≤ ‖a‖ + ‖R‖ := norm_add_le _ _
        _ ≤ x ^ 2 / (2 * N) + x ^ 3 / N := by linarith
        _ = D / N := by rw [hD]; field_simp
    have haR2 : ‖a + R‖ ^ 2 ≤ (D / N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) haR 2
    calc ‖exp (a + R) - (1 + a)‖ ≤ ‖a + R‖ ^ 2 + ‖R‖ :=
          norm_exp_add_sub_le a R (haR.trans hDN)
      _ ≤ (D / N) ^ 2 + x ^ 3 / (N : ℝ) ^ 2 := by linarith
      _ = (D ^ 2 + x ^ 3) / (N : ℝ) ^ 2 := by field_simp
  have hp := hsign Rp hRp
  have hmb := hsign Rm hRm
  have hB : 0 ≤ (D ^ 2 + x ^ 3) / (N : ℝ) ^ 2 := by positivity
  rw [hid]
  calc ‖exp (I * κ * G) * (exp (a + Rp) - (1 + a)) +
        exp (I * z * L) * exp (-(I * κ * G)) * (exp (a + Rm) - (1 + a))‖
      ≤ ‖exp (I * κ * G)‖ * ‖exp (a + Rp) - (1 + a)‖ +
        ‖exp (I * z * L)‖ * ‖exp (-(I * κ * G))‖ * ‖exp (a + Rm) - (1 + a)‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, norm_mul, norm_mul]
    _ ≤ Real.exp x * ((D ^ 2 + x ^ 3) / (N : ℝ) ^ 2) +
        M * Real.exp x * ((D ^ 2 + x ^ 3) / (N : ℝ) ^ 2) := by
        gcongr
    _ = Real.exp x * (1 + M) * (D ^ 2 + x ^ 3) / (N : ℝ) ^ 2 := by ring


def sourceG (ε : ℝ) {N : ℕ} (q : Fin N → ℝ) (z : ℂ) : ℂ :=
  (ε * (N : ℝ) : ℂ) * cauchyG N q z

theorem transfer_second_order_separated
    {κ L M η ε B : ℝ} (hκ : 0 ≤ κ) (hM : 0 < M) (hη : 0 < η)
    (hsmall : κ * M / η ≤ 1 / 10) {N : ℕ} (hN : 0 < N)
    (hε : 0 ≤ ε)
    (hbudget : ε * (N : ℝ) ≤ M)
    (q : Fin N → ℝ) {z : ℂ} (hw : ∀ j, η ≤ ‖z - (q j : ℂ)‖)
    (hB : 0 ≤ B) (htransfer : ‖Complex.exp (Complex.I * z * L)‖ ≤ B) :
    ‖transferS (κ * ε) L q z -
        (QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) -
          (κ^2 * ε / 2 : ℝ) *
            QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) *
            deriv (sourceG ε q) z)‖ ≤
      Real.exp (1 / 10) * (1 + B) *
        ((κ / η)^4 * M^2 + (κ / η)^3 * M) * ε^2 := by
  let n : ℝ := (N : ℝ)
  let κN : ℝ := κ * ε * n
  let x : ℝ := |κN| / η
  let D : ℝ := x^2 / 2 + x^3
  have hnpos : 0 < n := by
    dsimp [n]
    exact_mod_cast hN
  have hnne : n ≠ 0 := ne_of_gt hnpos
  have hknonneg : 0 ≤ κN := by
    dsimp [κN]
    exact mul_nonneg (mul_nonneg hκ hε) (by positivity)
  have hxid : x = (κ / η) * ε * n := by
    dsimp [x, κN]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hκ hε) (by positivity))]
    dsimp [n]
    field_simp
  have hKnonneg : 0 ≤ κ / η := div_nonneg hκ hη.le
  have hxnonneg : 0 ≤ x := by dsimp [x]; positivity
  have hxle : x ≤ 1 / 10 := by
    rw [hxid]
    calc
      (κ / η) * ε * n ≤ (κ / η) * M := by
        calc
          (κ / η) * ε * n = (κ / η) * (ε * n) := by ring
          _ ≤ (κ / η) * M := mul_le_mul_of_nonneg_left hbudget hKnonneg
      _ = κ * M / η := by ring
      _ ≤ 1 / 10 := hsmall
  have hx2 : x^2 ≤ (1 / 10 : ℝ)^2 := by
    exact pow_le_pow_left₀ hxnonneg hxle 2
  have hx3 : x^3 ≤ (1 / 10 : ℝ)^3 := by
    exact pow_le_pow_left₀ hxnonneg hxle 3
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnsmall : 2 * x ≤ (N : ℝ) := by linarith
  have hnD : x^2 / 2 + x^3 ≤ (N : ℝ) := by
    norm_num at hx2 hx3
    linarith
  have hDnonneg : 0 ≤ D := by dsimp [D]; positivity
  have hDle : D ≤ x^2 := by
    dsimp [D]
    have haux : x^3 ≤ x^2 / 10 := by
      nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1 / 10 - x)]
    calc
      x^2 / 2 + x^3 ≤ x^2 / 2 + x^2 / 10 := add_le_add_right haux _
      _ ≤ x^2 := by nlinarith
  have hDsq : D^2 ≤ x^4 := by
    calc
      D^2 ≤ (x^2)^2 := pow_le_pow_left₀ hDnonneg hDle 2
      _ = x^4 := by ring
  have hNnat : N ≠ 0 := by omega
  have hNcast : (N : ℝ) ≠ 0 := by exact_mod_cast hNnat
  have hcoef : κN / (N : ℝ) = κ * ε := by
    dsimp [κN, n]
    field_simp [hNcast]
  have hz : ∀ j, z ≠ (q j : ℂ) := by
    intro j he
    have := hw j
    rw [he, sub_self, norm_zero] at this
    linarith
  have hsourceGderiv :
      deriv (sourceG ε q) z =
        (ε * (N : ℝ) : ℂ) * deriv (cauchyG N q) z := by
    exact deriv_const_mul _ (hasDerivAt_cauchyG_separated q hz).differentiableAt
  have harg : (κN : ℂ) * cauchyG N q z =
      (κ : ℂ) * sourceG ε q z := by
    dsimp [κN, n, sourceG]
    push_cast
    ring
  have hargI : Complex.I * (κN : ℂ) * cauchyG N q z =
      Complex.I * (κ : ℂ) * sourceG ε q z := by
    calc
      Complex.I * (κN : ℂ) * cauchyG N q z =
          Complex.I * ((κN : ℂ) * cauchyG N q z) := by ring
      _ = Complex.I * ((κ : ℂ) * sourceG ε q z) := by rw [harg]
      _ = Complex.I * (κ : ℂ) * sourceG ε q z := by ring
  have hmap : fz κN L z (cauchyG N q z) =
      QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) := by
    unfold fz QuantumNLS.Ext025A7.spectralMap
    rw [hargI]
    congr 2
    congr 1
    ring
  have hcorr :
      ((κN : ℂ)^2 / (2 * (N : ℂ))) *
          fz κN L z (cauchyG N q z) * deriv (cauchyG N q) z =
        (κ^2 * ε / 2 : ℝ) *
          QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) *
          deriv (sourceG ε q) z := by
    rw [hmap, hsourceGderiv]
    dsimp [κN, n]
    push_cast
    have hNc : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hNcast
    field_simp [hNc]
  have hpoint := pointwise_bound_separated κN L hη hB hn1 hnsmall hnD q hw htransfer
  have hmain :
      transferS (κN / (N : ℝ)) L q z -
          (fz κN L z (cauchyG N q z) -
            (κN^2 / (2 * (N : ℝ))) *
              fz κN L z (cauchyG N q z) * deriv (cauchyG N q) z) =
        transferS (κ * ε) L q z -
          (QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) -
            (κ^2 * ε / 2 : ℝ) *
              QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) *
              deriv (sourceG ε q) z) := by
    simp only [Complex.ofReal_natCast] at hcorr ⊢
    rw [hcoef, hcorr, hmap]
  have hpoint' :
      ‖transferS (κ * ε) L q z -
        (QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) -
          (κ^2 * ε / 2 : ℝ) *
            QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) *
            deriv (sourceG ε q) z)‖ ≤
        Real.exp (|κN| / η) * (1 + B) *
          (((|κN| / η)^2 / 2 + (|κN| / η)^3)^2 +
            (|κN| / η)^3) / (N : ℝ)^2 := by
    rw [← hmain]
    exact hpoint
  have hexp : Real.exp x ≤ Real.exp (1 / 10) :=
    Real.exp_le_exp.mpr hxle
  have hratio4 : x^4 / n^2 =
      (κ / η)^4 * ε^2 * (ε * n)^2 := by
    rw [hxid]
    field_simp [hnne]
  have hratio3 : x^3 / n^2 =
      (κ / η)^3 * ε^2 * (ε * n) := by
    rw [hxid]
    field_simp [hnne]
  have hratio4le : x^4 / n^2 ≤ (κ / η)^4 * M^2 * ε^2 := by
    rw [hratio4]
    have hsq : (ε * n)^2 ≤ M^2 := by
      have hu : 0 ≤ ε * n := mul_nonneg hε (by positivity)
      have hMminus : 0 ≤ M - ε * n := by dsimp [n]; linarith
      nlinarith [mul_nonneg hMminus (by positivity : 0 ≤ M + ε * n)]
    have hnonneg : 0 ≤ (κ / η)^4 * ε^2 := by positivity
    calc
      (κ / η)^4 * ε^2 * (ε * n)^2 ≤
          (κ / η)^4 * ε^2 * M^2 := mul_le_mul_of_nonneg_left hsq hnonneg
      _ = (κ / η)^4 * M^2 * ε^2 := by ring
  have hratio3le : x^3 / n^2 ≤ (κ / η)^3 * M * ε^2 := by
    rw [hratio3]
    have hnonneg : 0 ≤ (κ / η)^3 * ε^2 := by positivity
    calc
      (κ / η)^3 * ε^2 * (ε * n) ≤
          (κ / η)^3 * ε^2 * M := mul_le_mul_of_nonneg_left hbudget hnonneg
      _ = (κ / η)^3 * M * ε^2 := by ring
  have hfrac : (D^2 + x^3) / n^2 ≤
      ((κ / η)^4 * M^2 + (κ / η)^3 * M) * ε^2 := by
    calc
      (D^2 + x^3) / n^2 ≤ (x^4 + x^3) / n^2 :=
        div_le_div_of_nonneg_right (add_le_add hDsq le_rfl) (sq_nonneg n)
      _ = x^4 / n^2 + x^3 / n^2 := by rw [add_div]
      _ ≤ (κ / η)^4 * M^2 * ε^2 + (κ / η)^3 * M * ε^2 :=
        add_le_add hratio4le hratio3le
      _ = ((κ / η)^4 * M^2 + (κ / η)^3 * M) * ε^2 := by ring
  have hfacnonneg : 0 ≤ (1 + B) := by linarith
  have hcoeffnonneg :
      0 ≤ ((κ / η)^4 * M^2 + (κ / η)^3 * M) * ε^2 := by positivity
  have hbound := hpoint'
  have hN2pos : 0 < n^2 := by positivity
  have hnum : 0 ≤ D^2 + x^3 := by positivity
  have hpoint_bound :
      ‖transferS (κ * ε) L q z -
        (QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) -
          (κ^2 * ε / 2 : ℝ) *
            QuantumNLS.Ext025A7.spectralMap κ L z (sourceG ε q z) *
            deriv (sourceG ε q) z)‖ ≤
        Real.exp (1 / 10) * (1 + B) *
          ((D^2 + x^3) / n^2) := by
    calc
      _ ≤ Real.exp x * (1 + B) * (D^2 + x^3) / n^2 := by
        simpa [n, x, D] using hbound
      _ = Real.exp x * (1 + B) * ((D^2 + x^3) / n^2) := by ring
      _ ≤ Real.exp (1 / 10) * (1 + B) * ((D^2 + x^3) / n^2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hexp hfacnonneg)
          (div_nonneg hnum (sq_nonneg n))
      _ = _ := by ring
  calc
    _ ≤ Real.exp (1 / 10) * (1 + B) * ((D^2 + x^3) / n^2) := hpoint_bound
    _ ≤ Real.exp (1 / 10) * (1 + B) *
          (((κ / η)^4 * M^2 + (κ / η)^3 * M) * ε^2) := by
        exact mul_le_mul_of_nonneg_left hfrac
          (mul_nonneg (Real.exp_pos _).le hfacnonneg)
    _ = Real.exp (1 / 10) * (1 + B) *
          ((κ / η)^4 * M^2 + (κ / η)^3 * M) * ε^2 := by ring


end QuantumNLS.LOCAL009R22Transfer
#print axioms QuantumNLS.LOCAL009R22Transfer.hasDerivAt_cauchyG_separated
#print axioms QuantumNLS.LOCAL009R22Transfer.pointwise_bound_separated
#print axioms QuantumNLS.LOCAL009R22Transfer.transfer_second_order_separated
