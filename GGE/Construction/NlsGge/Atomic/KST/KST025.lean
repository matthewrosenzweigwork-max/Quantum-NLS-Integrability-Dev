import Mathlib
import NlsGge.Atomic.KSTPath
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST023
import NlsGge.Atomic.KST.KST024

                                                                                                                                                                                                                                                                    
                                                                                                                                                                                                
                                                                                                                                                 

set_option autoImplicit false
open scoped ENNReal BigOperators
open NlsGge.Atomic.KSTPath NlsGge.Atomic.KST

namespace NlsGge.ThirdConsultation.KST

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The source B^σ_{2k,n}(A) from KST (54): the sum of squares of all
2k+1 Fourier factors over the pattern-restricted path set. -/
def sourcePatternFourierEnergy {k : ℕ} (hk : 0 < k) (A : ℤ → ℝ)
    (n : ℤ) (σ : Pattern k) : ℝ≥0∞ :=
  ∑' ell : Path k, if admissiblePath n ell ∧
    (∀ i, nearFarBit n (ell i) = σ i) then
    ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ell j)^2) else 0

/-- The literal quantity in KST equation (55):
Σ_{|n|≥N} w(2n)^2 A^σ_{2k,n} B^σ_{2k,n}(A). -/
def weightedCauchyPatternSum {k : ℕ} (hk : 0 < k) (w A : ℤ → ℝ)
    (N : ℕ) (σ : Pattern k) : ℝ≥0∞ :=
  ∑' n : ℤ, if N ≤ n.natAbs then
    ENNReal.ofReal (w (2*n)^2) * denominatorPattern n σ *
      sourcePatternFourierEnergy hk A n σ else 0

namespace K025Aux

/-- Injectivity of the path-argument map (KST (55) bookkeeping). -/
theorem pathArg_injective {k : ℕ} (hk : 0 < k) :
    Function.Injective (fun p : ℤ × Path k => fun j : Fin (2*k+1) => pathArgument hk p.1 p.2 j) := by
  rintro ⟨n, ℓ⟩ ⟨n', ℓ'⟩ h
  have h' : ∀ j : Fin (2*k+1), pathArgument hk n ℓ j = pathArgument hk n' ℓ' j :=
    fun j => congrFun h j
  set e := n - n' with he
  have h0 : n + ℓ ⟨0, by omega⟩ = n' + ℓ' ⟨0, by omega⟩ := by
    have := h' ⟨0, by omega⟩
    rw [pathArgument_zero hk n ℓ, pathArgument_zero hk n' ℓ'] at this
    exact this
  have hint : ∀ i (hi : i + 1 < 2*k), ℓ ⟨i, by omega⟩ + ℓ ⟨i+1, hi⟩ =
      ℓ' ⟨i, by omega⟩ + ℓ' ⟨i+1, hi⟩ := by
    intro i hi
    have hj : i + 1 < 2*k+1 := by omega
    have := h' ⟨i+1, hj⟩
    rw [pathArgument_interior hk n ℓ ⟨i+1, hj⟩ (by simp) hi,
      pathArgument_interior hk n' ℓ' ⟨i+1, hj⟩ (by simp) hi] at this
    simpa using this
  have key : ∀ i : ℕ, ∀ hi : i < 2*k, ℓ ⟨i, hi⟩ - ℓ' ⟨i, hi⟩ = -((-1 : ℤ)^i) * e := by
    intro i
    induction i with
    | zero =>
      intro hi
      simp only [he, pow_zero]
      linarith [h0]
    | succ i ih =>
      intro hi
      have hi' : i < 2*k := by omega
      have hstep := hint i hi
      have hprev := ih hi'
      have hrel : ℓ ⟨i+1, hi⟩ - ℓ' ⟨i+1, hi⟩ = -(ℓ ⟨i, hi'⟩ - ℓ' ⟨i, hi'⟩) := by
        linarith [hstep]
      rw [hrel, hprev]
      ring
  have hlastEq : ℓ ⟨2*k-1, by omega⟩ + n = ℓ' ⟨2*k-1, by omega⟩ + n' := by
    have := h' ⟨2*k, by omega⟩
    rw [pathArgument_last hk n ℓ, pathArgument_last hk n' ℓ'] at this
    exact this
  have hodd : (-1 : ℤ) ^ (2*k-1) = -1 := Odd.neg_one_pow ⟨k-1, by omega⟩
  have hk1 := key (2*k-1) (by omega)
  rw [hodd] at hk1
  have he0 : e = 0 := by linarith [hk1, hlastEq]
  have hnn : n = n' := by linarith [he, he0]
  have hℓ : ℓ = ℓ' := by
    funext i
    have := key i.val i.isLt
    rw [he0, mul_zero] at this
    have h2 : ℓ ⟨i.val, i.isLt⟩ = ℓ' ⟨i.val, i.isLt⟩ := by linarith [this]
    simpa using h2
  rw [hnn, hℓ]

end K025Aux

/-- KST-025 (Pro statement, verbatim except parse-neutral layout). -/
theorem kst025 (w A : ℤ → ℝ) (Cw : ℝ)
    (hw : SlowWeight w Cw) (hA : ∀ j, 0 ≤ A j)
    (hE : scalarEnergy w A < ⊤) (N k : ℕ) (hN : 1 ≤ N)
    (hk : 0 < k) (σ : Pattern k) (hτ : forcedTailCount hk σ = 0) :
  Function.Injective (fun p : ℤ × Path k =>
    fun j : Fin (2*k+1) => pathArgument hk p.1 p.2 j) ∧
  weightedCauchyPatternSum hk w A N σ < ⊤ ∧
  weightedCauchyPatternSum hk w A N σ ≤ ENNReal.ofReal
    ((5*Cw^2)^(2*k) *
      ((scalarEnergy w A).toReal / Real.sqrt (N : ℝ))^(2*k+1)) := by
  have hCw : 1 ≤ Cw := slowWeight_Cw_one_le hw
  have hC0 : 0 ≤ Cw := le_trans zero_le_one hCw
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (5:ℝ)^(2*k) / (N:ℝ)^(patternOnes σ) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  -- tau = 0 forces at least k+1 far bits
  have ht : k + 1 ≤ patternOnes σ := by
    have hid := forcedTailCount_identity hk σ
    rw [hτ] at hid
    omega
  -- per-n bound (uses the far-count denominator bound KST-023 and the path-product bound KST-022)
  have hterm : ∀ n : ℤ, N ≤ n.natAbs →
      ENNReal.ofReal (w (2*n)^2) * denominatorPattern n σ *
          sourcePatternFourierEnergy hk A n σ ≤
        ENNReal.ofReal (Cw^(4*k)) * ENNReal.ofReal c *
          ∑' ℓ : Path k, (if admissiblePath n ℓ ∧ (∀ i, nearFarBit n (ℓ i) = σ i) then
            ENNReal.ofReal (∏ j : Fin (2*k+1),
              w (pathArgument hk n ℓ j)^2 * A (pathArgument hk n ℓ j)^2)
            else 0) := by
    intro n hn
    have hnpos : 1 ≤ n.natAbs := le_trans hN hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hnpos
    have hNn : (N:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hn
    have hD : denominatorPattern n σ ≤ ENNReal.ofReal c := by
      refine le_trans (kst023 k (by omega) n hn0 σ).2 (ENNReal.ofReal_le_ofReal ?_)
      rw [hc]
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hNpos _)
        (pow_le_pow_left₀ hNpos.le hNn _)
    unfold sourcePatternFourierEnergy
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ℓ => ?_
    by_cases hp : admissiblePath n ℓ ∧ (∀ i, nearFarBit n (ℓ i) = σ i)
    · rw [if_pos hp, if_pos hp]
      have h2 := slowWeight_path_product_le hw hk n ℓ
      have hnn : 0 ≤ w (2*n) := le_trans zero_le_one (hw.one_le _)
      have h3 : w (2*n)^2 ≤ (Cw^(2*k) * ∏ j, w (pathArgument hk n ℓ j))^2 :=
        pow_le_pow_left₀ hnn h2 2
      have h4 : (Cw^(2*k) * ∏ j, w (pathArgument hk n ℓ j))^2 =
          Cw^(4*k) * ∏ j, w (pathArgument hk n ℓ j)^2 := by
        rw [mul_pow, ← Finset.prod_pow]; ring
      have hsq : w (2*n)^2 ≤ Cw^(4*k) * ∏ j, w (pathArgument hk n ℓ j)^2 :=
        h3.trans (le_of_eq h4)
      have hP : 0 ≤ ∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j)^2 :=
        Finset.prod_nonneg fun j _ => sq_nonneg _
      have hQ : ∏ j : Fin (2*k+1), (w (pathArgument hk n ℓ j)^2 * A (pathArgument hk n ℓ j)^2) =
          (∏ j : Fin (2*k+1), w (pathArgument hk n ℓ j)^2) *
            ∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j)^2 :=
        Finset.prod_mul_distrib
      have hreal : w (2*n)^2 * c * (∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j)^2) ≤
          Cw^(4*k) * c * ∏ j : Fin (2*k+1),
            (w (pathArgument hk n ℓ j)^2 * A (pathArgument hk n ℓ j)^2) := by
        rw [hQ]
        calc w (2*n)^2 * c * (∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j)^2)
            ≤ (Cw^(4*k) * ∏ j : Fin (2*k+1), w (pathArgument hk n ℓ j)^2) * c *
                (∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j)^2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hc0) hP
          _ = Cw^(4*k) * c * ((∏ j : Fin (2*k+1), w (pathArgument hk n ℓ j)^2) *
                (∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j)^2)) := by ring
      calc ENNReal.ofReal (w (2*n)^2) * denominatorPattern n σ *
            ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j)^2)
          ≤ ENNReal.ofReal (w (2*n)^2) * ENNReal.ofReal c *
            ENNReal.ofReal (∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j)^2) := by
            gcongr
        _ = ENNReal.ofReal (w (2*n)^2 * c * (∏ j : Fin (2*k+1), A (pathArgument hk n ℓ j)^2)) := by
            rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hc0), ENNReal.ofReal_mul (sq_nonneg _)]
        _ ≤ ENNReal.ofReal (Cw^(4*k) * c *
              ∏ j : Fin (2*k+1), (w (pathArgument hk n ℓ j)^2 * A (pathArgument hk n ℓ j)^2)) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (Cw^(4*k)) * ENNReal.ofReal c *
              ENNReal.ofReal (∏ j : Fin (2*k+1),
                (w (pathArgument hk n ℓ j)^2 * A (pathArgument hk n ℓ j)^2)) := by
            rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hC0 _) hc0),
              ENNReal.ofReal_mul (pow_nonneg hC0 _)]
    · rw [if_neg hp, if_neg hp]
      simp
  -- summing over all (n, ℓ): injectivity of the path-argument map and the product of ℓ¹ sums
  have hsumall : ∑' n : ℤ, ∑' ℓ : Path k, (if admissiblePath n ℓ ∧
        (∀ i, nearFarBit n (ℓ i) = σ i) then
          ENNReal.ofReal (∏ j : Fin (2*k+1),
            w (pathArgument hk n ℓ j)^2 * A (pathArgument hk n ℓ j)^2)
        else 0) ≤ scalarEnergy w A ^ (2*k+1) := by
    rw [← ENNReal.tsum_prod]
    calc ∑' p : ℤ × Path k, (if admissiblePath p.1 p.2 ∧
            (∀ i, nearFarBit p.1 (p.2 i) = σ i) then
          ENNReal.ofReal (∏ j : Fin (2*k+1),
            w (pathArgument hk p.1 p.2 j)^2 * A (pathArgument hk p.1 p.2 j)^2)
          else 0)
        ≤ ∑' p : ℤ × Path k, ENNReal.ofReal (∏ j : Fin (2*k+1),
            w (pathArgument hk p.1 p.2 j)^2 * A (pathArgument hk p.1 p.2 j)^2) :=
          ENNReal.tsum_le_tsum fun p => by split_ifs <;> simp
      _ ≤ ∑' a : Fin (2*k+1) → ℤ, ENNReal.ofReal (∏ j : Fin (2*k+1),
            w (a j)^2 * A (a j)^2) :=
          ENNReal.tsum_comp_le_tsum_of_injective (K025Aux.pathArg_injective hk)
            (fun a : Fin (2*k+1) → ℤ => ENNReal.ofReal (∏ j : Fin (2*k+1),
              w (a j)^2 * A (a j)^2))
      _ = ∑' a : Fin (2*k+1) → ℤ, ∏ j : Fin (2*k+1), ENNReal.ofReal (w (a j)^2 * A (a j)^2) := by
          refine tsum_congr fun a => ?_
          rw [ENNReal.ofReal_prod_of_nonneg fun j _ => by positivity]
      _ = ∏ j : Fin (2*k+1), ∑' z : ℤ, ENNReal.ofReal (w z^2 * A z^2) :=
          tsum_pi_fin_prod (2*k+1) (fun _ z => ENNReal.ofReal (w z^2 * A z^2))
      _ = scalarEnergy w A ^ (2*k+1) := by
          unfold scalarEnergy
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hmain : weightedCauchyPatternSum hk w A N σ ≤
      ENNReal.ofReal (Cw^(4*k)) * ENNReal.ofReal c * scalarEnergy w A ^ (2*k+1) := by
    unfold weightedCauchyPatternSum
    calc ∑' n : ℤ, (if N ≤ n.natAbs then ENNReal.ofReal (w (2*n)^2) * denominatorPattern n σ *
            sourcePatternFourierEnergy hk A n σ else 0)
        ≤ ∑' n : ℤ, ENNReal.ofReal (Cw^(4*k)) * ENNReal.ofReal c *
            ∑' ℓ : Path k, (if admissiblePath n ℓ ∧ (∀ i, nearFarBit n (ℓ i) = σ i) then
              ENNReal.ofReal (∏ j : Fin (2*k+1),
                w (pathArgument hk n ℓ j)^2 * A (pathArgument hk n ℓ j)^2)
              else 0) :=
          ENNReal.tsum_le_tsum fun n => by
            by_cases hn : N ≤ n.natAbs
            · rw [if_pos hn]; exact hterm n hn
            · rw [if_neg hn]; exact zero_le
      _ = ENNReal.ofReal (Cw^(4*k)) * ENNReal.ofReal c *
            ∑' n : ℤ, ∑' ℓ : Path k, (if admissiblePath n ℓ ∧
              (∀ i, nearFarBit n (ℓ i) = σ i) then
                ENNReal.ofReal (∏ j : Fin (2*k+1),
                  w (pathArgument hk n ℓ j)^2 * A (pathArgument hk n ℓ j)^2)
              else 0) := ENNReal.tsum_mul_left
      _ ≤ _ := by gcongr
  -- finish: real-number comparison
  have hEfin : scalarEnergy w A = ENNReal.ofReal (scalarEnergy w A).toReal :=
    (ENNReal.ofReal_toReal hE.ne).symm
  set X := (scalarEnergy w A).toReal with hX
  have hX0 : 0 ≤ X := ENNReal.toReal_nonneg
  have hs2 : Real.sqrt (N:ℝ) * Real.sqrt (N:ℝ) = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  have hs0 : 0 ≤ Real.sqrt (N:ℝ) := Real.sqrt_nonneg _
  have hs1 : 1 ≤ Real.sqrt (N:ℝ) := by nlinarith
  have hspos : 0 < Real.sqrt (N:ℝ) ^ (2*k+1) := pow_pos (by linarith) _
  have hsN : Real.sqrt (N:ℝ) ^ (2*k+1) ≤ (N:ℝ) ^ (patternOnes σ) := by
    have e1 : Real.sqrt (N:ℝ) ^ (2*k+1) ≤ Real.sqrt (N:ℝ) ^ (2*k+2) :=
      pow_le_pow_right₀ hs1 (by omega)
    have e2 : Real.sqrt (N:ℝ) ^ (2*k+2) = (N:ℝ) ^ (k+1) := by
      rw [show 2*k+2 = 2*(k+1) by ring, pow_mul, Real.sq_sqrt (Nat.cast_nonneg N)]
    have e3 : (N:ℝ) ^ (k+1) ≤ (N:ℝ) ^ (patternOnes σ) := pow_le_pow_right₀ hN1 ht
    exact le_trans e1 (le_trans e2.le e3)
  have hcomp : Cw^(4*k) * c = (5*Cw^2)^(2*k) / (N:ℝ) ^ (patternOnes σ) := by
    rw [hc]; ring
  have hreal : Cw^(4*k) * c * X^(2*k+1) ≤
      (5*Cw^2)^(2*k) * (X / Real.sqrt (N:ℝ))^(2*k+1) := by
    calc Cw^(4*k) * c * X^(2*k+1)
        = (5*Cw^2)^(2*k) * (X^(2*k+1) / (N:ℝ) ^ (patternOnes σ)) := by
          rw [hcomp]; ring
      _ ≤ (5*Cw^2)^(2*k) * (X^(2*k+1) / Real.sqrt (N:ℝ) ^ (2*k+1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_left (pow_nonneg hX0 _) hspos hsN
      _ = (5*Cw^2)^(2*k) * (X / Real.sqrt (N:ℝ))^(2*k+1) := by rw [div_pow]
  have hpw : ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
      ENNReal.ofReal x * ENNReal.ofReal y * ENNReal.ofReal z = ENNReal.ofReal (x*y*z) := by
    intro x y z hx hy hz
    rw [ENNReal.ofReal_mul (mul_nonneg hx hy), ENNReal.ofReal_mul hx]
  have hle : weightedCauchyPatternSum hk w A N σ ≤
      ENNReal.ofReal ((5*Cw^2)^(2*k) * (X / Real.sqrt (N:ℝ))^(2*k+1)) := by
    refine hmain.trans ?_
    rw [hEfin, ← ENNReal.ofReal_pow hX0,
      hpw _ _ _ (pow_nonneg hC0 (4*k)) hc0 (pow_nonneg hX0 (2*k+1))]
    exact ENNReal.ofReal_le_ofReal hreal
  exact ⟨K025Aux.pathArg_injective hk, lt_of_le_of_lt hle ENNReal.ofReal_lt_top, hle⟩

end



end NlsGge.ThirdConsultation.KST
