import Mathlib
import NlsGge.Atomic.G1.G1034
import NlsGge.ThirdConsultation.G1.Wkb035A

                                                                                              
                                                                                                
                                                                                               
                                                                
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
open NlsGge.Pilot NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.NLS38

namespace NlsGge.GKDefinitionDesign
attribute [local instance] Classical.propDecidable

theorem g35_psn_zero (u : PhysicalL2) : physicalSobolevNorm ((0 : ℕ) : ℝ) u = ‖u‖ := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ENNReal)) (by norm_num) (reflectedFourierL2 u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [← reflectedFourierL2.norm_map u, ← Real.sqrt_sq (norm_nonneg (reflectedFourierL2 u)), h]
  unfold physicalSobolevNorm
  congr 1
  refine tsum_congr (fun n => ?_)
  simp

theorem g35_H1_wkbR (M : ℕ) (hN : 1 ≤ M + 1) (φ : PotPair) (hφ : pairSobolev ((M + 1 : ℕ) : ℝ) φ)
    (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ M + 1) : physicalSobolev 1 (wkbR φ k) := by
  obtain ⟨_, _, _, h⟩ := wkb_bound (M + 1) (M + 1) hN le_rfl
  obtain ⟨h1, _⟩ := h φ hφ k hk1 hk2
  exact g35_H1_nat _ (psn_mono (show 1 ≤ M + 1 + 1 - k by omega) h1).1

theorem g35_tail_norm (M : ℕ) (C0 Cm X : ℝ) (p0 : ℕ) (hC0 : 0 ≤ C0) (hCm : 0 ≤ Cm) (hX : 0 ≤ X)
    (φ : PotPair)
    (hprod : ∀ u v : PhysicalL2, physicalSobolev ((1 : ℕ) : ℝ) u → physicalSobolev ((1 : ℕ) : ℝ) v →
      physicalSobolev ((1 : ℕ) : ℝ) (physicalProduct u v) ∧
        physicalSobolevNorm ((1 : ℕ) : ℝ) (physicalProduct u v) ≤
          Cm * physicalSobolevNorm ((1 : ℕ) : ℝ) u * physicalSobolevNorm ((1 : ℕ) : ℝ) v)
    (hφ1 : physicalSobolev ((1 : ℕ) : ℝ) φ.1)
    (hφX : physicalSobolevNorm ((1 : ℕ) : ℝ) φ.1 ≤ X)
    (hH : ∀ k, 1 ≤ k → k ≤ M + 1 → physicalSobolev ((1 : ℕ) : ℝ) (wkbR φ k))
    (hB : ∀ k, 1 ≤ k → k ≤ M + 1 →
      physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ k) ≤ C0 * (1 + X) ^ p0)
    (l : ℂ) (hl : 1 ≤ ‖l‖) :
    ‖wkbResidualTail (M + 1) l φ‖ ≤
      (2 * Real.pi * C0 + ((M + 1 : ℕ) : ℝ) ^ 2 * (Cm ^ 2 * C0 ^ 2)) *
        (1 + X) ^ (p0 + (2 * p0 + 1)) / ‖l‖ ^ (M + 1) := by
  unfold wkbResidualTail
  have hYnn : 0 ≤ 1 + X := by linarith
  have hY1 : 1 ≤ 1 + X := by linarith
  have ha : 0 < ‖l‖ := by linarith
  have hZnn : 0 ≤ (‖l‖ ^ (M + 1))⁻¹ := by positivity
  have hnorm2 : ‖(2 * Complex.I * l : ℂ)‖ = 2 * ‖l‖ := by
    simp [norm_mul]
  have hE : ∀ k, M + 1 ≤ k → ‖((2 * Complex.I * l) ^ k)⁻¹‖ ≤ (‖l‖ ^ (M + 1))⁻¹ := by
    intro k hk
    rw [norm_inv, norm_pow, hnorm2]
    exact inv_anti₀ (pow_pos ha _)
      ((pow_le_pow_left₀ ha.le (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hk))
  have hD : ‖weakDerivative (wkbR φ (M + 1))‖ ≤ 2 * Real.pi * (C0 * (1 + X) ^ p0) := by
    have h1 := (psn_deriv 0 (hH (M + 1) (by omega) le_rfl)).2
    rw [g35_psn_zero] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hB (M + 1) (by omega) le_rfl) (by positivity))
  have hQ : ∀ k j, 1 ≤ k → k ≤ M + 1 → 1 ≤ j → j ≤ M + 1 →
      ‖physicalProduct φ.1 (physicalProduct (wkbR φ k) (wkbR φ j))‖ ≤
        Cm ^ 2 * C0 ^ 2 * (1 + X) ^ (2 * p0 + 1) := by
    intro k j hk1 hk2 hj1 hj2
    obtain ⟨hPk, hPkn⟩ := hprod _ _ (hH k hk1 hk2) (hH j hj1 hj2)
    obtain ⟨hQH, hQn⟩ := hprod _ _ hφ1 hPk
    have hpk := hB k hk1 hk2
    have hpj := hB j hj1 hj2
    have hn0 : 0 ≤ physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ k) := psn_nonneg 1 _
    have hn1 : 0 ≤ physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ j) := psn_nonneg 1 _
    have hn2 : 0 ≤ physicalSobolevNorm ((1 : ℕ) : ℝ) φ.1 := psn_nonneg 1 _
    have hBnn : 0 ≤ C0 * (1 + X) ^ p0 := mul_nonneg hC0 (pow_nonneg hYnn _)
    have hPn : physicalSobolevNorm ((1 : ℕ) : ℝ) (physicalProduct (wkbR φ k) (wkbR φ j)) ≤
        Cm * (C0 * (1 + X) ^ p0) * (C0 * (1 + X) ^ p0) := by
      refine hPkn.trans ?_
      have hkj : physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ k) *
          physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ j) ≤
          (C0 * (1 + X) ^ p0) * (C0 * (1 + X) ^ p0) :=
        mul_le_mul hpk hpj hn1 hBnn
      calc Cm * physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ k) *
            physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ j)
          = Cm * (physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ k) *
              physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ j)) := by ring
        _ ≤ Cm * ((C0 * (1 + X) ^ p0) * (C0 * (1 + X) ^ p0)) :=
          mul_le_mul_of_nonneg_left hkj hCm
        _ = Cm * (C0 * (1 + X) ^ p0) * (C0 * (1 + X) ^ p0) := by ring
    have hQn' : physicalSobolevNorm ((1 : ℕ) : ℝ)
        (physicalProduct φ.1 (physicalProduct (wkbR φ k) (wkbR φ j))) ≤
        Cm ^ 2 * C0 ^ 2 * (1 + X) ^ (2 * p0 + 1) := by
      refine hQn.trans ?_
      have hf : Cm * physicalSobolevNorm ((1 : ℕ) : ℝ) φ.1 ≤ Cm * (1 + X) :=
        mul_le_mul_of_nonneg_left (hφX.trans (by linarith)) hCm
      have h1 : Cm * physicalSobolevNorm ((1 : ℕ) : ℝ) φ.1 *
          physicalSobolevNorm ((1 : ℕ) : ℝ) (physicalProduct (wkbR φ k) (wkbR φ j)) ≤
          Cm * (1 + X) * (Cm * (C0 * (1 + X) ^ p0) * (C0 * (1 + X) ^ p0)) :=
        mul_le_mul hf hPn (psn_nonneg _ _) (mul_nonneg hCm (by linarith))
      refine h1.trans (le_of_eq ?_)
      ring
    have h0 : ‖physicalProduct φ.1 (physicalProduct (wkbR φ k) (wkbR φ j))‖ ≤
        physicalSobolevNorm ((1 : ℕ) : ℝ) (physicalProduct φ.1 (physicalProduct (wkbR φ k) (wkbR φ j))) :=
      (g35_psn_zero _).ge.trans (psn_mono (Nat.zero_le 1) hQH).2
    exact h0.trans hQn'
  have hterm : ∀ n ∈ Finset.Icc 1 (M + 1), ∀ j ∈ Finset.Icc 1 (M + 1),
      ‖(if M + 1 ≤ n + j then ((2 * Complex.I * l) ^ (n + j))⁻¹ •
        physicalProduct φ.1 (physicalProduct (wkbR φ n) (wkbR φ j)) else 0)‖ ≤
        (‖l‖ ^ (M + 1))⁻¹ * (Cm ^ 2 * C0 ^ 2 * (1 + X) ^ (2 * p0 + 1)) := by
    intro n hn j hj
    rw [Finset.mem_Icc] at hn hj
    split_ifs with hc
    · rw [norm_smul]
      exact mul_le_mul (hE _ hc) (hQ n j hn.1 hn.2 hj.1 hj.2) (norm_nonneg _) hZnn
    · rw [norm_zero]
      exact mul_nonneg hZnn (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (pow_nonneg hYnn _))
  have hsum : ‖∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
      (if M + 1 ≤ n + j then ((2 * Complex.I * l) ^ (n + j))⁻¹ •
        physicalProduct φ.1 (physicalProduct (wkbR φ n) (wkbR φ j)) else 0)‖ ≤
      ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) *
        ((‖l‖ ^ (M + 1))⁻¹ * (Cm ^ 2 * C0 ^ 2 * (1 + X) ^ (2 * p0 + 1))) := by
    calc _ ≤ ∑ n ∈ Finset.Icc 1 (M + 1), ‖∑ j ∈ Finset.Icc 1 (M + 1),
          (if M + 1 ≤ n + j then ((2 * Complex.I * l) ^ (n + j))⁻¹ •
            physicalProduct φ.1 (physicalProduct (wkbR φ n) (wkbR φ j)) else 0)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
          ‖(if M + 1 ≤ n + j then ((2 * Complex.I * l) ^ (n + j))⁻¹ •
            physicalProduct φ.1 (physicalProduct (wkbR φ n) (wkbR φ j)) else 0)‖ :=
          Finset.sum_le_sum (fun n _ => norm_sum_le _ _)
      _ ≤ ∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
          (‖l‖ ^ (M + 1))⁻¹ * (Cm ^ 2 * C0 ^ 2 * (1 + X) ^ (2 * p0 + 1)) :=
          Finset.sum_le_sum (fun n hn => Finset.sum_le_sum (fun j hj => hterm n hn j hj))
      _ = ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) *
          ((‖l‖ ^ (M + 1))⁻¹ * (Cm ^ 2 * C0 ^ 2 * (1 + X) ^ (2 * p0 + 1))) := by
          simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          push_cast
          ring
  have hfirst : ‖((2 * Complex.I * l) ^ (M + 1))⁻¹ • weakDerivative (wkbR φ (M + 1))‖ ≤
      (‖l‖ ^ (M + 1))⁻¹ * (2 * Real.pi * (C0 * (1 + X) ^ p0)) := by
    rw [norm_smul]
    exact mul_le_mul (hE (M + 1) le_rfl) hD (norm_nonneg _) hZnn
  have hP1 : (1 + X) ^ p0 ≤ (1 + X) ^ (p0 + (2 * p0 + 1)) :=
    pow_le_pow_right₀ hY1 (by omega)
  have hP2 : (1 + X) ^ (2 * p0 + 1) ≤ (1 + X) ^ (p0 + (2 * p0 + 1)) :=
    pow_le_pow_right₀ hY1 (by omega)
  have hZ2 : 0 ≤ (‖l‖ ^ (M + 1))⁻¹ * (2 * Real.pi * C0) :=
    mul_nonneg hZnn (mul_nonneg (by positivity) hC0)
  have hZ3 : 0 ≤ ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) * ((‖l‖ ^ (M + 1))⁻¹ * (Cm ^ 2 * C0 ^ 2)) :=
    mul_nonneg (by positivity) (mul_nonneg hZnn (by positivity))
  have hfin : (‖l‖ ^ (M + 1))⁻¹ * (2 * Real.pi * (C0 * (1 + X) ^ p0)) +
      ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) *
        ((‖l‖ ^ (M + 1))⁻¹ * (Cm ^ 2 * C0 ^ 2 * (1 + X) ^ (2 * p0 + 1))) ≤
      ((2 * Real.pi * C0 + ((M + 1 : ℕ) : ℝ) ^ 2 * (Cm ^ 2 * C0 ^ 2)) *
        (1 + X) ^ (p0 + (2 * p0 + 1))) * (‖l‖ ^ (M + 1))⁻¹ := by
    calc (‖l‖ ^ (M + 1))⁻¹ * (2 * Real.pi * (C0 * (1 + X) ^ p0)) +
        ((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) *
          ((‖l‖ ^ (M + 1))⁻¹ * (Cm ^ 2 * C0 ^ 2 * (1 + X) ^ (2 * p0 + 1)))
        = ((‖l‖ ^ (M + 1))⁻¹ * (2 * Real.pi * C0)) * (1 + X) ^ p0 +
          (((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) *
            ((‖l‖ ^ (M + 1))⁻¹ * (Cm ^ 2 * C0 ^ 2))) * (1 + X) ^ (2 * p0 + 1) := by ring
      _ ≤ ((‖l‖ ^ (M + 1))⁻¹ * (2 * Real.pi * C0)) * (1 + X) ^ (p0 + (2 * p0 + 1)) +
          (((M + 1 : ℕ) : ℝ) * ((M + 1 : ℕ) : ℝ) *
            ((‖l‖ ^ (M + 1))⁻¹ * (Cm ^ 2 * C0 ^ 2))) * (1 + X) ^ (p0 + (2 * p0 + 1)) :=
          add_le_add (mul_le_mul_of_nonneg_left hP1 hZ2) (mul_le_mul_of_nonneg_left hP2 hZ3)
      _ = ((2 * Real.pi * C0 + ((M + 1 : ℕ) : ℝ) ^ 2 * (Cm ^ 2 * C0 ^ 2)) *
          (1 + X) ^ (p0 + (2 * p0 + 1))) * (‖l‖ ^ (M + 1))⁻¹ := by ring
  have htri := norm_add_le (((2 * Complex.I * l) ^ (M + 1))⁻¹ • weakDerivative (wkbR φ (M + 1)))
    (∑ n ∈ Finset.Icc 1 (M + 1), ∑ j ∈ Finset.Icc 1 (M + 1),
      (if M + 1 ≤ n + j then ((2 * Complex.I * l) ^ (n + j))⁻¹ •
        physicalProduct φ.1 (physicalProduct (wkbR φ n) (wkbR φ j)) else 0))
  rw [div_eq_mul_inv]
  exact htri.trans ((add_le_add hfirst hsum).trans hfin)

theorem G1_035 (N : ℕ) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ φ : PotPair,
      pairSobolev (N : ℝ) φ → ∀ l : ℂ, 1 ≤ ‖l‖ →
      productInL2 (wkbPartial N l φ) (wkbPartial N l φ) ∧
      productInL2 φ.1
        (physicalProduct (wkbPartial N l φ) (wkbPartial N l φ)) ∧
      wkbResidual N l φ = wkbResidualTail N l φ ∧
      ‖wkbResidual N l φ‖ ≤
        C * (1 + pairSobolevNorm (N : ℝ) φ) ^ p / ‖l‖ ^ N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨C0, hC0, p0, hw⟩ := wkb_bound (M + 1) (M + 1) hN le_rfl
  obtain ⟨Cm, hCm, hprod⟩ := psn_prod 1 le_rfl
  refine ⟨2 * Real.pi * C0 + ((M + 1 : ℕ) : ℝ) ^ 2 * (Cm ^ 2 * C0 ^ 2),
    add_pos_of_pos_of_nonneg (mul_pos (by positivity) hC0) (by positivity),
    p0 + (2 * p0 + 1), ?_⟩
  intro φ hφ l hl
  have hφ1 : physicalSobolev ((1 : ℕ) : ℝ) φ.1 := (psn_mono (show 1 ≤ M + 1 by omega) hφ.1).1
  have hφX : physicalSobolevNorm ((1 : ℕ) : ℝ) φ.1 ≤ pairSobolevNorm ((M + 1 : ℕ) : ℝ) φ :=
    (psn_mono (show 1 ≤ M + 1 by omega) hφ.1).2.trans (pairSobolevNorm_ge (M + 1) φ).2.1
  have hX : 0 ≤ pairSobolevNorm ((M + 1 : ℕ) : ℝ) φ := (pairSobolevNorm_ge (M + 1) φ).1
  have hH : ∀ k, 1 ≤ k → k ≤ M + 1 → physicalSobolev ((1 : ℕ) : ℝ) (wkbR φ k) := fun k hk1 hk2 =>
    g35_H1_cast _ (g35_H1_wkbR M hN φ hφ k hk1 hk2)
  have hB : ∀ k, 1 ≤ k → k ≤ M + 1 → physicalSobolevNorm ((1 : ℕ) : ℝ) (wkbR φ k) ≤
      C0 * (1 + pairSobolevNorm ((M + 1 : ℕ) : ℝ) φ) ^ p0 := by
    intro k hk1 hk2
    obtain ⟨h1, h2⟩ := hw φ hφ k hk1 hk2
    exact (psn_mono (show 1 ≤ M + 1 + 1 - k by omega) h1).2.trans h2
  have hφ1' : physicalSobolev 1 φ.1 := g35_H1_nat _ hφ1
  have hid : wkbResidual (M + 1) l φ = wkbResidualTail (M + 1) l φ :=
    g35_identity M φ l hl (fun k hk1 hk2 => g35_H1_wkbR M hN φ hφ k hk1 hk2) hφ1'
  have hW1 : physicalSobolev 1 (wkbPartial (M + 1) l φ) :=
    g35_H1_sum _ _ (fun i hi => g35_H1_smul _
      (g35_H1_wkbR M hN φ hφ i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2))
  refine ⟨productInL2_of_H1 _ _ hW1, productInL2_of_H1 _ _ hφ1', hid, ?_⟩
  rw [hid]
  exact g35_tail_norm M C0 Cm (pairSobolevNorm ((M + 1 : ℕ) : ℝ) φ) p0 hC0.le hCm.le hX φ hprod
    hφ1 hφX hH hB l hl

end NlsGge.GKDefinitionDesign
end
