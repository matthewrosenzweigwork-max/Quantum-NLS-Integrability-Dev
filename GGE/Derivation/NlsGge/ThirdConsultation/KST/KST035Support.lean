import Mathlib
import NlsGge.Analysis.NaturalCoverCoefficients
import NlsGge.Atomic.DM.DM004
import NlsGge.Atomic.KST.KST002
import NlsGge.Atomic.KST.KST004
import NlsGge.Atomic.KST.KST007
import NlsGge.Atomic.KST.KST016
import NlsGge.Atomic.KST.KST018
import NlsGge.Atomic.KST.KST021
import NlsGge.Atomic.KST.KST022
import NlsGge.Atomic.KST.KST027
import NlsGge.Atomic.KST.KST028
import NlsGge.Atomic.KST.KST030
import NlsGge.Atomic.KST.KST031
import NlsGge.Atomic.KST.KST032
import NlsGge.ThirdConsultation.KST.Basic
import NlsGge.ThirdConsultation.KST.KST031Host
import NlsGge.ThirdConsultation.KST.KST031Support
import NlsGge.ThirdConsultation.KST.KST032Host
import NlsGge.ThirdConsultation.KST.KST034Host
import NlsGge.ThirdConsultation.KST.KST035Host
import NlsGge.ThirdConsultation.KST.KST035Core

/- KST035Support PRODUCTION01 (proof development, AUTHOR; not self-reviewed).  Target NlsGge/ThirdConsultation/KST/KST035Support.lean.
   SUPPORT module for KST-035 (no packet increment; no design head).  Contents (namespace KST035S):
   energy_le        : scalarEnergy omega (majorantCoeff psi) <= ofReal (4 R^2) on physicalComponentBall omega R;
   remainder_uniform: the KST-021 Fourier-remainder bound for b,c WITHOUT the phi-dependent threshold N0 of kst021
                      (summability of the path series comes from pathMajorant < top, the unit-ball square bound from
                      the uniform ||q^2|| < 1);
   rawEnergy_le     : the (69)-(73) assembly: for N past the diagonal threshold and satisfying two numerical
                      smallness conditions (functions of M, w, Cw, N only), every phi of the omega=wv ball satisfies
                      rawEnergy omega (adaptedCoefficients N phi - rawFourier phi) <= (M/16)^2.
   Route: see KST035_ROUTE.md (Prop 4.1 re-run with the uniformly available smallness, KST035Core.core_rel). -/
set_option autoImplicit false
open scoped ENNReal
open NlsGge.Atomic.KST002 NlsGge.Atomic.KST003 NlsGge.Atomic.KST004 NlsGge.Atomic.KST006 NlsGge.Atomic.KST007
open NlsGge.Atomic.KST012 NlsGge.Atomic.KST013 NlsGge.Atomic.KST016
open NlsGge.Analysis NlsGge.Pilot NlsGge.Schur NlsGge.Atomic.KSTPath NlsGge.Atomic.KST

namespace NlsGge.ThirdConsultation.KST
noncomputable section
attribute [local instance] Classical.propDecidable

namespace KST035S

theorem energy_le (ω : ℤ → ℝ) (hev : ∀ k, ω (-k) = ω k) (ψ : Potential) (R : ℝ)
    (hψ : ψ ∈ physicalComponentBall ω R) :
    scalarEnergy ω (majorantCoeff ψ) ≤ ENNReal.ofReal (4 * R ^ 2) := by
  have hco : ∀ (ch : Bool) (m : ℤ), potentialCoeff ψ ch (2 * m) = physicalFourier (ψ ch) m :=
    fun ch m => naturalPhysicalCoverL2_fourier_even (ψ ch) m
  set f : Bool → ℤ → ℝ≥0∞ := fun ch m =>
    ENNReal.ofReal (ω (2 * m) ^ 2 * ‖physicalFourier (ψ ch) m‖ ^ 2) with hf
  have hfs : ∀ ch, ∑' m, f ch m ≤ ENNReal.ofReal (R ^ 2) := fun ch => hψ ch
  have hfneg : ∀ ch, ∑' m : ℤ, ENNReal.ofReal (ω (2 * m) ^ 2 * ‖physicalFourier (ψ ch) (-m)‖ ^ 2) =
      ∑' m, f ch m := by
    intro ch
    have h := (Equiv.neg ℤ).tsum_eq (fun m => f ch m)
    rw [← h]
    refine tsum_congr (fun m => ?_)
    simp only [hf, Equiv.neg_apply]
    rw [show (2 : ℤ) * -m = -(2 * m) by ring, hev]
  have hinj : Function.Injective (fun m : ℤ => 2 * m) := fun a b h => by
    simp only at h; omega
  have hsupp : Function.support
      (fun k : ℤ => ENNReal.ofReal (ω k ^ 2 * majorantCoeff ψ k ^ 2)) ⊆
        Set.range (fun m : ℤ => 2 * m) := by
    intro k hk
    by_contra hnot
    apply hk
    have hodd : k % 2 ≠ 0 := fun h0 => hnot ⟨k / 2, by simp only; omega⟩
    simp [majorant_odd_eq_zero ψ k hodd]
  have hev2 : scalarEnergy ω (majorantCoeff ψ) =
      ∑' m : ℤ, ENNReal.ofReal (ω (2 * m) ^ 2 * majorantCoeff ψ (2 * m) ^ 2) := by
    unfold scalarEnergy
    exact (hinj.tsum_eq hsupp).symm
  have hpt : ∀ m : ℤ, ENNReal.ofReal (ω (2 * m) ^ 2 * majorantCoeff ψ (2 * m) ^ 2) ≤
      f true m + ENNReal.ofReal (ω (2 * m) ^ 2 * ‖physicalFourier (ψ true) (-m)‖ ^ 2) +
        f false m + ENNReal.ofReal (ω (2 * m) ^ 2 * ‖physicalFourier (ψ false) (-m)‖ ^ 2) := by
    intro m
    have h1 := K030.majorant_sq_le ψ (2 * m)
    have hneg : -(2 * m) = 2 * (-m) := by ring
    rw [hneg] at h1
    simp only [hco] at h1
    have hω0 : 0 ≤ ω (2 * m) ^ 2 := sq_nonneg _
    have h2 := mul_le_mul_of_nonneg_left h1 hω0
    refine (ENNReal.ofReal_le_ofReal h2).trans (le_of_eq ?_)
    have e : ω (2 * m) ^ 2 * (‖physicalFourier (ψ true) m‖ ^ 2 + ‖physicalFourier (ψ true) (-m)‖ ^ 2 +
        ‖physicalFourier (ψ false) m‖ ^ 2 + ‖physicalFourier (ψ false) (-m)‖ ^ 2) =
        ω (2 * m) ^ 2 * ‖physicalFourier (ψ true) m‖ ^ 2 +
        ω (2 * m) ^ 2 * ‖physicalFourier (ψ true) (-m)‖ ^ 2 +
        ω (2 * m) ^ 2 * ‖physicalFourier (ψ false) m‖ ^ 2 +
        ω (2 * m) ^ 2 * ‖physicalFourier (ψ false) (-m)‖ ^ 2 := by ring
    rw [e, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [hev2]
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add, hfneg true, hfneg false]
  have e4 : ENNReal.ofReal (4 * R ^ 2) = ENNReal.ofReal (R ^ 2) + ENNReal.ofReal (R ^ 2) +
      ENNReal.ofReal (R ^ 2) + ENNReal.ofReal (R ^ 2) := by
    rw [show 4 * R ^ 2 = R ^ 2 + R ^ 2 + R ^ 2 + R ^ 2 by ring,
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity)]
  rw [e4]
  exact add_le_add (add_le_add (add_le_add (hfs true) (hfs true)) (hfs false)) (hfs false)

theorem remainder_uniform (φ : Potential) (n : ℤ)
    (hpm : pathMajorant (majorantCoeff φ) n < ⊤) (z : ℂ) (hz : z ∈ spectralStrip n)
    (hlt : ‖qOperator φ n z hz ^ 2‖ < 1) :
    ‖reducedB φ n z hz - coveredCoeff φ false (2 * n)‖ ≤
        (pathMajorant (majorantCoeff φ) n).toReal ∧
      ‖reducedC φ n z hz - coveredCoeff φ true (-2 * n)‖ ≤
        (pathMajorant (majorantCoeff φ) n).toReal := by
  have hr0 : ∀ j : ℕ, 0 ≤ Rv φ n (2 * (j + 1)) n := fun j => Rv_nonneg φ n _ _
  have hnorm : ∀ j : ℕ, ‖positivePathTerm φ n j‖ = Rv φ n (2 * (j + 1)) n := by
    intro j
    rw [ppt_eq_Rv φ n j, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 j)]
  have hpm' : pathMajorant (majorantCoeff φ) n =
      ∑' j : ℕ, ENNReal.ofReal (Rv φ n (2 * (j + 1)) n) := by
    unfold pathMajorant
    exact tsum_congr (fun j => pathBlock_eq_ofReal φ n j)
  have hsumR : Summable (fun j : ℕ => Rv φ n (2 * (j + 1)) n) := by
    have h := ENNReal.summable_toReal
      (f := fun j : ℕ => ENNReal.ofReal (Rv φ n (2 * (j + 1)) n)) (by rw [← hpm']; exact hpm.ne)
    exact h.congr (fun j => ENNReal.toReal_ofReal (hr0 j))
  have hMtoReal : (pathMajorant (majorantCoeff φ) n).toReal =
      ∑' j : ℕ, Rv φ n (2 * (j + 1)) n := by
    rw [hpm', ENNReal.tsum_toReal_eq (fun j => ENNReal.ofReal_ne_top)]
    exact tsum_congr (fun j => ENNReal.toReal_ofReal (hr0 j))
  have hsum : Summable (fun j : ℕ => ‖positivePathTerm φ n j‖) :=
    hsumR.congr (fun j => (hnorm j).symm)
  have hsB : Summable (fun j : ℕ => ‖pathTerm φ n z hz (2 * j + 2) false true‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => pathTerm_B_le φ n z hz j) hsum
  have hsC : Summable (fun j : ℕ => ‖pathTerm φ n z hz (2 * j + 2) true false‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => pathTerm_C_le φ n z hz j) hsum
  have hremB : ‖remainderB φ n z hz‖ ≤ (pathMajorant (majorantCoeff φ) n).toReal := by
    rw [hMtoReal]
    calc ‖remainderB φ n z hz‖ ≤ ∑' j : ℕ, ‖pathTerm φ n z hz (2 * j + 2) false true‖ :=
          norm_tsum_le_tsum_norm hsB
      _ ≤ ∑' j : ℕ, ‖positivePathTerm φ n j‖ :=
          hsB.tsum_le_tsum (fun j => pathTerm_B_le φ n z hz j) hsum
      _ = _ := tsum_congr hnorm
  have hremC : ‖remainderC φ n z hz‖ ≤ (pathMajorant (majorantCoeff φ) n).toReal := by
    rw [hMtoReal]
    calc ‖remainderC φ n z hz‖ ≤ ∑' j : ℕ, ‖pathTerm φ n z hz (2 * j + 2) true false‖ :=
          norm_tsum_le_tsum_norm hsC
      _ ≤ ∑' j : ℕ, ‖positivePathTerm φ n j‖ :=
          hsC.tsum_le_tsum (fun j => pathTerm_C_le φ n z hz j) hsum
      _ = _ := tsum_congr hnorm
  obtain ⟨-, -, hB, hC⟩ := reducedBC_fourier_remainders φ n z hz hlt
  refine ⟨?_, ?_⟩
  · rw [hB, add_sub_cancel_left]; exact hremB
  · rw [hC, add_sub_cancel_left]; exact hremC

theorem rawEnergy_le (w : ℤ → ℝ) (Cw M : ℝ) (hM : 1 ≤ M) (hw : SlowWeight w Cw)
    (hunb : Filter.Tendsto (fun n : ℕ => w (n : ℤ)) Filter.atTop Filter.atTop)
    (v : ℤ → ℝ) (hv : SecondaryWeight v) (N : ℕ) (hN : 1 ≤ N)
    (hNd : diagonalThreshold w M ≤ N)
    (hs1 : Cw ^ 2 * (16 * M ^ 2 / w (N : ℤ) ^ 2 + 16 * M ^ 2 / Real.sqrt (N : ℝ)) ≤ 1 / 60)
    (hs2 : 900 * Cw ^ 2 * (16 * M ^ 2 + 1) *
        (16 * M ^ 2 / w (N : ℤ) ^ 2 + 16 * M ^ 2 / Real.sqrt (N : ℝ)) ^ 2 ≤ (M / 16) ^ 2 / 2)
    (φ : Potential) (hφ : φ ∈ physicalComponentBall (productWeight w v) (2 * M)) :
    rawEnergy (productWeight w v) (adaptedCoefficients N φ - rawFourier φ) ≤
      ENNReal.ofReal ((M / 16) ^ 2) := by
  have hw' : UnboundedWeight w := ⟨⟨hw.one_le, hw.even, hw.radial_mono⟩, hunb⟩
  have hC : 1 ≤ Cw := slowWeight_Cw_one_le hw
  have hC2 : 1 ≤ Cw ^ 2 := by nlinarith
  have hM0 : 0 < M := by linarith
  have hωev : ∀ k, productWeight w v (-k) = productWeight w v k := fun k => by
    simp only [productWeight, hw.even, hv.1.2.1]
  have hφw : φ ∈ physicalComponentBall w (2 * M) :=
    KST031S.ball_productWeight_subset w v hw.one_le hv.1.1 _ hφ
  set A : ℤ → ℝ := majorantCoeff φ with hA
  set A' : ℤ → ℝ := fun j => v j * A j with hA'
  have hA0 : ∀ j, 0 ≤ A j := fun j => majorant_nonneg φ j
  have hv0 : ∀ j, 0 ≤ v j := fun j => by linarith [hv.1.1 j]
  have hA'0 : ∀ j, 0 ≤ A' j := fun j => mul_nonneg (hv0 j) (hA0 j)
  have hEeq : scalarEnergy w A' = scalarEnergy (productWeight w v) A := by
    unfold scalarEnergy
    refine tsum_congr (fun j => ?_)
    simp only [hA', productWeight]
    congr 1; ring
  have hEle : scalarEnergy w A' ≤ ENNReal.ofReal (4 * (2 * M) ^ 2) := by
    rw [hEeq]; exact energy_le _ hωev φ (2 * M) hφ
  have hEtop : scalarEnergy w A' < ⊤ := lt_of_le_of_lt hEle ENNReal.ofReal_lt_top
  set E : ℝ := (scalarEnergy w A').toReal with hE
  set T : ℝ := (scalarTailEnergy w A' N).toReal with hT
  have hE16 : E ≤ 16 * M ^ 2 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hEle
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    nlinarith [h]
  have hTE : scalarTailEnergy w A' N ≤ scalarEnergy w A' :=
    ENNReal.tsum_le_tsum (fun j => by split_ifs <;> simp)
  have hT0 : 0 ≤ T := ENNReal.toReal_nonneg
  have hE0 : 0 ≤ E := ENNReal.toReal_nonneg
  have hTE' : T ≤ E := ENNReal.toReal_mono hEtop.ne hTE
  have hwN : 1 ≤ w (N : ℤ) := hw.one_le _
  have hwN2 : 1 ≤ w (N : ℤ) ^ 2 := by nlinarith
  have hsqN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have has : T / w (N : ℤ) ^ 2 ≤ 16 * M ^ 2 / w (N : ℤ) ^ 2 :=
    div_le_div_of_nonneg_right (hTE'.trans hE16) (by positivity)
  have hys : E / Real.sqrt (N : ℝ) ≤ 16 * M ^ 2 / Real.sqrt (N : ℝ) :=
    div_le_div_of_nonneg_right hE16 hsqN.le
  have has' : 0 ≤ 16 * M ^ 2 / w (N : ℤ) ^ 2 := by positivity
  have hys' : 0 ≤ 16 * M ^ 2 / Real.sqrt (N : ℝ) := by positivity
  have ha0 : 0 ≤ T / w (N : ℤ) ^ 2 := div_nonneg hT0 (sq_nonneg _)
  have hy0 : 0 ≤ E / Real.sqrt (N : ℝ) := div_nonneg hE0 hsqN.le
  have hy1 : Cw ^ 2 * (E / Real.sqrt (N : ℝ)) ≤ 1 / 60 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)) hs1
    linarith
  have ha1 : T / w (N : ℤ) ^ 2 ≤ 1 / 60 := by
    have h0 : 0 ≤ 16 * M ^ 2 / w (N : ℤ) ^ 2 + 16 * M ^ 2 / Real.sqrt (N : ℝ) := by linarith
    have : T / w (N : ℤ) ^ 2 ≤ Cw ^ 2 * (16 * M ^ 2 / w (N : ℤ) ^ 2 + 16 * M ^ 2 / Real.sqrt (N : ℝ)) := by
      nlinarith [mul_nonneg h0 (sub_nonneg.2 hC2)]
    exact this.trans hs1
  have htail0 := KST035C.core_rel w A' Cw hw hA'0 hEtop N hN hy1 ha1
  have htail : weightedMajorantTail w A' N ≤ ENNReal.ofReal ((M / 16) ^ 2 / 2) := by
    refine htail0.trans (ENNReal.ofReal_le_ofReal ?_)
    refine le_trans ?_ hs2
    have h1 : (T + 1) ≤ 16 * M ^ 2 + 1 := by linarith
    have h2 : (T / w (N : ℤ) ^ 2 + E / Real.sqrt (N : ℝ)) ^ 2 ≤
        (16 * M ^ 2 / w (N : ℤ) ^ 2 + 16 * M ^ 2 / Real.sqrt (N : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h3 : 0 ≤ 900 * Cw ^ 2 := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 h3) h2 (by positivity) (by positivity)
  -- pointwise path-majorant control for N ≤ |n|
  have hkey : ∀ n : ℤ, N ≤ n.natAbs →
      pathMajorant A n < ⊤ ∧
      ENNReal.ofReal (productWeight w v (2 * n) ^ 2 * ((pathMajorant A n).toReal) ^ 2) ≤
        ENNReal.ofReal (w (2 * n) ^ 2) * pathMajorant A' n ^ 2 := by
    intro n hn
    have h28 : ENNReal.ofReal (v (2 * n)) * pathMajorant A n ≤ pathMajorant A' n :=
      kst028 v A hv hA0 n
    have hterm : ENNReal.ofReal (w (2 * n) ^ 2) * pathMajorant A' n ^ 2 ≤
        weightedMajorantTail w A' N := by
      unfold weightedMajorantTail
      calc ENNReal.ofReal (w (2 * n) ^ 2) * pathMajorant A' n ^ 2
          = (if N ≤ n.natAbs then ENNReal.ofReal (w (2 * n) ^ 2) * pathMajorant A' n ^ 2
              else 0) := by rw [if_pos hn]
        _ ≤ _ := ENNReal.le_tsum (f := fun n : ℤ => if N ≤ n.natAbs then
              ENNReal.ofReal (w (2 * n) ^ 2) * pathMajorant A' n ^ 2 else 0) n
    have htailfin : weightedMajorantTail w A' N < ⊤ := lt_of_le_of_lt htail ENNReal.ofReal_lt_top
    have hfin : pathMajorant A' n < ⊤ := by
      by_contra hcon
      have htop : pathMajorant A' n = ⊤ := not_lt_top_iff.mp hcon
      have hne : ENNReal.ofReal (w (2 * n) ^ 2) ≠ 0 := by
        have : 0 < w (2 * n) ^ 2 := by nlinarith [hw.one_le (2 * n)]
        exact (ENNReal.ofReal_pos.2 this).ne'
      rw [htop, ENNReal.top_pow (by norm_num), ENNReal.mul_top hne] at hterm
      exact (not_le.mpr htailfin) hterm
    have h1 : pathMajorant A n ≤ pathMajorant A' n := by
      refine le_trans ?_ h28
      calc pathMajorant A n = 1 * pathMajorant A n := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (ENNReal.one_le_ofReal.mpr (hv.1.1 _)) le_rfl
    have hpm : pathMajorant A n < ⊤ := lt_of_le_of_lt h1 hfin
    refine ⟨hpm, ?_⟩
    have hv2 : 0 ≤ v (2 * n) := hv0 _
    have hw2 : 0 ≤ w (2 * n) ^ 2 := sq_nonneg _
    have e : ENNReal.ofReal (productWeight w v (2 * n) ^ 2 * ((pathMajorant A n).toReal) ^ 2) =
        ENNReal.ofReal (w (2 * n) ^ 2) *
          (ENNReal.ofReal (v (2 * n)) * pathMajorant A n) ^ 2 := by
      have e1 : productWeight w v (2 * n) ^ 2 * ((pathMajorant A n).toReal) ^ 2 =
          w (2 * n) ^ 2 * (v (2 * n) * (pathMajorant A n).toReal) ^ 2 := by
        simp only [productWeight]; ring
      rw [e1, ENNReal.ofReal_mul hw2, ENNReal.ofReal_pow (mul_nonneg hv2 ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul hv2, ENNReal.ofReal_toReal hpm.ne]
    rw [e]
    exact mul_le_mul' le_rfl (pow_le_pow_left' h28 2)
  -- the pointwise coefficient bounds at the diagonal zero
  have hcoef : ∀ n : ℤ, N ≤ n.natAbs →
      ‖b φ n (diagonalZero n φ) - physicalFourier (φ false) n‖ ≤ (pathMajorant A n).toReal ∧
      ‖c φ n (diagonalZero n φ) - physicalFourier (φ true) (-n)‖ ≤ (pathMajorant A n).toReal := by
    intro n hn
    have hnd : diagonalThreshold w M ≤ n.natAbs := le_trans hNd hn
    obtain ⟨-, hall⟩ := (kst031 w M hM hw').2.1
    obtain ⟨-, hQ, -⟩ := hall φ hφw n hnd
    obtain ⟨-, -, hmem, -, -⟩ := kst032 w M hM hw' φ hφw n hnd
    have hσ : diagonalZero n φ ∈ spectralStrip n :=
      KST032S.closedBall_sub_strip n (center n) (Metric.mem_closedBall_self (by positivity))
        (Real.pi / 48) (by nlinarith [Real.pi_pos]) hmem
    have hlt : ‖qOperator φ n (diagonalZero n φ) hσ ^ 2‖ < 1 :=
      lt_of_le_of_lt (hQ _ hσ).1 (by norm_num)
    obtain ⟨hB, hCc⟩ := remainder_uniform φ n (hkey n hn).1 _ hσ hlt
    have eb : b φ n (diagonalZero n φ) = reducedB φ n (diagonalZero n φ) hσ := by
      show (abc φ n (diagonalZero n φ)).2.1 = _
      rw [abc_eq_reduced φ n _ hσ]
    have ec : c φ n (diagonalZero n φ) = reducedC φ n (diagonalZero n φ) hσ := by
      show (abc φ n (diagonalZero n φ)).2.2 = _
      rw [abc_eq_reduced φ n _ hσ]
    have cb : coveredCoeff φ false (2 * n) = physicalFourier (φ false) n :=
      naturalPhysicalCoverL2_fourier_even (φ false) n
    have cc : coveredCoeff φ true (-2 * n) = physicalFourier (φ true) (-n) := by
      rw [show (-2 : ℤ) * n = 2 * (-n) by ring]
      exact naturalPhysicalCoverL2_fourier_even (φ true) (-n)
    rw [eb, ← cb, ec, ← cc]
    exact ⟨hB, hCc⟩
  -- the sum
  set g : ℤ → ℝ≥0∞ := fun n => if N ≤ n.natAbs then
      ENNReal.ofReal (w (2 * n) ^ 2) * pathMajorant A' n ^ 2 else 0 with hg
  have hgsum : ∑' n, g n = weightedMajorantTail w A' N := rfl
  have hterm : ∀ m : ℤ, ENNReal.ofReal (productWeight w v (2 * m) ^ 2 *
      (‖(adaptedCoefficients N φ - rawFourier φ) true m‖ ^ 2 +
        ‖(adaptedCoefficients N φ - rawFourier φ) false m‖ ^ 2)) ≤ g (-m) + g m := by
    intro m
    by_cases hm : m.natAbs ≤ N
    · have h0 : ∀ ch, (adaptedCoefficients N φ - rawFourier φ) ch m = 0 := by
        intro ch
        simp [adaptedCoefficients, hm]
      simp [h0]
    · have hNm : N < m.natAbs := not_le.mp hm
      have hm1 : N ≤ (-m).natAbs := by simp; omega
      have hm2 : N ≤ m.natAbs := hNm.le
      obtain ⟨hbf, -⟩ := hcoef m hm2
      obtain ⟨-, hct⟩ := hcoef (-m) hm1
      rw [neg_neg] at hct
      have dF : (adaptedCoefficients N φ - rawFourier φ) false m =
          b φ m (diagonalZero m φ) - physicalFourier (φ false) m := by
        simp [adaptedCoefficients, hm, rawFourier]
      have dT : (adaptedCoefficients N φ - rawFourier φ) true m =
          c φ (-m) (diagonalZero (-m) φ) - physicalFourier (φ true) m := by
        simp [adaptedCoefficients, hm, rawFourier]
      rw [dF, dT]
      have hωm : productWeight w v (2 * m) = productWeight w v (2 * (-m)) := by
        rw [show 2 * -m = -(2 * m) by ring, hωev]
      have hk1 := (hkey (-m) hm1).2
      have hk2 := (hkey m hm2).2
      have hq1 : ENNReal.ofReal (productWeight w v (2 * m) ^ 2 * ‖c φ (-m) (diagonalZero (-m) φ) -
          physicalFourier (φ true) m‖ ^ 2) ≤ g (-m) := by
        have step : productWeight w v (2 * m) ^ 2 * ‖c φ (-m) (diagonalZero (-m) φ) -
            physicalFourier (φ true) m‖ ^ 2 ≤
            productWeight w v (2 * -m) ^ 2 * ((pathMajorant A (-m)).toReal) ^ 2 := by
          rw [← hωm]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hct 2) (sq_nonneg _)
        simp only [hg, if_pos hm1]
        exact (ENNReal.ofReal_le_ofReal step).trans hk1
      have hq2 : ENNReal.ofReal (productWeight w v (2 * m) ^ 2 * ‖b φ m (diagonalZero m φ) -
          physicalFourier (φ false) m‖ ^ 2) ≤ g m := by
        have step : productWeight w v (2 * m) ^ 2 * ‖b φ m (diagonalZero m φ) -
            physicalFourier (φ false) m‖ ^ 2 ≤
            productWeight w v (2 * m) ^ 2 * ((pathMajorant A m).toReal) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hbf 2) (sq_nonneg _)
        simp only [hg, if_pos hm2]
        exact (ENNReal.ofReal_le_ofReal step).trans hk2
      rw [mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add hq1 hq2
  have hraw : rawEnergy (productWeight w v) (adaptedCoefficients N φ - rawFourier φ) ≤
      ∑' m, (g (-m) + g m) := ENNReal.tsum_le_tsum hterm
  have hneg : ∑' m : ℤ, g (-m) = ∑' m, g m := (Equiv.neg ℤ).tsum_eq g
  refine hraw.trans ?_
  rw [ENNReal.tsum_add, hneg, hgsum]
  calc weightedMajorantTail w A' N + weightedMajorantTail w A' N
      ≤ ENNReal.ofReal ((M / 16) ^ 2 / 2) + ENNReal.ofReal ((M / 16) ^ 2 / 2) :=
        add_le_add htail htail
    _ = ENNReal.ofReal ((M / 16) ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end KST035S

end
end NlsGge.ThirdConsultation.KST
