import NlsGge.Atomic.S.S001
import NlsGge.Spectral.ActualGapActionAllNE02_38
import LiebLiniger.FixedPeriod.Atomic.ORIG.B018SobolevMoment

/-! # B050.C01 (records NEW-E01, NEW-F03): reflected gap-action bound and moment chain

v2 l.1012: the action bound `F:eq:gapaction` and the moment inequalities `F:eq:moment` are
unchanged by the reflection `𝖫_u = -L_{-u}`. Pure composition of S001 (reflected Dirac
convention), the E02 gap-action bound and the B018.C02 moment theorems. -/

set_option autoImplicit false
noncomputable section

namespace NlsGge.Atomic.B050

open MeasureTheory Filter Topology NlsGge.Pilot NlsGge.Schur NlsGge.Analysis
open NlsGge.SpectralFoundations NlsGge.HierarchyRiccati.Core NlsGge.Atomic.S001
open scoped ContDiff

/-- The reflected real even charge `Q_{2j} = (2/π) ∫ (2λ)^{2j} v(λ) dλ` of the reflected Dirac
operator `𝖫_u` (v2 F:eq:Dirac), as a real number (finiteness is asserted separately). -/
def reflectedCharge (u : PhysicalL2) (j : ℕ) : ℝ :=
  (2 / Real.pi) * ∫ x : ℝ, (2 * x) ^ (2 * j) * reflectedHeight u x

/-- The reflected spectral height is nonnegative. -/
theorem reflectedHeight_nonneg_B050 (u : PhysicalL2) (x : ℝ) : 0 ≤ reflectedHeight u x := by
  rw [reflectedHeight_eq]
  exact actualGapHeightE02_38_nonneg u (-x)

/-- Under integrability, the reflected ENNReal even moment is `ofReal` of the real charge. -/
theorem reflectedEvenMomentENN_eq_ofReal_B050 (u : PhysicalL2) (j : ℕ)
    (hint : Integrable (fun x : ℝ => (2 * x) ^ (2 * j) * reflectedHeight u x)) :
    reflectedEvenMomentENN u j = ENNReal.ofReal (reflectedCharge u j) := by
  have hnn : ∀ x : ℝ, 0 ≤ (2 * x) ^ (2 * j) * reflectedHeight u x := fun x =>
    mul_nonneg ((even_two_mul j).pow_nonneg _) (reflectedHeight_nonneg_B050 u x)
  unfold reflectedEvenMomentENN reflectedCharge
  rw [ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]

/-- Smooth-field reflected charges: integrability, finiteness, `ofReal` conversion and the
identification with the local charge. -/
theorem reflected_smooth_B050 (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1)
    (j : ℕ) :
    Integrable (fun x : ℝ => (2 * x) ^ (2 * j) * reflectedHeight (smoothL2_38 U hU hper) x) ∧
      reflectedEvenMomentENN (smoothL2_38 U hU hper) j < ⊤ ∧
      reflectedEvenMomentENN (smoothL2_38 U hU hper) j =
        ENNReal.ofReal (reflectedCharge (smoothL2_38 U hU hper) j) ∧
      reflectedCharge (smoothL2_38 U hU hper) j = localCharge38 U j := by
  obtain ⟨_, hint, _, hfin, hR, _⟩ := reflected_evenMoment_smooth U hU hper j
  exact ⟨hint, hfin, reflectedEvenMomentENN_eq_ofReal_B050 _ j hint, hR⟩

/-- The L² class of a Fourier truncation is the smooth L² class of the truncated field. -/
theorem sobolevToL2_trunc_smooth_B050 (j N : ℕ) (x : SobolevHilbert ((j : ℕ) : ℝ)) :
    sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x) =
      smoothL2_38 (truncField38 (j : ℝ) N x) (contDiff_truncField38 (j : ℝ) N x)
        (periodic_truncField38 (j : ℝ) N x) := by
  rw [sobolevToL2_trunc_B018]
  rfl

/-- The truncated reflected charge equals the extended charge at the truncation. -/
theorem reflectedCharge_trunc_B050 (j : ℕ) (hj : 1 ≤ j) (x : SobolevHilbert ((j : ℕ) : ℝ)) (i : ℕ)
    (hi : i ≤ j) (N : ℕ) :
    reflectedCharge (sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x)) i =
      chargeSobolev38 (j + 1) i (truncSobolev38 (j : ℝ) N x) := by
  have hc : chargeSobolev38 (j + 1) i (truncSobolev38 (j : ℝ) N x) =
      localCharge38 (truncField38 (j : ℝ) N x) i :=
    chargeSobolev38_smooth (j + 1) i (by omega) (by omega) (truncField38 (j : ℝ) N x)
      (contDiff_truncField38 (j : ℝ) N x) (periodic_truncField38 (j : ℝ) N x)
      (truncSobolev38 (j : ℝ) N x) (truncSobolev38_link (j : ℝ) N x)
  rw [hc, sobolevToL2_trunc_smooth_B050]
  exact (reflected_smooth_B050 _ _ _ i).2.2.2

/-- **B050.C01** (v2 l.1012): the action bound `F:eq:gapaction` and the moment inequalities
`F:eq:moment` (smooth chain and fixed-Sobolev extension) hold unchanged in the reflected
Dirac convention. -/
theorem reflectedGapActionMoment_B050 :
    -- (A) F:eq:gapaction for the reflected gaps g_n of 𝖫_u, every n ∈ ℤ, closed gaps included
    (∀ (u : PhysicalL2) (n : ℤ),
      (reflectedGapUpper u n - reflectedGapLower u n) ^ 2 / 4 ≤ reflectedAction u n) ∧
    -- (B) F:eq:moment for smooth fields, in the reflected spectral charges
    (∀ (U : ℝ → ℂ) (hU : ContDiff ℝ ∞ U) (hper : Function.Periodic U 1),
      let u := smoothL2_38 U hU hper
      (∀ j : ℕ,
        Integrable (fun x : ℝ => (2 * x) ^ (2 * j) * reflectedHeight u x) ∧
        reflectedEvenMomentENN u j < ⊤ ∧
        reflectedEvenMomentENN u j = ENNReal.ofReal (reflectedCharge u j) ∧
        reflectedCharge u j = localCharge38 U j) ∧
      (reflectedCharge u 0) ^ 2 ≤ ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 4 ∧
      ∫ x in (0 : ℝ)..1, ‖U x‖ ^ 4 ≤ reflectedCharge u 1 ∧
      ∀ j : ℕ, 1 ≤ j →
        (reflectedCharge u 1) ^ (((j : ℝ) + 1) / 2) ≤ reflectedCharge u j ∧
        (reflectedCharge u 0) ^ (j + 1) ≤ reflectedCharge u j ∧
        (U ≠ 0 →
          0 < reflectedCharge u 0 ∧
          (reflectedCharge u 1) ^ j / (reflectedCharge u 0) ^ (j - 1) ≤ reflectedCharge u j ∧
          (reflectedCharge u 1) ^ (((j : ℝ) + 1) / 2) ≤
            (reflectedCharge u 1) ^ j / (reflectedCharge u 0) ^ (j - 1))) ∧
    -- (C) fixed-Sobolev extension on H^j, bound to the reflected charges
    (∀ (j : ℕ), 1 ≤ j → ∀ x : SobolevHilbert ((j : ℕ) : ℝ),
      -- (C1) same-field reflection of the spectral even moments (ENNReal, no conversion)
      (∀ i : ℕ, reflectedEvenMomentENN (sobolevToL2_38 j x) i =
        evenMomentENN (sobolevToL2_38 j x) i) ∧
      -- (C2) continuous-extension/truncation correspondence for i ≤ j
      (∀ i : ℕ, i ≤ j →
        (∀ N : ℕ,
          reflectedEvenMomentENN (sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x)) i < ⊤ ∧
          reflectedEvenMomentENN (sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x)) i =
            ENNReal.ofReal
              (reflectedCharge (sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x)) i) ∧
          reflectedCharge (sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x)) i =
            chargeSobolev38 (j + 1) i (truncSobolev38 (j : ℝ) N x)) ∧
        Tendsto (fun N : ℕ =>
            reflectedCharge (sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x)) i)
          atTop (𝓝 (chargeSobolev38 (j + 1) i x))) ∧
      -- (C3) the moment chain for the extended charges
      Integrable (fun z : PhysicalCircle =>
        ‖(sobolevToL2_38 j x : PhysicalCircle → ℂ) z‖ ^ 4) spatialMeasure ∧
      (chargeSobolev38 (j + 1) 0 x) ^ 2 ≤
        ∫ z, ‖(sobolevToL2_38 j x : PhysicalCircle → ℂ) z‖ ^ 4 ∂spatialMeasure ∧
      ∫ z, ‖(sobolevToL2_38 j x : PhysicalCircle → ℂ) z‖ ^ 4 ∂spatialMeasure ≤
        chargeSobolev38 (j + 1) 1 x ∧
      (chargeSobolev38 (j + 1) 1 x) ^ (((j : ℝ) + 1) / 2) ≤ chargeSobolev38 (j + 1) j x ∧
      (chargeSobolev38 (j + 1) 0 x) ^ (j + 1) ≤ chargeSobolev38 (j + 1) j x ∧
      (x ≠ 0 →
        0 < chargeSobolev38 (j + 1) 0 x ∧
        (chargeSobolev38 (j + 1) 1 x) ^ j / (chargeSobolev38 (j + 1) 0 x) ^ (j - 1) ≤
          chargeSobolev38 (j + 1) j x ∧
        (chargeSobolev38 (j + 1) 1 x) ^ (((j : ℝ) + 1) / 2) ≤
          (chargeSobolev38 (j + 1) 1 x) ^ j / (chargeSobolev38 (j + 1) 0 x) ^ (j - 1))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (A)
    intro u n
    obtain ⟨hl, hu, ha⟩ := (reflectedDirac_moments_and_actions u).1 n
    rw [hl, hu, ha]
    calc (-actualGapLowerAllE02_38 u (-n) - -actualGapUpperAllE02_38 u (-n)) ^ 2 / 4
        = (actualGapUpperAllE02_38 u (-n) - actualGapLowerAllE02_38 u (-n)) ^ 2 / 4 := by ring
      _ ≤ actualGapActionAllE02_38 u (-n) := actualGapAction_ge_sq_div_four_all_E02_38 u (-n)
  · -- (B)
    intro U hU hper u
    have hc : ∀ i : ℕ, reflectedCharge u i = localCharge38 U i := fun i =>
      (reflected_smooth_B050 U hU hper i).2.2.2
    refine ⟨fun j => reflected_smooth_B050 U hU hper j, ?_⟩
    simp only [hc]
    exact smoothMomentH38 U hU hper
  · -- (C)
    intro j hj x
    refine ⟨fun i => (reflectedDirac_moments_and_actions _).2.1 i, ?_, sobolevMomentH38 j hj x⟩
    intro i hi
    have hN : ∀ N : ℕ,
        reflectedEvenMomentENN (sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x)) i < ⊤ ∧
        reflectedEvenMomentENN (sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x)) i =
          ENNReal.ofReal (reflectedCharge (sobolevToL2_38 j (truncSobolev38 (j : ℝ) N x)) i) := by
      intro N
      rw [sobolevToL2_trunc_smooth_B050]
      exact ⟨(reflected_smooth_B050 _ _ _ i).2.1, (reflected_smooth_B050 _ _ _ i).2.2.1⟩
    refine ⟨fun N => ⟨(hN N).1, (hN N).2, reflectedCharge_trunc_B050 j hj x i hi N⟩, ?_⟩
    have hcont : Continuous (chargeSobolev38 (j + 1) i) :=
      continuous_chargeSobolev38 (j + 1) i (by omega)
    have ht : Tendsto (fun N : ℕ => chargeSobolev38 (j + 1) i (truncSobolev38 (j : ℝ) N x))
        atTop (𝓝 (chargeSobolev38 (j + 1) i x)) :=
      (hcont.tendsto x).comp (tendsto_truncSobolev38 (j : ℝ) x)
    exact ht.congr fun N => (reflectedCharge_trunc_B050 j hj x i hi N).symm

end NlsGge.Atomic.B050
