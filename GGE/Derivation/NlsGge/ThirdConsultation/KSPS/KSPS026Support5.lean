import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS026Support4

/- KSPS-026 SUPPORT5 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS026Support5.lean.
   KSPS-026 step 4 (KSPS026_MAP01.md) and the per-endpoint assembly. For one endpoint sequence xi (= periodicPlus φ or
   periodicMinus φ), with r_ij = lead_ij + E_ij (lead = (e, i hatφ1(-n); -i hatφ2(n), -e), e = I_(N+1)/(2 i xi)^(N+1),
   E_ij = endpointEntryError, Support3), the radicand error
     h := q1^2 - 4 q0 q2 + 4 hatφ1(-n) hatφ2(n)
   equals (exact ring identity, i^2 = -1; the e^2 terms cancel)
     4 e (α r01 - β r10) + X^2 + 4 (E00 E11 - i hatφ1 E10 + i hatφ2 E01 - E01 E10) - 4 α β P - 2 (A + C) P + P^2,
   X = E00 - E11 - β r10 + α r01, P = r00 r11 - r01 r10, A = r00 - β r10, C = r11 - α r01,
   and every term is weighted l1 of order 2N+1 by the Support1 product rules (Cauchy-Schwarz): E_ij in l2 (N+1),
   hatφ in l2 (N) (H^N tails, KSPS-001), e bounded at order N+1, α, β bounded at order 1, 1/w in l2.
   q0 = -1 + (small) is eventually nonzero; the quadratic vanishes eventually by Support4.
   The KSPS-011/012/013/014/015 head conclusions for xi enter as explicit hypotheses of exactly their landed types. -/
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS026W
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS015W NlsGge.ThirdConsultation.KSPS016W

theorem abc_apply {N : ℕ} (φ : SobolevC N) (n : ℤ) (z : ℂ) (hz : z ≠ 0) :
    KSPSWKB.endpointQuadraticABC N φ n ⟨z, hz⟩ 0 =
      -1 + KSPSWKB.alpha φ z 0 * KSPSWKB.beta φ z 0 + KSPSWKB.scaledEndpointCorrection N φ n ⟨z, hz⟩ 0 0 -
        KSPSWKB.beta φ z 0 * KSPSWKB.scaledEndpointCorrection N φ n ⟨z, hz⟩ 1 0 ∧
    KSPSWKB.endpointQuadraticABC N φ n ⟨z, hz⟩ 1 =
      1 + (1 - KSPSWKB.scaledEndpointCorrection N φ n ⟨z, hz⟩ 0 0) *
          (1 - KSPSWKB.scaledEndpointCorrection N φ n ⟨z, hz⟩ 1 1) - KSPSWKB.alpha φ z 0 * KSPSWKB.beta φ z 0 -
        (KSPSWKB.alpha φ z 0 - KSPSWKB.scaledEndpointCorrection N φ n ⟨z, hz⟩ 1 0) *
          (KSPSWKB.beta φ z 0 - KSPSWKB.scaledEndpointCorrection N φ n ⟨z, hz⟩ 0 1) ∧
    KSPSWKB.endpointQuadraticABC N φ n ⟨z, hz⟩ 2 =
      -1 + KSPSWKB.alpha φ z 0 * KSPSWKB.beta φ z 0 + KSPSWKB.scaledEndpointCorrection N φ n ⟨z, hz⟩ 1 1 -
        KSPSWKB.alpha φ z 0 * KSPSWKB.scaledEndpointCorrection N φ n ⟨z, hz⟩ 0 1 :=
  ⟨rfl, rfl, rfl⟩

/-- The exact radicand identity (pure algebra). -/
theorem rad_identity (e a1 a2 E00 E01 E10 E11 α β : ℂ) :
    (1 + (1 - (e + E00)) * (1 - (-e + E11)) - α * β -
        (α - (-Complex.I * a2 + E10)) * (β - (Complex.I * a1 + E01))) ^ 2 -
      4 * (-1 + α * β + (e + E00) - β * (-Complex.I * a2 + E10)) *
        (-1 + α * β + (-e + E11) - α * (Complex.I * a1 + E01)) + 4 * a1 * a2 =
    4 * (e * (α * (Complex.I * a1 + E01) - β * (-Complex.I * a2 + E10))) +
      (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) *
        (E00 - E11 - β * (-Complex.I * a2 + E10) + α * (Complex.I * a1 + E01)) +
      4 * (E00 * E11 - Complex.I * (a1 * E10) + Complex.I * (a2 * E01) - E01 * E10) -
      4 * ((α * β) * ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) -
      2 * (((e + E00) - β * (-Complex.I * a2 + E10) + ((-e + E11) - α * (Complex.I * a1 + E01))) *
        ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10))) +
      ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) *
        ((e + E00) * (-e + E11) - (Complex.I * a1 + E01) * (-Complex.I * a2 + E10)) := by
  linear_combination (4 * a1 * a2) * Complex.I_sq

/-! ### Per-index tail facts -/

theorem tail_pack {N : ℕ} (φ : SobolevC N) (xi : ℤ → ℂ) (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) (n : ℤ)
    (hn : ((⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 : ℕ) : ℤ) ≤ |n|) :
    xi n ≠ 0 ∧ WKBThreshold N (sobolevNorm N φ) (xi n) ∧ 1 ≤ ‖xi n‖ ∧ indexWeight n ≤ 2 * ‖xi n‖ ∧
      1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0 ≠ 0 ∧
      ‖KSPSWKB.alpha φ (xi n) 0‖ ≤ Sb φ / (2 * ‖xi n‖) ∧ ‖KSPSWKB.beta φ (xi n) 0‖ ≤ Sb φ / (2 * ‖xi n‖) := by
  obtain ⟨hX1, hXT, hwX⟩ := tail_facts a _ ha xi hxi n hn
  have hz : xi n ≠ 0 := by
    intro h; rw [h, norm_zero] at hX1; norm_num at hX1
  have hX0 : 0 < ‖xi n‖ := by linarith
  have hthr : WKBThreshold N (sobolevNorm N φ) (xi n) := ⟨hX0, hXT⟩
  have hdet := KSPSWKB.initialColumns_det_bound N (sobolevNorm N φ) φ (xi n) le_rfl hthr
  have hdetv : Matrix.det (KSPSWKB.initialColumns φ (xi n)) =
      1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0 := by
    simp [KSPSWKB.initialColumns, Matrix.det_fin_two]
  rw [hdetv] at hdet
  have hD : 1 - KSPSWKB.beta φ (xi n) 0 * KSPSWKB.alpha φ (xi n) 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hdet; norm_num at hdet
  have hw0 : 0 < indexWeight n := lt_of_lt_of_le one_pos (one_le_w n)
  obtain ⟨_, _, hα, hβ⟩ := dinv_facts φ (xi n) (indexWeight n) hX1 hthr hw0 hwX
  exact ⟨hz, hthr, hX1, hwX, hD, hα, hβ⟩

theorem e_tail_bound (N : ℕ) (IL z : ℂ) (w : ℝ) (hw : 0 < w) (hwX : w ≤ 2 * ‖z‖) :
    w ^ (N + 1) * ‖IL / (2 * Complex.I * z) ^ (N + 1)‖ ≤ ‖IL‖ := by
  have hX : 0 < 2 * ‖z‖ := lt_of_lt_of_le hw hwX
  have e1 : w ^ (N + 1) * ‖IL / (2 * Complex.I * z) ^ (N + 1)‖ = (w / (2 * ‖z‖)) ^ (N + 1) * ‖IL‖ := by
    rw [norm_div, norm_pow, norm_mul, norm_mul, Complex.norm_I, Complex.norm_ofNat, mul_one, div_pow]
    field_simp
  rw [e1]
  have hr0 : 0 ≤ w / (2 * ‖z‖) := div_nonneg hw.le hX.le
  have hr1 : w / (2 * ‖z‖) ≤ 1 := by rw [div_le_one hX]; exact hwX
  have := mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1 : (w / (2 * ‖z‖)) ^ (N + 1) ≤ 1) (norm_nonneg IL)
  linarith

theorem ab_tail_bound (S w X : ℝ) (α : ℂ) (hS : 0 ≤ S) (hw : 0 < w) (hwX : w ≤ 2 * X)
    (hα : ‖α‖ ≤ S / (2 * X)) : w ^ 1 * ‖α‖ ≤ S := by
  have hX : 0 < 2 * X := lt_of_lt_of_le hw hwX
  rw [pow_one]
  calc w * ‖α‖ ≤ w * (S / (2 * X)) := mul_le_mul_of_nonneg_left hα hw.le
    _ ≤ S := by
      rw [mul_div_assoc', div_le_iff₀ hX]
      nlinarith

/-! ### One endpoint (conditional on the KSPS-011/012/013/014/015 head conclusions for xi) -/

theorem endpoint_side_of
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (upper : Bool) (xi : ℤ → ℂ)
    (hxe : ∀ n, (if upper then periodicPlus φ n else periodicMinus φ n) = xi n)
    (a : ℝ) (ha : 0 ≤ a)
    (hxi : ∀ n : ℤ, ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n)
    (h11 : ∃ eLower eUpper : ℤ → ℂ,
      SquareSummable eLower ∧ SquareSummable eUpper ∧
      ∀ n : ℤ,
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderLower N φ xi n =
          Complex.I * ((-1 : ℂ) ^ (n + 1)) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.2) n +
            eLower n / indexValue n ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointRemainderUpper N φ xi n =
          Complex.I * ((-1 : ℂ) ^ n) *
            NlsGge.Pilot.physicalFourier
              (NlsGge.ThirdConsultation.KSPS.iteratedDerivative N φ.1) (-n) +
            eUpper n / indexValue n)
    (h12 : ∃ e1 e2 : ℤ → ℂ,
      SquareSummable e1 ∧ SquareSummable e2 ∧
      ∀ n : ℤ,
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ))
    (h13 : ∀ k : ℕ, (1 ≤ k ∧ k ≤ N + 1) → integralRiccatiLeft φ k = integralRiccatiRight φ k)
    (h14 : ∀ lam : {z : ℂ // z ≠ 0}, WKBThreshold N (sobolevNorm N φ) lam.1 →
      monodromyPair (toPotPair φ) lam.1 = KSPSWKB.explicitWKBMonodromy N φ lam)
    (h15 : WeightedL2Error ((N + 1 : ℕ) : ℝ)
      (fun n : ℤ => NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) -
        2 * Complex.cos (NlsGge.ThirdConsultation.KSPS.wkbPhase φ (xi n))))
    (hroot : ∀ n : ℤ, NlsGge.ThirdConsultation.KSPS.discriminant φ (xi n) ^ 2 = 4) :
    ∃ h : ℤ → ℂ, Summable (fun n : ℤ => indexWeight n ^ (2 * N + 1) * ‖h n‖) ∧
      ∀ᶠ n : ℤ in cofinite, ∃ hz : xi n ≠ 0, KSPSWKB.endpointQuadraticAt N φ n ⟨xi n, hz⟩ (h n) := by
  have hw : ∀ n : ℤ, 1 ≤ indexWeight n := one_le_indexWeight'
  have hw0 : ∀ n : ℤ, 0 < indexWeight n := fun n => lt_of_lt_of_le one_pos (hw n)
  set n0 : ℕ := ⌈a⌉₊ + ⌈NlsGge.ThirdConsultation.KSPSVolterra.threshold N (sobolevNorm N φ)⌉₊ + 1 with hn0
  have htail := eventually_natAbs n0
  -- the basic sequences
  obtain ⟨e, he⟩ : ∃ e : ℤ → ℂ, e = fun n => integralRiccatiLeft φ (N + 1) / (2 * Complex.I * xi n) ^ (N + 1) :=
    ⟨_, rfl⟩
  obtain ⟨a1, ha1⟩ : ∃ a1 : ℤ → ℂ, a1 = fun n => physicalFourier (toPotPair φ).1 (-n) := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a2 : ℤ → ℂ, a2 = fun n => physicalFourier (toPotPair φ).2 n := ⟨_, rfl⟩
  obtain ⟨al, hal⟩ : ∃ al : ℤ → ℂ, al = fun n => KSPSWKB.alpha φ (xi n) 0 := ⟨_, rfl⟩
  obtain ⟨be, hbe⟩ : ∃ be : ℤ → ℂ, be = fun n => KSPSWKB.beta φ (xi n) 0 := ⟨_, rfl⟩
  obtain ⟨E00, hE00⟩ : ∃ E : ℤ → ℂ, E = KSPSWKB.endpointEntryError N φ upper 0 0 := ⟨_, rfl⟩
  obtain ⟨E01, hE01⟩ : ∃ E : ℤ → ℂ, E = KSPSWKB.endpointEntryError N φ upper 0 1 := ⟨_, rfl⟩
  obtain ⟨E10, hE10⟩ : ∃ E : ℤ → ℂ, E = KSPSWKB.endpointEntryError N φ upper 1 0 := ⟨_, rfl⟩
  obtain ⟨E11, hE11⟩ : ∃ E : ℤ → ℂ, E = KSPSWKB.endpointEntryError N φ upper 1 1 := ⟨_, rfl⟩
  -- classes
  have cE : ∀ i j : Fin 2, WL2 indexWeight (N + 1) (KSPSWKB.endpointEntryError N φ upper i j) := fun i j =>
    (weightedL2Error_iff N _).1 (entry_errors_of N hN φ upper xi hxe a ha hxi h11 h12 h13 i j)
  have c00 : WL2 indexWeight (N + 1) E00 := by rw [hE00]; exact cE 0 0
  have c01 : WL2 indexWeight (N + 1) E01 := by rw [hE01]; exact cE 0 1
  have c10 : WL2 indexWeight (N + 1) E10 := by rw [hE10]; exact cE 1 0
  have c11 : WL2 indexWeight (N + 1) E11 := by rw [hE11]; exact cE 1 1
  -- r_ij = lead_ij + E_ij off the zero set
  have hsec : ∀ n : ℤ, ∀ hz : xi n ≠ 0,
      KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 0 = e n + E00 n ∧
      KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 0 1 = Complex.I * a1 n + E01 n ∧
      KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 0 = -Complex.I * a2 n + E10 n ∧
      KSPSWKB.scaledEndpointCorrection N φ n ⟨xi n, hz⟩ 1 1 = -e n + E11 n := by
    intro n hz
    have q00 := entryError_eq φ upper xi hxe 0 0 n hz
    have q01 := entryError_eq φ upper xi hxe 0 1 n hz
    have q10 := entryError_eq φ upper xi hxe 1 0 n hz
    have q11 := entryError_eq φ upper xi hxe 1 1 n hz
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at q00 q01 q10 q11
    subst he ha1 ha2 hE00 hE01 hE10 hE11
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [q00]; ring
    · rw [q01]; ring
    · rw [q10]; ring
    · rw [q11]; ring
  have hiw : Summable (fun n : ℤ => (1 / indexWeight n) ^ 2) := sq_summable_inv_w
  have hF1 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.1) (-n)‖ ^ 2) :=
    (hasSum_physicalFourier_sq (iteratedDerivative N φ.1)).summable.comp_injective neg_injective
  have hF2 : Summable (fun n : ℤ => ‖physicalFourier (iteratedDerivative N φ.2) n‖ ^ 2) :=
    (hasSum_physicalFourier_sq _).summable
  have ca1 : WL2 indexWeight N a1 := by
    refine summable_of_le_ev hw hF1 (fun n => sq_nonneg _) ?_
    filter_upwards [eventually_natAbs 1] with n hn
    have hν1 : (1 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
    rw [ha1]
    exact pow_le_pow_left₀ (wt_nonneg hw N n _) (fourier_facts φ n hν1).2.2.1 2
  have ca2 : WL2 indexWeight N a2 := by
    refine summable_of_le_ev hw hF2 (fun n => sq_nonneg _) ?_
    filter_upwards [eventually_natAbs 1] with n hn
    have hν1 : (1 : ℝ) ≤ |(n : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hn
    rw [ha2]
    exact pow_le_pow_left₀ (wt_nonneg hw N n _) (fourier_facts φ n hν1).2.2.2 2
  have ce : WBd indexWeight (N + 1) e := by
    refine ⟨‖integralRiccatiLeft φ (N + 1)‖, ?_⟩
    filter_upwards [htail] with n hn
    obtain ⟨_, _, _, hwX, _, _, _⟩ := tail_pack φ xi a ha hxi n hn
    rw [he]
    exact e_tail_bound N _ _ _ (hw0 n) hwX
  have cal : WBd indexWeight 1 al := by
    refine ⟨Sb φ, ?_⟩
    filter_upwards [htail] with n hn
    obtain ⟨_, _, _, hwX, _, hα, _⟩ := tail_pack φ xi a ha hxi n hn
    rw [hal]
    exact ab_tail_bound _ _ _ _ (Sb_nonneg φ) (hw0 n) hwX hα
  have cbe : WBd indexWeight 1 be := by
    refine ⟨Sb φ, ?_⟩
    filter_upwards [htail] with n hn
    obtain ⟨_, _, _, hwX, _, _, hβ⟩ := tail_pack φ xi a ha hxi n hn
    rw [hbe]
    exact ab_tail_bound _ _ _ _ (Sb_nonneg φ) (hw0 n) hwX hβ
  have ce2 : WL2 indexWeight N e := WBd.succ_WL2 hw hiw ce
  have cal2 : WL2 indexWeight 0 al := WBd.succ_WL2 hw hiw cal
  have cbe2 : WL2 indexWeight 0 be := WBd.succ_WL2 hw hiw cbe
  -- the four corrections r_ij = lead_ij + E_ij
  have cR00 : WL2 indexWeight N (fun n => e n + E00 n) := WL2.add hw ce2 (c00.mono hw (Nat.le_succ N))
  have cR11 : WL2 indexWeight N (fun n => -e n + E11 n) :=
    WL2.add hw ((WL2.const_mul hw (-1) ce2).congr hw (Eventually.of_forall fun n => by ring))
      (c11.mono hw (Nat.le_succ N))
  have cR01 : WL2 indexWeight N (fun n => Complex.I * a1 n + E01 n) :=
    WL2.add hw (WL2.const_mul hw Complex.I ca1) (c01.mono hw (Nat.le_succ N))
  have cR10 : WL2 indexWeight N (fun n => -Complex.I * a2 n + E10 n) :=
    WL2.add hw (WL2.const_mul hw (-Complex.I) ca2) (c10.mono hw (Nat.le_succ N))
  have bR00 : WBd indexWeight (N + 1) (fun n => e n + E00 n) := WBd.add hw ce (c00.bd hw)
  have bR11 : WBd indexWeight (N + 1) (fun n => -e n + E11 n) :=
    WBd.add hw ((WBd.const_mul hw (-1) ce).congr hw (Eventually.of_forall fun n => by ring)) (c11.bd hw)
  -- P = r00 r11 - r01 r10
  have cP : WL1 indexWeight (2 * N) (fun n => (e n + E00 n) * (-e n + E11 n) -
      (Complex.I * a1 n + E01 n) * (-Complex.I * a2 n + E10 n)) :=
    WL1.sub hw (WL2.mul hw cR00 cR11 (by ring)) (WL2.mul hw cR01 cR10 (by ring))
  have bP : WBd indexWeight 1 (fun n => (e n + E00 n) * (-e n + E11 n) -
      (Complex.I * a1 n + E01 n) * (-Complex.I * a2 n + E10 n)) := by
    have b1 : WBd indexWeight (2 * N) (fun n => (e n + E00 n) * (-e n + E11 n)) :=
      WBd.mul hw (bR00.mono hw (Nat.le_succ N)) (bR11.mono hw (Nat.le_succ N)) (by ring)
    have b2 : WBd indexWeight (2 * N) (fun n => (Complex.I * a1 n + E01 n) * (-Complex.I * a2 n + E10 n)) :=
      WBd.mul hw (cR01.bd hw) (cR10.bd hw) (by ring)
    exact (WBd.sub hw b1 b2).mono hw (by omega)
  -- the six terms
  have T1 : WL1 indexWeight (2 * N + 1) (fun n => 4 * (e n * (al n * (Complex.I * a1 n + E01 n) -
      be n * (-Complex.I * a2 n + E10 n)))) := by
    have y : WL1 indexWeight N (fun n => al n * (Complex.I * a1 n + E01 n) -
        be n * (-Complex.I * a2 n + E10 n)) :=
      WL1.sub hw (WL2.mul hw cal2 cR01 (by ring)) (WL2.mul hw cbe2 cR10 (by ring))
    exact WL1.const_mul hw 4 (WBd.mul_WL1 hw ce y (by ring))
  have cX : WL2 indexWeight (N + 1) (fun n => E00 n - E11 n - be n * (-Complex.I * a2 n + E10 n) +
      al n * (Complex.I * a1 n + E01 n)) := by
    have x1 : WL2 indexWeight (N + 1) (fun n => be n * (-Complex.I * a2 n + E10 n)) :=
      WBd.mul_WL2 hw cbe cR10 (by ring)
    have x2 : WL2 indexWeight (N + 1) (fun n => al n * (Complex.I * a1 n + E01 n)) :=
      WBd.mul_WL2 hw cal cR01 (by ring)
    exact WL2.add hw (WL2.sub hw (WL2.sub hw c00 c11) x1) x2
  have T2 : WL1 indexWeight (2 * N + 1) (fun n =>
      (E00 n - E11 n - be n * (-Complex.I * a2 n + E10 n) + al n * (Complex.I * a1 n + E01 n)) *
      (E00 n - E11 n - be n * (-Complex.I * a2 n + E10 n) + al n * (Complex.I * a1 n + E01 n))) :=
    (WL2.mul hw cX cX (rfl : N + 1 + (N + 1) = N + 1 + (N + 1))).mono hw (by omega)
  have T3 : WL1 indexWeight (2 * N + 1) (fun n => 4 * (E00 n * E11 n - Complex.I * (a1 n * E10 n) +
      Complex.I * (a2 n * E01 n) - E01 n * E10 n)) := by
    have u1 : WL1 indexWeight (2 * N + 1) (fun n => E00 n * E11 n) :=
      (WL2.mul hw c00 c11 (rfl : N + 1 + (N + 1) = N + 1 + (N + 1))).mono hw (by omega)
    have u2 : WL1 indexWeight (2 * N + 1) (fun n => Complex.I * (a1 n * E10 n)) :=
      WL1.const_mul hw Complex.I (WL2.mul hw ca1 c10 (by ring))
    have u3 : WL1 indexWeight (2 * N + 1) (fun n => Complex.I * (a2 n * E01 n)) :=
      WL1.const_mul hw Complex.I (WL2.mul hw ca2 c01 (by ring))
    have u4 : WL1 indexWeight (2 * N + 1) (fun n => E01 n * E10 n) :=
      (WL2.mul hw c01 c10 (rfl : N + 1 + (N + 1) = N + 1 + (N + 1))).mono hw (by omega)
    exact WL1.const_mul hw 4 (WL1.sub hw (WL1.add hw (WL1.sub hw u1 u2) u3) u4)
  have T4 : WL1 indexWeight (2 * N + 1) (fun n => 4 * ((al n * be n) *
      ((e n + E00 n) * (-e n + E11 n) - (Complex.I * a1 n + E01 n) * (-Complex.I * a2 n + E10 n)))) := by
    have b : WBd indexWeight 2 (fun n => al n * be n) := WBd.mul hw cal cbe (by ring)
    exact WL1.const_mul hw 4 ((WBd.mul_WL1 hw b cP (rfl : 2 + 2 * N = 2 + 2 * N)).mono hw (by omega))
  have T5 : WL1 indexWeight (2 * N + 1) (fun n => 2 * (((e n + E00 n) - be n * (-Complex.I * a2 n + E10 n) +
      ((-e n + E11 n) - al n * (Complex.I * a1 n + E01 n))) *
      ((e n + E00 n) * (-e n + E11 n) - (Complex.I * a1 n + E01 n) * (-Complex.I * a2 n + E10 n)))) := by
    have bA : WBd indexWeight 1 (fun n => (e n + E00 n) - be n * (-Complex.I * a2 n + E10 n)) := by
      have x : WBd indexWeight (1 + N) (fun n => be n * (-Complex.I * a2 n + E10 n)) :=
        WBd.mul hw cbe (cR10.bd hw) rfl
      exact WBd.sub hw (bR00.mono hw (by omega)) (x.mono hw (by omega))
    have bC : WBd indexWeight 1 (fun n => (-e n + E11 n) - al n * (Complex.I * a1 n + E01 n)) := by
      have x : WBd indexWeight (1 + N) (fun n => al n * (Complex.I * a1 n + E01 n)) :=
        WBd.mul hw cal (cR01.bd hw) rfl
      exact WBd.sub hw (bR11.mono hw (by omega)) (x.mono hw (by omega))
    exact WL1.const_mul hw 2 (WBd.mul_WL1 hw (WBd.add hw bA bC) cP (by ring))
  have T6 : WL1 indexWeight (2 * N + 1) (fun n =>
      ((e n + E00 n) * (-e n + E11 n) - (Complex.I * a1 n + E01 n) * (-Complex.I * a2 n + E10 n)) *
      ((e n + E00 n) * (-e n + E11 n) - (Complex.I * a1 n + E01 n) * (-Complex.I * a2 n + E10 n))) :=
    WBd.mul_WL1 hw bP cP (by ring)
  have hT := WL1.add hw (WL1.sub hw (WL1.sub hw (WL1.add hw (WL1.add hw T1 T2) T3) T4) T5) T6
  -- small coefficient perturbation in q0
  have cQ : WL2 indexWeight 0 (fun n => al n * be n + (e n + E00 n) - be n * (-Complex.I * a2 n + E10 n)) := by
    have q1 : WL2 indexWeight 0 (fun n => al n * be n) :=
      (WBd.succ_WL2 hw hiw (WBd.mul hw cal cbe (rfl : 1 + 1 = 1 + 1))).mono hw (Nat.zero_le _)
    have q3 : WL2 indexWeight 0 (fun n => be n * (-Complex.I * a2 n + E10 n)) :=
      (WBd.mul_WL2 hw cbe cR10 rfl).mono hw (Nat.zero_le _)
    exact WL2.sub hw (WL2.add hw q1 (cR00.mono hw (Nat.zero_le _))) q3
  have hsmall := cQ.eventually_le hw (1 / 2) (by norm_num)
  -- the sign of the discriminant
  have hsign := disc_sign_eventually N φ xi a ha hxi hroot h15
  -- the radicand error sequence
  refine ⟨fun n => if hz : xi n = 0 then 0 else
      (KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 1) ^ 2 -
        4 * KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 0 * KSPSWKB.endpointQuadraticABC N φ n ⟨xi n, hz⟩ 2 +
        4 * physicalFourier (toPotPair φ).1 (-n) * physicalFourier (toPotPair φ).2 n, ?_, ?_⟩
  · -- weighted l1
    refine WL1.congr hw hT ?_
    filter_upwards [htail] with n hn
    obtain ⟨hz, _, _, _, _, _, _⟩ := tail_pack φ xi a ha hxi n hn
    obtain ⟨s00, s01, s10, s11⟩ := hsec n hz
    have pa1 : physicalFourier (toPotPair φ).1 (-n) = a1 n := by rw [ha1]
    have pa2 : physicalFourier (toPotPair φ).2 n = a2 n := by rw [ha2]
    have pal : KSPSWKB.alpha φ (xi n) 0 = al n := by rw [hal]
    have pbe : KSPSWKB.beta φ (xi n) 0 = be n := by rw [hbe]
    beta_reduce
    rw [dif_neg hz, (abc_apply φ n (xi n) hz).1, (abc_apply φ n (xi n) hz).2.1, (abc_apply φ n (xi n) hz).2.2,
      s00, s01, s10, s11, pa1, pa2, pal, pbe]
    linear_combination (-(4 * a1 n * a2 n)) * Complex.I_sq
  · filter_upwards [htail, hsmall, hsign] with n hn hQ hsg
    obtain ⟨hz, hthr, _, _, hD, _, _⟩ := tail_pack φ xi a ha hxi n hn
    obtain ⟨s00, s01, s10, s11⟩ := hsec n hz
    have pal : KSPSWKB.alpha φ (xi n) 0 = al n := by rw [hal]
    have pbe : KSPSWKB.beta φ (xi n) 0 = be n := by rw [hbe]
    refine ⟨hz, ?_⟩
    dsimp only [KSPSWKB.endpointQuadraticAt]
    refine ⟨?_, ?_, ?_⟩
    · rw [(abc_apply φ n (xi n) hz).1, s00, s10, pal, pbe]
      intro h0
      have e1 : al n * be n + (e n + E00 n) - be n * (-Complex.I * a2 n + E10 n) = 1 := by
        linear_combination h0
      simp only [pow_zero, one_mul] at hQ
      rw [e1, norm_one] at hQ
      norm_num at hQ
    · exact quad_zero_at φ n ⟨xi n, hz⟩ h13 (h14 _ hthr) hD hsg
    · rw [dif_neg hz]
      ring
end
end NlsGge.ThirdConsultation.KSPS026W
