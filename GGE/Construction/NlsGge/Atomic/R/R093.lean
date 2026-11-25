
import NlsGge.Composition.Main

set_option autoImplicit false
noncomputable section
open scoped ENNReal BigOperators
open NlsGge.Composition
open AddCircle
open scoped NNReal

namespace NlsGge.ThirdConsultation.R

def LocalModelPowerSeries
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (w : ℤ → ℝ) (hw : NlsGge.Composition.AdmissibleWeight w)
    (F : X → Y) (g p : NlsGge.Composition.Model X)
    (P : FormalMultilinearSeries ℝ
      (NlsGge.Composition.Model X) (NlsGge.Composition.Model Y))
    (A q R : ℝ) : Prop :=
  0 ≤ A ∧ 0 ≤ q ∧ 0 < R ∧ q * R ≤ 1 ∧ ‖g - p‖ < R ∧
  (∃ S : Finset ℤ, p = NlsGge.Composition.truncate S g) ∧
  (∃ ρ : ℝ, 0 < ρ ∧
    q = 2 * NlsGge.Composition.prodConst hw / ρ ∧
    NlsGge.Composition.supConst w * R < ρ) ∧
  (∀ k : ℕ, ‖P k‖ ≤ A * q ^ k) ∧
  HasFPowerSeriesOnBall (NlsGge.Composition.compMap hw F)
    P p (ENNReal.ofReal R) ∧
  ∀ r : NlsGge.Composition.Model X, ‖r‖ < R →
    q * ‖r‖ < 1 ∧
    Summable (fun k : ℕ => ‖P k (fun _ : Fin k => r)‖) ∧
    HasSum (fun k : ℕ => P k (fun _ : Fin k => r))
      (NlsGge.Composition.compMap hw F (p + r)) ∧
    ∀ θ : AddCircle (1 : ℝ),
      HasSum
        (fun k : ℕ =>
          NlsGge.Composition.synth w (P k (fun _ : Fin k => r)) θ)
        (F (NlsGge.Composition.synth w (p + r) θ)) ∧
      NlsGge.Composition.synth w
        (∑' k : ℕ, P k (fun _ : Fin k => r)) θ =
          F (NlsGge.Composition.synth w (p + r) θ)

theorem exists_local_expansion
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    (w : ℤ → ℝ) (hw : NlsGge.Composition.AdmissibleWeight w)
    (F : X → Y) (O : Set X) (hO : IsOpen O)
    (hF : AnalyticOnNhd ℝ F O)
    (g : NlsGge.Composition.Model X)
    (hg : g ∈ NlsGge.Composition.rangeSet w O) :
    ∃ (p : NlsGge.Composition.Model X)
      (P : FormalMultilinearSeries ℝ
        (NlsGge.Composition.Model X) (NlsGge.Composition.Model Y))
      (A q R : ℝ), LocalModelPowerSeries w hw F g p P A q R := by
  classical
  -- Step 1: compact range and uniform data
  set K := Set.range (synth w g) with hKdef
  have hK : IsCompact K := isCompact_range_synth hw g
  have hKO : K ⊆ O := by rintro _ ⟨θ, rfl⟩; exact hg θ
  obtain ⟨δ, ρ, M, hδ, hρ, hM, _hsub, hdata⟩ := exists_uniform_series_bounds hO hF hK hKO
  -- constants independent of the approximant
  set Sw := supConst w with hSw
  have hSw0 : 0 ≤ Sw := supConst_nonneg w
  set Cw := prodConst hw with hCw
  have hCw0 : 0 ≤ Cw := prodConst_nonneg hw
  set q : ℝ := Cw * (2 / ρ) with hq
  have hq0 : 0 ≤ q := by positivity
  set R : ℝ := min (1 / (q + 1)) (ρ / (Sw + 1)) with hR
  have hRpos : 0 < R := lt_min (by positivity) (by positivity)
  have hqR : q * R ≤ 1 := by
    calc q * R ≤ q * (1 / (q + 1)) := by gcongr; exact min_le_left _ _
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by linarith)]; linarith
  have hSR : Sw * R < ρ := by
    calc Sw * R ≤ Sw * (ρ / (Sw + 1)) := by gcongr; exact min_le_right _ _
      _ < ρ := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  -- Step 2: the trigonometric approximant
  set ε : ℝ := min (R / 2) (δ / (Sw + 1)) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  obtain ⟨Sset, hSset⟩ := exists_truncate_near g hεpos
  set p := truncate Sset g with hp
  have hpR : ‖g - p‖ < R := lt_of_lt_of_le hSset ((min_le_left _ _).trans (by linarith))
  have hpδ : Sw * ‖p - g‖ < δ := by
    rw [norm_sub_rev]
    calc Sw * ‖g - p‖ ≤ Sw * (δ / (Sw + 1)) := by
          gcongr; exact hSset.le.trans (min_le_right _ _)
      _ < δ := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  set v : ℤ → X := coeff w g with hv
  have hpsynth : ∀ θ, synth w p θ = ∑ n ∈ Sset, fourier n θ • v n := fun θ =>
    synth_truncate Sset g θ
  have hγ : ∀ θ : AddCircle (1 : ℝ), (∑ n ∈ Sset, fourier n θ • v n) ∈ Metric.thickening δ K := by
    intro θ
    rw [← hpsynth]
    exact synth_mem_thickening hw hpδ θ
  -- Step 3: Taylor coefficients in `A_w`
  obtain ⟨D, hD0, hB⟩ := taylorFun_memAw hw hδ hρ hM hdata Sset v hγ
  set Bk : (k : ℕ) → Model (ContinuousMultilinearMap ℝ (fun _ : Fin k => X) Y) :=
    fun k => toModel hw (hB k).1 with hBk
  have hBk_norm : ∀ k, ‖Bk k‖ ≤ 2 * M * (2 / ρ) ^ k * D := fun k => by
    simp only [hBk]; rw [norm_toModel]; exact (hB k).2
  have hBk_synth : ∀ k θ, synth w (Bk k) θ = taylorFun F Sset v k θ := fun k θ => by
    simp only [hBk]; rw [synth_toModel]
  -- Step 4: the formal series on the model
  set P : FormalMultilinearSeries ℝ (Model X) (Model Y) := fun k => multCLM hw k (Bk k) with hP
  have hPbound : ∀ k : ℕ, ‖P k‖ ≤ 2 * M * D * q ^ k := by
    intro k
    have h1 := (multCLM hw k (X := X) (Y := Y)).le_opNorm (Bk k)
    have h2 := norm_multCLM_le hw k (X := X) (Y := Y)
    have h3 := hBk_norm k
    have hn0 : 0 ≤ ‖Bk k‖ := norm_nonneg _
    calc ‖P k‖ ≤ Cw ^ k * (2 * M * (2 / ρ) ^ k * D) :=
          h1.trans (mul_le_mul h2 h3 hn0 (by positivity))

      _ = 2 * M * D * q ^ k := by rw [hq, mul_pow]; ring
  have hpt : ∀ r : NlsGge.Composition.Model X, ‖r‖ < R → ∀ θ : AddCircle (1 : ℝ),
      HasSum (fun k : ℕ => synth w (P k (fun _ => r)) θ) (F (synth w (p + r) θ)) := by
    intro r hr θ
    have hy : synth w p θ ∈ Metric.thickening δ K := by rw [hpsynth]; exact hγ θ
    obtain ⟨pser, hpser, -⟩ := hdata _ hy
    have hz : synth w r θ ∈ Metric.eball (0 : X) (ENNReal.ofReal ρ) := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hρ]
      calc ‖synth w r θ‖ ≤ Sw * ‖r‖ := norm_synth_le hw r θ
        _ ≤ Sw * R := by gcongr
        _ < ρ := hSR
    have hsum := hpser.hasSum_iteratedFDeriv hz
    rw [synth_add hw]
    refine hsum.congr_fun fun k => ?_
    simp only [hP]
    rw [synth_multCLM, hBk_synth, taylorFun, ← hpsynth]
    rfl
  have hps := hasFPowerSeriesOnBall_compMap hw F p P (A := 2 * M * D) (by positivity) hq0 hRpos hqR hPbound hpt
  refine ⟨p, P, 2 * M * D, q, R, ?_⟩
  unfold LocalModelPowerSeries
  refine ⟨by positivity, hq0, hRpos, hqR, hpR, ⟨Sset, hp⟩, ⟨ρ, hρ, ?_, hSR⟩, hPbound, hps, ?_⟩
  · rw [hq, hCw]
    ring
  · intro r hr
    have hqr : q * ‖r‖ < 1 := by
      rcases eq_or_lt_of_le hq0 with h0 | h0
      · rw [← h0]; simp
      · calc q * ‖r‖ < q * R := mul_lt_mul_of_pos_left hr h0
          _ ≤ 1 := hqR
    have hsumN : Summable fun k : ℕ => ‖P k (fun _ => r)‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
        ((summable_geometric_of_lt_one (mul_nonneg hq0 (norm_nonneg r)) hqr).mul_left (2 * M * D))
      calc ‖P k (fun _ => r)‖ ≤ ‖P k‖ * ∏ _i : Fin k, ‖r‖ := (P k).le_opNorm _
        _ ≤ 2 * M * D * q ^ k * ‖r‖ ^ k := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            gcongr; exact hPbound k
        _ = 2 * M * D * (q * ‖r‖) ^ k := by ring
    have hrm : r ∈ Metric.eball (0 : NlsGge.Composition.Model X) (ENNReal.ofReal R) := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_ofReal_iff hRpos]
      exact hr
    have hG := hps.hasSum hrm
    have hsumY : Summable (fun k : ℕ => P k (fun _ => r)) := hsumN.of_norm
    refine ⟨hqr, hsumN, hG, fun θ => ⟨hpt r hr θ, ?_⟩⟩
    have hmap := (evalCLM hw θ).map_tsum hsumY
    simp only [evalCLM_apply] at hmap
    rw [hmap]
    exact (hpt r hr θ).tsum_eq

end NlsGge.ThirdConsultation.R

end
