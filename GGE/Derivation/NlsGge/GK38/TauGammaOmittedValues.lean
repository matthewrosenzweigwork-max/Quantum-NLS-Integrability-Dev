import NlsGge.GK38.TauGammaSincBounds

/-! Accepted single omitted-product L2 errors give a common paired error bound. -/
set_option autoImplicit false
open Filter Topology Set Metric
namespace NlsGge.GK38
noncomputable section

theorem norm_product_sub_square_le38 (a b s : ℂ) (A B E : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (ha : ‖a - s‖ ≤ A) (hb : ‖b - s‖ ≤ B) (hs : ‖s‖ ≤ E) :
    ‖a * b - s ^ 2‖ ≤ A * B + E * (A + B) := by
  have he : a * b - s ^ 2 = (a - s) * (b - s) + s * ((a - s) + (b - s)) := by ring
  rw [he]
  calc
    _ ≤ ‖(a - s) * (b - s)‖ + ‖s * ((a - s) + (b - s))‖ := norm_add_le _ _
    _ ≤ ‖a - s‖ * ‖b - s‖ + ‖s‖ * (‖a - s‖ + ‖b - s‖) := by
      rw [norm_mul, norm_mul]
      gcongr
      exact norm_add_le _ _
    _ ≤ A * B + E * (A + B) := by gcongr

theorem paired_omit_value_majorant38 (K : ℝ) (hK : 0 ≤ K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ sp sm : Lib.L2Seq, ‖sp‖ ≤ K → ‖sm‖ ≤ K →
      ∃ b : ℤ → ℝ, (∀ n : ℤ, 0 ≤ b n ∧ ∀ z ∈ Lib.Dn n,
        ‖Lib.omitProd n sp z * Lib.omitProd n sm z - (Lib.sincAt n z) ^ 2‖ ≤ b n) ∧
        Summable (fun n => b n ^ 2) ∧ (∑' n : ℤ, b n ^ 2) ≤ B := by
  obtain ⟨C, hC⟩ := Lib.omitProd_asymp K
  let T := max C 0
  let S := T + 1
  let E := Real.exp (Real.pi / 4)
  let L := S + E
  have hT : 0 ≤ T := le_max_right C 0
  have hE : 0 < E := Real.exp_pos _
  have hL : 0 < L := by dsimp [L, S]; linarith
  refine ⟨4 * L ^ 2 * T, by positivity, fun sp sm hsp hsm => ?_⟩
  obtain ⟨bp, hp, hps, hpB⟩ := hC sp hsp
  obtain ⟨bm, hm, hms, hmB⟩ := hC sm hsm
  have hcenter (n : ℤ) : (n : ℂ) * (Real.pi : ℂ) ∈ Lib.Dn n := by
    exact mem_ball_self (by positivity)
  have hp0 (n : ℤ) : 0 ≤ bp n := (norm_nonneg _).trans (hp n _ (hcenter n))
  have hm0 (n : ℤ) : 0 ≤ bm n := (norm_nonneg _).trans (hm n _ (hcenter n))
  have hpT (n : ℤ) : bp n ^ 2 ≤ T := by
    have ht := hps.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => sq_nonneg _)
    have hpoint : bp n ^ 2 ≤ ∑' m : ℤ, bp m ^ 2 := by simpa only [Finset.sum_singleton] using ht
    exact hpoint.trans (hpB.trans (le_max_left C 0))
  have hmT (n : ℤ) : bm n ^ 2 ≤ T := by
    have ht := hms.sum_le_tsum ({n} : Finset ℤ) (fun _ _ => sq_nonneg _)
    have hpoint : bm n ^ 2 ≤ ∑' m : ℤ, bm m ^ 2 := by simpa only [Finset.sum_singleton] using ht
    exact hpoint.trans (hmB.trans (le_max_left C 0))
  have hpS (n : ℤ) : bp n ≤ S := by dsimp [S]; nlinarith [hpT n, hp0 n, sq_nonneg T]
  let b : ℤ → ℝ := fun n => L * (bp n + bm n)
  have hdom (n : ℤ) : b n ^ 2 ≤ 2 * L ^ 2 * (bp n ^ 2 + bm n ^ 2) := by
    dsimp [b]
    nlinarith [mul_nonneg (sq_nonneg L) (sq_nonneg (bp n - bm n))]
  have hsdom := (hps.add hms).mul_left (2 * L ^ 2)
  have hbs := hsdom.of_nonneg_of_le (fun _ => sq_nonneg _) hdom
  refine ⟨b, fun n => ⟨mul_nonneg hL.le (add_nonneg (hp0 n) (hm0 n)), fun z hz => ?_⟩,
    hbs, ?_⟩
  · have hh := norm_product_sub_square_le38 (Lib.omitProd n sp z) (Lib.omitProd n sm z)
      (Lib.sincAt n z) (bp n) (bm n) E (hp0 n) (hm0 n) hE.le
      (hp n z hz) (hm n z hz) (Lib.norm_sincAt_le n hz)
    apply hh.trans
    have hpMul := mul_le_mul_of_nonneg_right (hpS n) (hm0 n)
    dsimp [b, L]
    nlinarith [mul_nonneg (by dsimp [S]; linarith : 0 ≤ S) (hp0 n)]
  · apply (hbs.tsum_le_tsum hdom hsdom).trans
    rw [tsum_mul_left, hps.tsum_add hms]
    have hpC : (∑' n : ℤ, bp n ^ 2) ≤ T := hpB.trans (le_max_left C 0)
    have hmC : (∑' n : ℤ, bm n ^ 2) ≤ T := hmB.trans (le_max_left C 0)
    nlinarith [sq_nonneg L]

end
end NlsGge.GK38
