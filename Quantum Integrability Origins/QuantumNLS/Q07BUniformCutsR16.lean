import QuantumNLS.Q07WindowHessiansR16
import QuantumNLS.Q07ContourMeasureR16
import QuantumNLS.Q07UniformCutsR16

/-! R-B90ACAE9 / lem:Q07Buniformcuts, assembled for the actual physical
transfer, full-mass window Hamiltonian and full real Hilbert differentials.
The Sobolev scope s>0 includes the printed smooth integer s≥1 class. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Metric Filter Topology MeasureTheory
namespace QuantumNLS.Q07BUniformCutsR16
open PhysicalTensor (L2T)
open Q07IntegratedHessiansR16 (windowContour)
open Q07SobolevCutsR16 (sobolevClass)
open PROP017UniformN (cutSeq)
variable {L κ : ℝ} [Fact (0 < L)]

/-- The printed uniform cuts and contour differential theorem, including
identification with the actual full-mass moment over the spectral window.
All application hypotheses are the physical source parameters. -/
theorem q07Buniformcuts (hκ : 0 < κ) {s : ℝ} (hs : 0 < s) (B : ℝ)
    {h : ℝ} (hh : 0 < h) (r : ℕ) :
    (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in cocompact ℝ,
      ∀ u ∈ sobolevClass (L := L) s B, ∀ y : ℝ, |y| ≤ h →
        ‖NormalizedTransfer.productSymbol L κ u (Q07StripInteractionR16.spectral t y)-1-
          Complex.exp (Complex.I*Q07StripInteractionR16.spectral t y*L)‖ < ε) ∧
    ∃ η : ℝ, 0 < η ∧ ∃ l0 : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ l : ℕ, l0 ≤ l → 1 ≤ cutSeq L l ∧
        ∀ u ∈ sobolevClass (L := L) s B, ∀ v : L2T L, ‖v-u‖ < η →
          (∀ a : ℝ, (a = cutSeq L l ∨ a = -cutSeq L l) →
            (∀ t : ℝ, |t| < 1/L → |PhysicalL2BandGeometry.d (κ := κ) v (a+t)| < 3/2) ∧
            FullMass.Mmeas κ v (Ioo (a-1/L) (a+1/L)) = 0) ∧
          windowContour hκ r (cutSeq L l) h v =
            (∫ t in Ioo (-cutSeq L l) (cutSeq L l), t^r ∂FullMass.Mmeas κ v) ∧
          DifferentiableAt ℝ (windowContour hκ r (cutSeq L l) h) v ∧
          DifferentiableAt ℝ (fderiv ℝ (windowContour hκ r (cutSeq L l) h)) v ∧
          ∀ w q : L2T L,
            |((fderiv ℝ (fderiv ℝ (windowContour hκ r (cutSeq L l) h)) v) w) q| ≤
              C*(cutSeq L l)^(r+1)*‖w‖*‖q‖ := by
  obtain ⟨hstrip,η1,hη1,l1,C1,d,hC1,hd,hdata⟩ :=
    Q07UniformCutsR16.q07_uniform_analytic_data (L := L) hκ hs B hh
  obtain ⟨η2,hη2,l2,C,hC,hH⟩ := Q07WindowHessiansR16.uniform_window_hessians (L := L) hκ hs B hh r
  refine ⟨hstrip,min η1 η2,lt_min hη1 hη2,max l1 l2,C,hC,?_⟩
  intro l hl
  have hl1 := (le_max_left l1 l2).trans hl
  have hl2 := (le_max_right l1 l2).trans hl
  obtain ⟨ha,hHs⟩ := hH l hl2
  refine ⟨ha,?_⟩
  intro u hu v hv
  obtain ⟨hcuts,-⟩ := hdata l hl1 u hu v (hv.trans_le (min_le_left _ _))
  obtain ⟨hD1,hD2,hbound⟩ := hHs u hu v (hv.trans_le (min_le_right _ _))
  refine ⟨hcuts,?_,hD1,hD2,hbound⟩
  have hg1 := Q07UniformGeometryR16.gap_ae hκ (hcuts (cutSeq L l) (Or.inl rfl)).2
  have hg2 := Q07UniformGeometryR16.gap_ae hκ (hcuts (-cutSeq L l) (Or.inr rfl)).2
  have hgap : ∀ᵐ t ∂(PhysicalQuantumMeasure.measure hκ v),
      1/L ≤ |t-cutSeq L l| ∧ 1/L ≤ |t+cutSeq L l| := by
    filter_upwards [hg1,hg2] with t ht1 ht2
    exact ⟨ht1,by simpa only [sub_neg_eq_add] using ht2⟩
  have hm := Q07ContourMeasureR16.contour_measure (PhysicalQuantumMeasure.measure hκ v)
    hκ (zero_le_one.trans ha) hh (one_div_pos.mpr (Fact.out : 0 < L)) r hgap
  change windowContour hκ r (cutSeq L l) h v =
    (∫ t in Ioo (-cutSeq L l) (cutSeq L l), t^r ∂PhysicalQuantumMeasure.measure hκ v) at hm
  exact hm.trans (by rw [PhysicalL2Normalization.measure_eq_Mmeas hκ v])

end QuantumNLS.Q07BUniformCutsR16
