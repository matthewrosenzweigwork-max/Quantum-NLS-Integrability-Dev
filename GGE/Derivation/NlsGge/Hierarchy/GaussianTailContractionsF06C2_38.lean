import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import Mathlib.Tactic

/-! Batch 38, F06-C2(b): `C:lem:contractions` (paper/v2.tex l.736-784) with the infinite Gaussian
tail, i.e. with `C_{m,N}` exactly as in `C:eq:correction` (l.738-741):
`C_{m,N}(v) = E[V_m(v + Y_N)] − V_m(v)`, `M(v) = ‖v‖₂²`, where

* `U ~ γ_m^F` is `gammaM38 m β = countableComplexGaussian (finiteHierarchyRate38 m β)` (rates
  `a_{m,n} = W_m(2πn)`), realized in `H^{m-1}` by `gaussianRealization38`;
* `Y_N = (Id − P_N) U` is `tailRealization38 m N` (`ae_tailRealization_eq_sub38`);
* `V_m` is the continuous local remainder on `H^{m-1}`, `localRemainderSobolev38 m β ∘ toCarrier38`;
* `v ∈ F_N` with Fourier coordinates `z` is the `H^{m-1}` element `planeElement38` whose
  coefficients are the Fourier coefficients of the smooth field `planeReal N z`
  (`planeElement_hsource38`); `M(v) = ‖planeL2 N z‖²`.

The finite-cutoff case is `contraction_finiteCutoff38` (F06-C1); the passage `N' → ∞` uses
dominated convergence with `|V_m(x)| ≤ C (1 + ‖x‖^{2m+2})`, `‖Y_{N,N'}‖ ≤ ‖Y_N‖` and finite
moments of `‖Y_N‖` (source remark l.757-758: "convergence of the continuous polynomial `V_m` in
every finite `L^p` on the Gaussian `H^{m-1}` space"). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace NlsGge.HierarchyRiccati.Core

open MeasureTheory NlsGge.Pilot NlsGge.Measure NlsGge.Sobolev38 Filter
open scoped ENNReal Topology ContDiff

section Fields

theorem planeReal_eq_tailField38 (N : ℕ) (z : FourierPlane N) :
    planeReal N z = tailField38 (modeIndex N) z := by
  funext x
  simp only [planeReal, planeField, tailField38, fourier_coe_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  push_cast
  ring

theorem tailField_append38 {K L : ℕ} (a : Fin K → ℤ) (b : Fin L → ℤ) (g : Fin K → ℂ)
    (h : Fin L → ℂ) (x : ℝ) :
    tailField38 (Fin.append a b) (Fin.append g h) x = tailField38 a g x + tailField38 b h x := by
  unfold tailField38
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem finiteSeq_append38 {K L : ℕ} (a : Fin K → ℤ) (b : Fin L → ℤ) (g : Fin K → ℂ)
    (h : Fin L → ℂ) (n : ℤ) :
    finiteSeq38 (Fin.append a b) (Fin.append g h) n = finiteSeq38 a g n + finiteSeq38 b h n := by
  unfold finiteSeq38
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem smoothFourier38_congr {u u' : ℝ → ℂ} (h : u = u') (hu : ContDiff ℝ ∞ u)
    (hper : Function.Periodic u 1) (hu' : ContDiff ℝ ∞ u') (hper' : Function.Periodic u' 1)
    (n : ℤ) : smoothFourier38 u hu hper n = smoothFourier38 u' hu' hper' n := by
  subst h
  rfl

theorem finiteElement_add_apply38 (r : ℝ) {K L : ℕ} (a : Fin K → ℤ) (b : Fin L → ℤ)
    (g : Fin K → ℂ) (h : Fin L → ℂ) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight r) from
      finiteElement38 r a g + finiteElement38 r b h) n =
      (show WeightedHilbert (sobolevModeWeight r) from finiteElement38 r a g) n +
      (show WeightedHilbert (sobolevModeWeight r) from finiteElement38 r b h) n :=
  rfl

theorem finiteElement_append38 (r : ℝ) {K L : ℕ} (a : Fin K → ℤ) (b : Fin L → ℤ)
    (g : Fin K → ℂ) (h : Fin L → ℂ) (hab : Function.Injective (Fin.append a b)) :
    finiteElement38 r (Fin.append a b) (Fin.append g h) =
      finiteElement38 r a g + finiteElement38 r b h := by
  obtain ⟨ha, hb, -⟩ := Fin.append_injective_iff.1 hab
  apply Subtype.ext
  funext n
  change (show WeightedHilbert (sobolevModeWeight r) from
      finiteElement38 r (Fin.append a b) (Fin.append g h)) n =
    (show WeightedHilbert (sobolevModeWeight r) from
      finiteElement38 r a g + finiteElement38 r b h) n
  rw [finiteElement_add_apply38, finiteElement_apply38 r _ _ hab n, finiteElement_apply38 r _ _ ha n,
    finiteElement_apply38 r _ _ hb n, finiteSeq_append38]

end Fields

section Remainder

/-- `V_m` on `H^{m-1}`: the continuous local remainder `localRemainderSobolev38` (F03). -/
def vSobolev38 (m : ℕ) (β : ℕ → ℝ) (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) : ℝ :=
  localRemainderSobolev38 m β (toCarrier38 _ x)

theorem continuous_vSobolev38 (m : ℕ) (β : ℕ → ℝ) : Continuous (vSobolev38 m β) :=
  (continuous_localRemainderSobolev38 m β).comp (continuous_toCarrier38 _)

theorem vSobolev38_bound (m : ℕ) (β : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |vSobolev38 m β x| ≤ C * (1 + ‖x‖ ^ (2 * m + 2)) := by
  obtain ⟨C, hC0, hC⟩ := localRemainderSobolev38_bound m β
  exact ⟨C, hC0, fun x => hC (toCarrier38 _ x)⟩

/-- Smooth identity: at the finite exponential sum `Σ_k g_k e_{ι k}`, `V_m` is the realized
remainder `vLocal38` of the smooth field `tailField38 ι g`. -/
theorem vSobolev_finiteElement38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) {K : ℕ} (ι : Fin K → ℤ)
    (hι : Function.Injective ι) (g : Fin K → ℂ) :
    vSobolev38 m β (finiteElement38 ((m - 1 : ℕ) : ℝ) ι g) = vLocal38 m β (tailField38 ι g) := by
  have hu : ContDiff ℝ ∞ (tailField38 ι g) := (contDiff_tailField38 ι g).of_le le_top
  have hper := tailField_periodic38 ι g
  unfold vSobolev38 localRemainderSobolev38 vLocal38
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  exact localRemainderCharge38_smooth m j hm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) _ hu
    hper _ (finiteElement_hsource38 _ ι g hι hu hper)

end Remainder

section Plane

/-- `v ∈ F_N` (Fourier coordinates `z`) as an element of `H^r`. -/
def planeElement38 (r : ℝ) (N : ℕ) (z : FourierPlane N) : SobolevHilbert r :=
  finiteElement38 r (modeIndex N) z

/-- The coefficients of `planeElement38` are the Fourier coefficients of the field `v`. -/
theorem planeElement_hsource38 (r : ℝ) (N : ℕ) (z : FourierPlane N) (n : ℤ) :
    (show WeightedHilbert (sobolevModeWeight r) from planeElement38 r N z) n =
      smoothFourier38 (planeReal N z) (planeReal_smooth38 N z) (planeReal_periodic N z) n := by
  have hu : ContDiff ℝ ∞ (tailField38 (modeIndex N) z) :=
    (contDiff_tailField38 _ z).of_le le_top
  rw [smoothFourier38_congr (planeReal_eq_tailField38 N z) _ _ hu (tailField_periodic38 _ z)]
  exact finiteElement_hsource38 r _ z (modeIndex_injective N) hu (tailField_periodic38 _ z) n

theorem vSobolev_plane38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (N : ℕ) (z : FourierPlane N) :
    vSobolev38 m β (planeElement38 _ N z) = vLocal38 m β (planeReal N z) := by
  rw [planeElement38, vSobolev_finiteElement38 m hm β _ (modeIndex_injective N),
    planeReal_eq_tailField38]

theorem plane_append_injective38 (N : ℕ) {K : ℕ} (ι : Fin K → ℤ) (hinj : Function.Injective ι)
    (hι : ∀ k, (N : ℤ) < |ι k|) : Function.Injective (Fin.append (modeIndex N) ι) := by
  refine Fin.append_injective_iff.2 ⟨modeIndex_injective N, hinj, fun i k h => ?_⟩
  have hb := modeIndex_bounds N i
  have hk := hι k
  rw [← h] at hk
  exact absurd hk (not_lt.2 (abs_le.2 hb))

theorem vSobolev_plane_add38 (m : ℕ) (hm : 2 ≤ m) (β : ℕ → ℝ) (N : ℕ) (z : FourierPlane N)
    {K : ℕ} (ι : Fin K → ℤ) (hinj : Function.Injective ι) (hι : ∀ k, (N : ℤ) < |ι k|)
    (g : Fin K → ℂ) :
    vSobolev38 m β (planeElement38 _ N z + finiteElement38 _ ι g) =
      vLocal38 m β (fun y => planeReal N z y + tailField38 ι g y) := by
  have hab := plane_append_injective38 N ι hinj hι
  rw [planeElement38, ← finiteElement_append38 _ _ _ _ _ hab,
    vSobolev_finiteElement38 m hm β _ hab]
  congr 1
  funext y
  rw [tailField_append38, planeReal_eq_tailField38]

end Plane

section Limit

variable {m : ℕ} {β : ℕ → ℝ}

/-- `C_{m,N}(v) = E[V_m(v + Y_N)] − V_m(v)` (`C:eq:correction`), `U ~ γ_m^F`. -/
def contractionCorrection38 (m : ℕ) (β : ℕ → ℝ) (N : ℕ) (z : FourierPlane N) : ℝ :=
  (∫ s, vSobolev38 m β (planeElement38 _ N z + tailRealization38 m N s) ∂gammaM38 m β) -
    vSobolev38 m β (planeElement38 _ N z)

/-- The expectation with the upper cutoff `N'` is the finite-dimensional `cgPi` integral of F06-C1. -/
theorem integral_trunc38 (hm : 2 ≤ m) (N N' : ℕ) (z : FourierPlane N) :
    ∫ s, vSobolev38 m β (planeElement38 _ N z + truncRealization38 m N N' s) ∂gammaM38 m β =
      ∫ g, vLocal38 m β (fun y => planeReal N z y + tailField38 (truncIota38 N N') g y)
        ∂cgPi (fun k => finiteHierarchyRate38 m β (truncIota38 N N' k)) := by
  have hF : Measurable (fun g : Fin (truncFinset38 N N').card → ℂ =>
      vSobolev38 m β (planeElement38 _ N z + finiteElement38 _ (truncIota38 N N') g)) :=
    ((continuous_vSobolev38 m β).comp (continuous_const.add continuous_id)).measurable.comp
      (measurable_finiteElement38 _ _)
  have hφ : Measurable (fun s : ℤ → ℂ => fun k => s (truncIota38 N N' k)) :=
    measurable_pi_iff.2 (fun k => measurable_pi_apply _)
  have hFeq : (fun g => vLocal38 m β (fun y => planeReal N z y + tailField38 (truncIota38 N N') g y)) =
      fun g : Fin (truncFinset38 N N').card → ℂ =>
        vSobolev38 m β (planeElement38 _ N z + finiteElement38 _ (truncIota38 N N') g) :=
    funext fun g => (vSobolev_plane_add38 m hm β N z _ (truncIota_injective38 N N')
      (truncIota_gt38 N N') g).symm
  rw [hFeq, ← law_truncBlock38 (m := m) (β := β) N N',
    integral_map hφ.aemeasurable hF.aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [truncRealization_eq_finiteElement38]

variable (hm : 2 ≤ m) (hβ : ∀ i ≤ m, 0 ≤ β i) (h0 : 0 < β 0) (hM : 0 < β m)
include hm hβ h0 hM

/-- Removal of the upper cutoff: `V_m(v + Y_N)` is integrable and
`E V_m(v + Y_{N,N'}) → E V_m(v + Y_N)` as `N' → ∞` (dominated convergence). -/
theorem tendsto_integral_trunc38 (N : ℕ) (x : SobolevHilbert ((m - 1 : ℕ) : ℝ)) :
    Integrable (fun s => vSobolev38 m β (x + tailRealization38 m N s)) (gammaM38 m β) ∧
    Tendsto (fun N' : ℕ => ∫ s, vSobolev38 m β (x + truncRealization38 m N N' s) ∂gammaM38 m β)
      atTop (𝓝 (∫ s, vSobolev38 m β (x + tailRealization38 m N s) ∂gammaM38 m β)) := by
  obtain ⟨C, hC0, hC⟩ := vSobolev38_bound m β
  set p := 2 * m + 2
  set c := ‖x‖
  set γ := gammaM38 m β
  have hmom : ∀ k : ℕ, Integrable (fun s => ‖tailRealization38 m N s‖ ^ k) γ := fun k => by
    obtain ⟨_, _, h⟩ := tailRealization_moment38 hm hβ h0 hM k
    exact (h N).1
  set bound : (ℤ → ℂ) → ℝ := fun s => C * (1 + (‖tailRealization38 m N s‖ + c) ^ p) with hbound
  have hbi : Integrable bound γ := by
    have hsum : Integrable (fun s => ∑ i ∈ Finset.range (p + 1),
        ‖tailRealization38 m N s‖ ^ i * c ^ (p - i) * (p.choose i : ℝ)) γ :=
      integrable_finsetSum _ fun i _ => ((hmom i).mul_const _).mul_const _
    have heq : bound = fun s => C * (1 + ∑ i ∈ Finset.range (p + 1),
        ‖tailRealization38 m N s‖ ^ i * c ^ (p - i) * (p.choose i : ℝ)) := by
      funext s
      simp only [hbound, add_pow]
    rw [heq]
    exact ((integrable_const 1).add hsum).const_mul C
  have hcont : Continuous (fun y : SobolevHilbert ((m - 1 : ℕ) : ℝ) => vSobolev38 m β (x + y)) :=
    (continuous_vSobolev38 m β).comp (continuous_const.add continuous_id)
  have hle : ∀ y : SobolevHilbert ((m - 1 : ℕ) : ℝ), ∀ s, ‖y‖ ≤ ‖tailRealization38 m N s‖ →
      ‖vSobolev38 m β (x + y)‖ ≤ bound s := by
    intro y s hy
    rw [Real.norm_eq_abs]
    refine (hC _).trans (mul_le_mul_of_nonneg_left ?_ hC0)
    gcongr
    calc ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le _ _
      _ ≤ ‖tailRealization38 m N s‖ + c := by linarith
  refine ⟨hbi.mono' (hcont.measurable.comp (measurable_tailRealization38 N)).aestronglyMeasurable
    (Eventually.of_forall fun s => hle _ s le_rfl), ?_⟩
  have hae := ae_trunc_tendsto38 hm hβ h0 hM N
  refine tendsto_integral_of_dominated_convergence bound
    (fun N' => (hcont.measurable.comp (measurable_truncRealization38 N N')).aestronglyMeasurable)
    hbi (fun N' => ?_) ?_
  · filter_upwards [hae] with s hs
    exact hle _ s (hs.2 N')
  · filter_upwards [hae] with s hs
    exact (hcont.tendsto _).comp hs.1

/-- **`C:lem:contractions`** (paper/v2.tex l.743-750), with `C_{m,N}` exactly as in
`C:eq:correction`: for fixed `m ≥ 2` and positive `β_0, …, β_m` there are `A_m, B_m ≥ 0`
(depending only on `m, β`) such that for every `N ≥ 1` and `v ∈ F_N`, `V_m(v + Y_N)` is
integrable and
`|C_{m,N}(v)| ≤ A_m [N^{-2m} + Σ_{l=1}^m (M(v)/N)^l] ≤ (B_m/N)(1 + M(v)^m)`,
`M(v) = ‖v‖₂²`. -/
theorem contractions_massBound38 :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ z : FourierPlane N,
      Integrable (fun s => vSobolev38 m β (planeElement38 _ N z + tailRealization38 m N s))
        (gammaM38 m β) ∧
      |contractionCorrection38 m β N z| ≤
        A * (((N : ℝ) ^ (2 * m))⁻¹ + ∑ l ∈ Finset.Icc 1 m, (‖planeL2 N z‖ ^ 2 / N) ^ l) ∧
      A * (((N : ℝ) ^ (2 * m))⁻¹ + ∑ l ∈ Finset.Icc 1 m, (‖planeL2 N z‖ ^ 2 / N) ^ l) ≤
        B / N * (1 + (‖planeL2 N z‖ ^ 2) ^ m) := by
  obtain ⟨A, hA0, hA⟩ := contraction_finiteCutoff38 m β (by omega) hβ h0 hM
  refine ⟨A, A * (m + 1), hA0, by positivity, fun N hN z => ?_⟩
  rw [planeL2_norm_sq]
  obtain ⟨hint, htend⟩ := tendsto_integral_trunc38 hm hβ h0 hM N (planeElement38 _ N z)
  refine ⟨hint, ?_, ?_⟩
  · have hstep : ∀ N' : ℕ,
        |(∫ s, vSobolev38 m β (planeElement38 _ N z + truncRealization38 m N N' s)
            ∂gammaM38 m β) - vSobolev38 m β (planeElement38 _ N z)| ≤
          A * Phi38 m N (∑ i, ‖z i‖ ^ 2) := by
      intro N'
      rw [integral_trunc38 hm N N' z, vSobolev_plane38 m hm β N z]
      exact (hA N hN z _ (truncIota38 N N') (truncIota_injective38 N N')
        (truncIota_gt38 N N')).2
    have hlim := (continuous_abs.tendsto _).comp
      (htend.sub_const (vSobolev38 m β (planeElement38 _ N z)))
    exact le_of_tendsto' hlim hstep
  · have hMnn : 0 ≤ ∑ i, ‖z i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
    have := Phi38_le38 m N (by omega) hN _ hMnn
    unfold Phi38 at this
    calc A * (((N : ℝ) ^ (2 * m))⁻¹ + ∑ l ∈ Finset.Icc 1 m, ((∑ i, ‖z i‖ ^ 2) / N) ^ l)
        ≤ A * ((m + 1) * ((1 + (∑ i, ‖z i‖ ^ 2) ^ m) / N)) :=
          mul_le_mul_of_nonneg_left this hA0
      _ = A * (m + 1) / N * (1 + (∑ i, ‖z i‖ ^ 2) ^ m) := by ring

end Limit

end NlsGge.HierarchyRiccati.Core

end
