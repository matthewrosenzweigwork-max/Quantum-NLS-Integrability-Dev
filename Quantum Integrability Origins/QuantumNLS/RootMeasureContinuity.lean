import Mathlib
import QuantumNLS.RootMeasureExistence

/-!
# R-09E1EAE9 `thm:root-measure`, Step 6: continuity of `u ↦ μ_{κ,u}` on the unit `L²` sphere

Source: `ROOT_spectral_measure.tex`, `thm:root-measure`, Step 6.  Imports the frozen `RootMeasureExistence` (and through it Steps 1-5) read-only.
No EXT-025 contract is used.

* `norm_htpow_sub_le`: `‖u^{⊗r} − v^{⊗r}‖ ≤ r‖u − v‖` for `‖u‖,‖v‖ ≤ 1` (telescoping, via mathlib's multilinear difference estimate for the
  continuous multilinear map `htpowML`).
* `norm_kps_sub_le`: `|⟨u^r, A u^r⟩ − ⟨v^r, A v^r⟩| ≤ 2‖A‖ r ‖u − v‖`.
* `productSymbol_sub_le`: `|s(z;u) − s(z;v)| ≤ 16 (κ/η) ‖u − v‖` on the high half-plane (the printed constant is `4κ/(η(1−κ/η)²)`; the constant here is
  coarser, from `r ≤ 2^r` and a geometric series, which suffices for continuity).
* `gStar_dist_le`: `|g_u(z) − g_v(z)| ≤ (2/κ)|s(z;u) − s(z;v)|` (the inverse bound `eq:root-inverse-bound`).
* `continuity_limiting_measure`: if unit `u_n → u` and `μ_n`, `μ` are the limiting measures of `u_n`, `u` (`IsLimitingRapidityMeasure`), then `μ_n → μ` weakly.
  Proof as printed: the Cauchy transforms converge on the high half-plane, the tail inequality with no loss of mass for `μ` gives tightness, and
  Cauchy-transform uniqueness identifies every limit (`CauchyLimitCriterion.tendsto_of_cauchy`).
* `continuous_muOf`: the map `u ↦ μ_{κ,u}` (chosen via `exists_limiting_measure`; unique) is continuous on the unit sphere.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace QuantumNLS.RootMeasureContinuity

open QuantumNLS.PhysicalTensor (L2T)
open QuantumNLS.TensorCarrier (htpow ptprod norm_ptprod norm_htpow htpow_mem_symSector AlgTensorPower HilbertTensorPower)
open QuantumNLS.KernelDefinition (kernelProductSymbol BoundedSymmetricKernel)
open QuantumNLS.NormalizedTransfer (productSymbol symbolTerm orderedKernel)
open QuantumNLS.RootMeasureComplex (fz HighHalf fz_lower)
open QuantumNLS.RootMeasureConcentration (gStar gStar_spec)
open QuantumNLS.HighMomentsOps (wvec)
open QuantumNLS.RootPlacementBound (lem_root_placement)
open QuantumNLS.CauchyUniqueness (cauchyTransform)
open QuantumNLS.BulkResponseActual (IsLimitingRapidityMeasure)

variable {L : ℝ} [Fact (0 < L)] {κ : ℝ}

/-! ### Telescoping for tensor powers -/

theorem norm_htpow_sub_le (n : ℕ) (u v : L2T L) (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ‖(htpow n u : HilbertTensorPower ℂ (L2T L) n) - htpow n v‖ ≤ n * ‖u - v‖ := by
  set f := QuantumNLS.RootOverlapLimit.htpowML (H := L2T L) n with hf
  have hnorm : ‖f‖ ≤ 1 := by
    refine ContinuousMultilinearMap.opNorm_le_bound zero_le_one (fun m => ?_)
    have e : f m = ((ptprod m : AlgTensorPower ℂ (L2T L) n) : HilbertTensorPower ℂ (L2T L) n) :=
      QuantumNLS.RootOverlapLimit.htpowML_apply n m
    rw [one_mul]
    exact (calc ‖f m‖ = ‖((ptprod m : AlgTensorPower ℂ (L2T L) n) : HilbertTensorPower ℂ (L2T L) n)‖ :=
        congrArg _ e
      _ = ∏ i, ‖m i‖ := by rw [UniformSpace.Completion.norm_coe, norm_ptprod]).le
  have h := f.norm_image_sub_le (fun _ => u) (fun _ => v)
  have e1 : f (fun _ => u) = htpow n u := QuantumNLS.RootOverlapLimit.htpowML_apply n _
  have e2 : f (fun _ => v) = htpow n v := QuantumNLS.RootOverlapLimit.htpowML_apply n _
  have hh : ‖(htpow n u : HilbertTensorPower ℂ (L2T L) n) - htpow n v‖ =
      ‖f (fun _ => u) - f (fun _ => v)‖ := by rw [e1, e2]
  have h1 : ‖(fun _ : Fin n => u)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun _ => hu)
  have h2 : ‖(fun _ : Fin n => v)‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun _ => hv)
  have h3 : ‖(fun _ : Fin n => u) - (fun _ : Fin n => v)‖ ≤ ‖u - v‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun _ => le_rfl)
  have h4 : max ‖(fun _ : Fin n => u)‖ ‖(fun _ : Fin n => v)‖ ^ (n - 1) ≤ 1 :=
    pow_le_one₀ (le_max_iff.2 (Or.inl (norm_nonneg _))) (max_le h1 h2)
  refine hh.le.trans (h.trans ?_)
  rw [Fintype.card_fin]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc ‖f‖ * (n : ℝ) * max ‖(fun _ : Fin n => u)‖ ‖(fun _ : Fin n => v)‖ ^ (n - 1) *
        ‖(fun _ : Fin n => u) - (fun _ : Fin n => v)‖ ≤ 1 * (n : ℝ) * 1 * ‖u - v‖ := by
        gcongr
    _ = n * ‖u - v‖ := by ring

theorem norm_kps_sub_le (r : ℕ) (A : BoundedSymmetricKernel (L2T L) r) (u v : L2T L) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) :
    ‖kernelProductSymbol A u - kernelProductSymbol A v‖ ≤ 2 * ‖A‖ * (r * ‖u - v‖) := by
  have e : ∀ w : L2T L, kernelProductSymbol A w = ⟪wvec r w, A (wvec r w)⟫_ℂ := fun w => rfl
  have hn : ∀ w : L2T L, ‖w‖ = 1 → ‖wvec r w‖ = 1 := by
    intro w hw
    rw [← Submodule.norm_coe]
    show ‖(htpow r w : HilbertTensorPower ℂ (L2T L) r)‖ = 1
    rw [norm_htpow, hw, one_pow]
  have hd : ‖wvec r u - wvec r v‖ ≤ r * ‖u - v‖ := by
    rw [← Submodule.norm_coe, Submodule.coe_sub]
    exact norm_htpow_sub_le r u v hu.le hv.le
  rw [e, e]
  have hid : ⟪wvec r u, A (wvec r u)⟫_ℂ - ⟪wvec r v, A (wvec r v)⟫_ℂ =
      ⟪wvec r u - wvec r v, A (wvec r u)⟫_ℂ + ⟪wvec r v, A (wvec r u - wvec r v)⟫_ℂ := by
    rw [map_sub, inner_sub_left, inner_sub_right]; ring
  rw [hid]
  have hA : ∀ x : QuantumNLS.TensorCarrier.SymSector ℂ (L2T L) r, ‖A x‖ ≤ ‖A‖ * ‖x‖ := fun x => A.le_opNorm x
  have b1 : ‖⟪wvec r u - wvec r v, A (wvec r u)⟫_ℂ‖ ≤ ‖wvec r u - wvec r v‖ * ‖A‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    have := hA (wvec r u)
    rw [hn u hu, mul_one] at this
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have b2 : ‖⟪wvec r v, A (wvec r u - wvec r v)⟫_ℂ‖ ≤ ‖A‖ * ‖wvec r u - wvec r v‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hn v hv, one_mul]
    exact hA _
  calc _ ≤ ‖⟪wvec r u - wvec r v, A (wvec r u)⟫_ℂ‖ + ‖⟪wvec r v, A (wvec r u - wvec r v)⟫_ℂ‖ :=
        norm_add_le _ _
    _ ≤ ‖wvec r u - wvec r v‖ * ‖A‖ + ‖A‖ * ‖wvec r u - wvec r v‖ := add_le_add b1 b2
    _ = 2 * ‖A‖ * ‖wvec r u - wvec r v‖ := by ring
    _ ≤ 2 * ‖A‖ * (r * ‖u - v‖) := by gcongr

/-! ### Lipschitz dependence of the product symbol and of `g` -/

theorem summable_symbolTerm (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    Summable (fun j : ℕ => symbolTerm L κ u z (j + 1)) := by
  have hη : 0 < z.im := by linarith [hz.1]
  have hx0 : 0 ≤ κ / z.im := by positivity
  have hx4 : κ / z.im ≤ 1 / 4 := by rw [div_le_iff₀ hη]; linarith [hz.1]
  refine Summable.of_norm_bounded (g := fun j => 2 * (κ / z.im) ^ (j + 1)) ?_
    (fun j => QuantumNLS.RootMeasureNoLoss.symbolTerm_le hκ u hu hη (j + 1) (by omega))
  exact ((summable_geometric_of_lt_one hx0 (by linarith)).mul_left (2 * (κ / z.im))).congr
    (fun j => by ring)

theorem symbolTerm_sub_le (hκ : 0 < κ) (u v : L2T L) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {z : ℂ} (hz : 0 < z.im)
    (r : ℕ) (hr : 1 ≤ r) :
    ‖symbolTerm L κ u z r - symbolTerm L κ v z r‖ ≤ 4 * (2 * (κ / z.im)) ^ r * ‖u - v‖ := by
  unfold symbolTerm
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hκ r)]
  have h1 := norm_kps_sub_le r (orderedKernel L r z) u v hu hv
  have h2 : ‖orderedKernel L r z‖ ≤ 2 * (z.im)⁻¹ ^ r :=
    (lem_root_placement u hu (N := r) hr le_rfl z hz).1
  have hr2 : (r : ℝ) ≤ 2 ^ r := by
    exact_mod_cast (Nat.lt_two_pow_self (n := r)).le
  have hn0 : 0 ≤ ‖u - v‖ := norm_nonneg _
  calc κ ^ r * ‖kernelProductSymbol (orderedKernel L r z) u - kernelProductSymbol (orderedKernel L r z) v‖
      ≤ κ ^ r * (2 * ‖orderedKernel L r z‖ * (r * ‖u - v‖)) := by gcongr
    _ ≤ κ ^ r * (2 * (2 * (z.im)⁻¹ ^ r) * (r * ‖u - v‖)) := by gcongr
    _ = 4 * (κ / z.im) ^ r * r * ‖u - v‖ := by
        rw [div_pow, div_eq_mul_inv, inv_pow]; ring
    _ ≤ 4 * (κ / z.im) ^ r * 2 ^ r * ‖u - v‖ := by gcongr
    _ = 4 * (2 * (κ / z.im)) ^ r * ‖u - v‖ := by rw [mul_pow]; ring

theorem productSymbol_sub_le (hκ : 0 < κ) (u v : L2T L) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {z : ℂ}
    (hz : HighHalf L κ z) :
    ‖productSymbol L κ u z - productSymbol L κ v z‖ ≤ 16 * (κ / z.im) * ‖u - v‖ := by
  have hη : 0 < z.im := by linarith [hz.1]
  set x : ℝ := κ / z.im with hx
  have hx0 : 0 ≤ x := by positivity
  have hx4 : x ≤ 1 / 4 := by rw [hx, div_le_iff₀ hη]; linarith [hz.1]
  have hsu := summable_symbolTerm hκ u hu hz
  have hsv := summable_symbolTerm hκ v hv hz
  have hdiff : productSymbol L κ u z - productSymbol L κ v z =
      ∑' j : ℕ, (symbolTerm L κ u z (j + 1) - symbolTerm L κ v z (j + 1)) := by
    rw [hsu.tsum_sub hsv]
    unfold productSymbol; ring
  rw [hdiff]
  have hg : HasSum (fun j : ℕ => (8 * x * ‖u - v‖) * (2 * x) ^ j) ((8 * x * ‖u - v‖) * (1 - 2 * x)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) (by linarith)).mul_left _
  have hb := tsum_of_norm_bounded hg (f := fun j : ℕ => symbolTerm L κ u z (j + 1) - symbolTerm L κ v z (j + 1))
    (fun j => by
      refine (symbolTerm_sub_le hκ u v hu hv hη (j + 1) (by omega)).trans (le_of_eq ?_)
      ring)
  refine hb.trans ?_
  have hinv : (1 - 2 * x)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hn0 : 0 ≤ 8 * x * ‖u - v‖ := by positivity
  calc (8 * x * ‖u - v‖) * (1 - 2 * x)⁻¹ ≤ (8 * x * ‖u - v‖) * 2 := mul_le_mul_of_nonneg_left hinv hn0
    _ = 16 * x * ‖u - v‖ := by ring

theorem gStar_dist_le (hκ : 0 < κ) (u v : L2T L) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) {z : ℂ} (hz : HighHalf L κ z) :
    κ / 2 * ‖gStar L κ hκ u hu z - gStar L κ hκ v hv z‖ ≤ 16 * (κ / z.im) * ‖u - v‖ := by
  obtain ⟨hg1, hg2⟩ := gStar_spec hκ u hu hz
  obtain ⟨hh1, hh2⟩ := gStar_spec hκ v hv hz
  have h1 := fz_lower hκ hz hg1 hh1
  rw [hg2, hh2] at h1
  exact h1.trans (productSymbol_sub_le hκ u v hu hv hz)

theorem gStar_tendsto (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (un : ℕ → L2T L) (hun : ∀ n, ‖un n‖ = 1)
    (hlim : Tendsto un atTop (𝓝 u)) {z : ℂ} (hz : HighHalf L κ z) :
    Tendsto (fun n => gStar L κ hκ (un n) (hun n) z) atTop (𝓝 (gStar L κ hκ u hu z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun n => (2 / κ) * (16 * (κ / z.im)) * ‖un n - u‖) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hlim).const_mul ((2 / κ) * (16 * (κ / z.im)))
    simpa [mul_assoc] using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h0
  have h := gStar_dist_le hκ (un n) u (hun n) hu hz
  have hκ2 : 0 < κ / 2 := by positivity
  have hmain : ‖gStar L κ hκ (un n) (hun n) z - gStar L κ hκ u hu z‖ ≤
      (2 / κ) * (16 * (κ / z.im) * ‖un n - u‖) := by
    calc ‖gStar L κ hκ (un n) (hun n) z - gStar L κ hκ u hu z‖
        = (2 / κ) * (κ / 2 * ‖gStar L κ hκ (un n) (hun n) z - gStar L κ hκ u hu z‖) := by
          field_simp
      _ ≤ (2 / κ) * (16 * (κ / z.im) * ‖un n - u‖) :=
          mul_le_mul_of_nonneg_left h (by positivity)
  calc ‖gStar L κ hκ (un n) (hun n) z - gStar L κ hκ u hu z‖
      ≤ (2 / κ) * (16 * (κ / z.im) * ‖un n - u‖) := hmain
    _ = 2 / κ * (16 * (κ / z.im)) * ‖un n - u‖ := by ring

/-! ### Continuity of `u ↦ μ_{κ,u}` -/

theorem continuity_limiting_measure (hκ : 0 < κ) (u : L2T L) (hu : ‖u‖ = 1) (un : ℕ → L2T L)
    (hun : ∀ n, ‖un n‖ = 1) (hlim : Tendsto un atTop (𝓝 u)) (μn : ℕ → ProbabilityMeasure ℝ)
    (hμn : ∀ n, IsLimitingRapidityMeasure L κ hκ (un n) (hun n) (μn n)) (μ : ProbabilityMeasure ℝ)
    (hμ : IsLimitingRapidityMeasure L κ hκ u hu μ) : Tendsto μn atTop (𝓝 μ) := by
  set η₀ : ℝ := max (4 * κ) (Real.log 16 / L) with hη₀
  have hL : 0 < L := Fact.out
  have hη0 : 0 < η₀ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hhigh : ∀ y : ℝ, η₀ ≤ y → HighHalf L κ (Complex.I * (y : ℂ)) := by
    intro y hy
    have him : (Complex.I * (y : ℂ)).im = y := by simp
    refine ⟨by rw [him]; exact (le_max_left _ _).trans hy, ?_⟩
    rw [him]
    have : Real.log 16 / L ≤ y := (le_max_right _ _).trans hy
    rwa [div_le_iff₀ hL, mul_comm] at this
  have hhighL : ∀ t : ℝ, HighHalf L κ ((t : ℂ) + η₀ * Complex.I) := by
    intro t
    have him : ((t : ℂ) + η₀ * Complex.I).im = η₀ := by simp
    refine ⟨by rw [him]; exact le_max_left _ _, ?_⟩
    rw [him]
    have : Real.log 16 / L ≤ η₀ := le_max_right _ _
    rwa [div_le_iff₀ hL, mul_comm] at this
  let g : ℂ → ℂ := gStar L κ hκ u hu
  let q : ℕ → ℝ := TopologicalSpace.denseSeq ℝ
  let Y : ℕ → ℝ := fun j => η₀ + j
  have hYge : ∀ j, η₀ ≤ Y j := fun j => by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    simp only [Y]; linarith
  have hYpos : ∀ j, 0 < Y j := fun j => lt_of_lt_of_le hη0 (hYge j)
  have hmassY : Tendsto (fun y : ℝ => 1 + y * (g (Complex.I * (y : ℂ))).im) atTop (𝓝 0) := by
    refine QuantumNLS.RootMeasureNoLoss.one_add_mul_im_tendsto hκ u hu (fun y => g (Complex.I * (y : ℂ))) ?_
    intro y hy
    obtain ⟨h1, h2⟩ := gStar_spec hκ u hu hy
    refine ⟨?_, h2⟩
    have him : (Complex.I * (y : ℂ)).im = y := by simp
    simpa [him] using h1
  have hYtop : Tendsto Y atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hmass : Tendsto (fun j => 1 + Y j * (g (Complex.I * (Y j : ℂ))).im) atTop (𝓝 0) :=
    hmassY.comp hYtop
  have hconv : ∀ z : ℂ, HighHalf L κ z →
      Tendsto (fun n => cauchyTransform (μn n : Measure ℝ) z) atTop (𝓝 (g z)) := by
    intro z hz
    have : ∀ n, cauchyTransform (μn n : Measure ℝ) z = gStar L κ hκ (un n) (hun n) z :=
      fun n => QuantumNLS.RootMeasureExistence.cauchy_limiting_measure hκ (un n) (hun n) (hμn n) hz
    simp_rw [this]
    exact gStar_tendsto hκ u hu un hun hlim hz
  exact QuantumNLS.CauchyLimitCriterion.tendsto_of_cauchy (η₀ := η₀) (q := q) (g := g) (Y := Y) hη0
    (TopologicalSpace.denseRange_denseSeq ℝ) μn hYpos μ
    (fun k => QuantumNLS.RootMeasureExistence.cauchy_limiting_measure hκ u hu hμ (hhighL (q k)))
    hmass (fun j => hconv _ (hhigh (Y j) (hYge j))) (fun k => hconv _ (hhighL (q k)))

/-- The (unique) limiting rapidity measure `μ_{κ,u}` of a unit profile, chosen via `exists_limiting_measure`. -/
def muOf (hκ : 0 < κ) (u : Metric.sphere (0 : L2T L) 1) : ProbabilityMeasure ℝ :=
  Classical.choose (QuantumNLS.RootMeasureExistence.exists_limiting_measure hκ u.1
    (by simpa using u.2))

theorem muOf_spec (hκ : 0 < κ) (u : Metric.sphere (0 : L2T L) 1) :
    IsLimitingRapidityMeasure L κ hκ u.1 (by simpa using u.2) (muOf hκ u) :=
  Classical.choose_spec (QuantumNLS.RootMeasureExistence.exists_limiting_measure hκ u.1
    (by simpa using u.2))

/-- **Step 6**: `u ↦ μ_{κ,u}` is continuous from the unit `L²` sphere to probability measures with the weak topology. -/
theorem continuous_muOf (hκ : 0 < κ) : Continuous (muOf (L := L) hκ) := by
  refine continuous_iff_seqContinuous.2 (fun un u hlim => ?_)
  have hun : ∀ n, ‖(un n).1‖ = 1 := fun n => by simpa using (un n).2
  have hu : ‖u.1‖ = 1 := by simpa using u.2
  exact continuity_limiting_measure hκ u.1 hu (fun n => (un n).1) hun
    ((continuous_subtype_val.tendsto u).comp hlim) (fun n => muOf hκ (un n))
    (fun n => muOf_spec hκ (un n)) (muOf hκ u) (muOf_spec hκ u)

end QuantumNLS.RootMeasureContinuity

#print axioms QuantumNLS.RootMeasureContinuity.norm_htpow_sub_le
#print axioms QuantumNLS.RootMeasureContinuity.norm_kps_sub_le
#print axioms QuantumNLS.RootMeasureContinuity.productSymbol_sub_le
#print axioms QuantumNLS.RootMeasureContinuity.gStar_dist_le
#print axioms QuantumNLS.RootMeasureContinuity.continuity_limiting_measure
#print axioms QuantumNLS.RootMeasureContinuity.continuous_muOf
