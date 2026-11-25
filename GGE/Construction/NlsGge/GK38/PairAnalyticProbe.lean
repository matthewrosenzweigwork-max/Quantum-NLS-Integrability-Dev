import NlsGge.GK38.PairAnalyticDet
import NlsGge.GK38.PairVolterraProbe

/-!
# F3 probes: `φ = 0` and the constant real-slice potential

* `φ = 0`: the free solution `E_z(t)` and the free monodromy are entire in `z`
  (`analyticOnNhd_fundPair_zero`, `analyticOnNhd_monodromyPair_zero`); `det = 1` is `cos² + sin²`
  (`det_monodromyPair_zero`).
* Constant real-slice potential `u ≡ a`: the monodromy entries are entire in `z`
  (`analyticOnNhd_monodromyPair_realSlice_const`).  The closed form of F2 has the apparent branch
  point `z² = |a|²` (`κ = 0`); analyticity (continuity) of the trace at the double point forces its
  value there: `tr M(1) = 2` (`trace_monodromyPair_realSlice_const_double`; F2 note N5).  This is a
  genuine consequence of F3, not available from the closed form (which assumes `κ ≠ 0`).
-/

set_option autoImplicit false

open Filter Topology MeasureTheory

namespace NlsGge.GK38

noncomputable section

/-- Restriction to a slice `z ↦ (φ, z)`: analyticity in `z` alone. -/
theorem analyticOnNhd_monodromyPair_z (φ : PotPair) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z : ℂ => monodromyPair φ z i j) Set.univ := fun z _ =>
  AnalyticAt.comp (g := fun p : PotPair × ℂ => monodromyPair p.1 p.2 i j)
    (f := fun z : ℂ => (φ, z)) (analyticOnNhd_monodromyPair i j (φ, z) (Set.mem_univ _))
    ((analyticAt_const (v := φ)).prod analyticAt_id)

theorem analyticOnNhd_monodromyPair_z' (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    AnalyticAt ℂ (fun φ : PotPair => monodromyPair φ z i j) φ :=
  AnalyticAt.comp (g := fun p : PotPair × ℂ => monodromyPair p.1 p.2 i j)
    (f := fun φ : PotPair => (φ, z)) (analyticOnNhd_monodromyPair i j (φ, z) (Set.mem_univ _))
    (analyticAt_id.prod analyticAt_const)

theorem analyticOnNhd_fundPair_z (φ : PotPair) (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z : ℂ => fundPair φ z t i j) Set.univ := fun z _ =>
  AnalyticAt.comp (g := fun p : PotPair × ℂ => fundPair p.1 p.2 t i j)
    (f := fun z : ℂ => (φ, z)) (analyticOnNhd_fundPair t i j (φ, z) (Set.mem_univ _))
    ((analyticAt_const (v := φ)).prod analyticAt_id)

/-! ### `φ = 0` -/

theorem analyticOnNhd_fundPair_zero (t : Set.Icc (0 : ℝ) 1) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z : ℂ => fundPair 0 z t i j) Set.univ :=
  analyticOnNhd_fundPair_z 0 t i j

/-- The free monodromy entries are entire, and agree with `diag(e^{-iz}, e^{iz})` (F2). -/
theorem analyticOnNhd_monodromyPair_zero (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z : ℂ => monodromyPair 0 z i j) Set.univ ∧
      ∀ z, monodromyPair 0 z i j = freeE z 1 i j :=
  ⟨analyticOnNhd_monodromyPair_z 0 i j, fun z => by rw [monodromyPair_zero_potential]⟩

/-- Analyticity along a complex line in `φ`: `s ↦ M(1, z, s φ)` is entire (all of `PotPair`, not
only the `z`-slice).  At `s = 0` it is the free monodromy of the probe above. -/
theorem analyticOnNhd_monodromyPair_smul (φ : PotPair) (z : ℂ) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun s : ℂ => monodromyPair (s • φ) z i j) Set.univ := fun s _ =>
  AnalyticAt.comp (g := fun p : PotPair × ℂ => monodromyPair p.1 p.2 i j)
    (f := fun s : ℂ => (s • φ, z)) (analyticOnNhd_monodromyPair i j (s • φ, z) (Set.mem_univ _))
    ((analyticAt_id.smul analyticAt_const).prod analyticAt_const)

/-- The transfer to the real slice used by F4: `u ↦ M(1, z, (u, ū))` is real analytic on `L²`. -/
theorem analyticOnNhd_real_monodromyPair_realSlice (z : ℂ) (i j : Fin 2) :
    AnalyticOnNhd ℝ (fun u : NlsGge.Pilot.PhysicalL2 => monodromyPair (realSlice u) z i j) Set.univ :=
  analyticOnNhd_comp_realSlice (f := fun φ : PotPair => monodromyPair φ z i j)
    (fun φ _ => analyticOnNhd_monodromyPair_z' φ z i j)

/-- `det M = 1` at `φ = 0` is `e^{-iz} e^{iz} = 1`; it is also what `det_monodromyPair` gives. -/
theorem det_monodromyPair_zero (z : ℂ) : (monodromyPair 0 z).det = 1 :=
  det_monodromyPair 0 z

/-! ### The constant real-slice potential -/

theorem analyticOnNhd_monodromyPair_realSlice_const (a : ℂ) (i j : Fin 2) :
    AnalyticOnNhd ℂ (fun z : ℂ => monodromyPair (realSlice (constL2 a)) z i j) Set.univ :=
  analyticOnNhd_monodromyPair_z _ i j

theorem analyticOnNhd_trace_monodromyPair (φ : PotPair) :
    AnalyticOnNhd ℂ (fun z : ℂ => Matrix.trace (monodromyPair φ z)) Set.univ := by
  intro z hz
  have h : ∀ i, AnalyticAt ℂ (fun z : ℂ => monodromyPair φ z i i) z :=
    fun i => analyticOnNhd_monodromyPair_z φ i i z hz
  have e : (fun z : ℂ => Matrix.trace (monodromyPair φ z)) =
      (fun z : ℂ => monodromyPair φ z 0 0) + (fun z : ℂ => monodromyPair φ z 1 1) := by
    ext z; simp [Matrix.trace, Fin.sum_univ_two]
  rw [e]
  exact (h 0).add (h 1)

/-- At the double point `z₀² = |a|²` of the constant potential, `tr M(1) = 2` (`κ = 0`), by
continuity of the (analytic) trace and the closed form `2 cos κ` off the double point. -/
theorem trace_monodromyPair_realSlice_const_double (a z₀ : ℂ) (hz₀ : z₀ ^ 2 = a * star a) :
    Matrix.trace (monodromyPair (realSlice (constL2 a)) z₀) = 2 := by
  set T : ℂ → ℂ := fun z => Matrix.trace (monodromyPair (realSlice (constL2 a)) z) with hT
  have hTc : ContinuousAt T z₀ :=
    (analyticOnNhd_trace_monodromyPair (realSlice (constL2 a)) z₀ (Set.mem_univ _)).continuousAt
  set κ : ℂ → ℂ := fun z => (z ^ 2 - a * star a) ^ ((2 : ℕ)⁻¹ : ℂ) with hκ
  have hκc : ContinuousAt κ z₀ := by
    have h1 : ContinuousAt (fun z : ℂ => z ^ 2 - a * star a) z₀ := by fun_prop
    have h2 : ContinuousAt (fun x : ℂ => x ^ ((2 : ℕ)⁻¹ : ℂ)) (z₀ ^ 2 - a * star a) := by
      refine Complex.continuousAt_cpow_const_of_re_pos (Or.inl ?_) ?_
      · rw [hz₀]; simp
      · norm_num
    exact ContinuousAt.comp (g := fun x : ℂ => x ^ ((2 : ℕ)⁻¹ : ℂ)) (f := fun z : ℂ => z ^ 2 - a * star a) h2 h1
  have hκ0 : κ z₀ = 0 := by
    simp [hκ, hz₀]
  have hκ2 : ∀ z, κ z ^ 2 = z ^ 2 - a * star a := fun z => Complex.cpow_nat_inv_pow _ (by norm_num)
  have hlim1 : Tendsto (fun z => 2 * Complex.cos (κ z)) (𝓝[≠] z₀) (𝓝 2) := by
    have : ContinuousAt (fun z => 2 * Complex.cos (κ z)) z₀ := by
      exact continuousAt_const.mul (Complex.continuous_cos.continuousAt.comp hκc)
    have h := this.tendsto
    simp only [hκ0, Complex.cos_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim2 : Tendsto T (𝓝[≠] z₀) (𝓝 (T z₀)) := hTc.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ z in 𝓝[≠] z₀, T z = 2 * Complex.cos (κ z) := by
    have hne : ∀ᶠ z in 𝓝[≠] z₀, z ≠ -z₀ := by
      by_cases h0 : z₀ = 0
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa [h0] using hz
      · exact eventually_nhdsWithin_of_eventually_nhds
          (isOpen_ne.mem_nhds (by intro h; apply h0; linear_combination (1 / 2 : ℂ) * h))
    filter_upwards [hne, self_mem_nhdsWithin] with z hz1 hz2
    have hz2' : z ≠ z₀ := hz2
    have hd : z ^ 2 ≠ a * star a := by
      intro h
      have : (z - z₀) * (z + z₀) = 0 := by linear_combination h - hz₀
      rcases mul_eq_zero.1 this with h1 | h1
      · exact hz2' (sub_eq_zero.1 h1)
      · exact hz1 (by linear_combination h1)
    have hκne : κ z ≠ 0 := by
      intro h0
      apply hd
      rw [← sub_eq_zero, ← hκ2 z, h0]; simp
    exact trace_monodromyPair_realSlice_const a z (κ z) hκne (hκ2 z)
  have := tendsto_nhds_unique (hlim2.congr' hev) hlim1
  exact this

end

end NlsGge.GK38
