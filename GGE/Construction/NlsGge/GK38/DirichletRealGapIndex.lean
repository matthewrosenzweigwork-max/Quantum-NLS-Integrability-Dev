import NlsGge.GK38.DirichletRealGap
import Mathlib.Topology.LocallyConstant.Basic

/-! The actual closed-gap index is locally constant along real norm paths.
Private source anchor: book I.7 Lemma 7.2. -/
set_option autoImplicit false
open Filter Topology Set
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

def dirichletGapIndex38 (u : PhysicalL2) (n : ℤ) : ℤ :=
  (dirichlet_root_some_gap38 u (gkMu u n) (gkMu_root38 u n)).exists.choose

theorem dirichletGapIndex_mem38 (u : PhysicalL2) (n : ℤ) :
    gkMu u n ∈ Icc (actualGapLowerAllE02_38 u (dirichletGapIndex38 u n))
      (actualGapUpperAllE02_38 u (dirichletGapIndex38 u n)) :=
  (dirichlet_root_some_gap38 u (gkMu u n) (gkMu_root38 u n)).exists.choose_spec

theorem dirichlet_gap_index_sandwich38 (u : PhysicalL2) (m k : ℤ) (x : ℝ)
    (hx : x ∈ Icc (actualGapLowerAllE02_38 u k) (actualGapUpperAllE02_38 u k))
    (hl : actualGapUpperAllE02_38 u (m - 1) < x)
    (hu : x < actualGapLowerAllE02_38 u (m + 1)) : k = m := by
  have hlow : StrictMono (actualGapLowerAllE02_38 u) := fun a b hab =>
    (gap_endpoint_levels38 u a).1.trans_lt (gap_indices_separated38 u hab)
  have hupp : StrictMono (actualGapUpperAllE02_38 u) := fun a b hab =>
    (gap_indices_separated38 u hab).trans_le (gap_endpoint_levels38 u b).1
  rcases lt_trichotomy k m with h | h | h
  · have hk : k ≤ m - 1 := by omega
    have ht := hupp.monotone hk
    linarith [hx.2]
  · exact h
  · have hk : m + 1 ≤ k := by omega
    have ht := hlow.monotone hk
    linarith [hx.1]

theorem dirichlet_gap_endpoint_path38 (u : PhysicalL2) (m : ℤ) :
    Continuous (fun t : DirichletTime38 => actualGapLowerAllE02_38 ((t : ℝ) • u) m) ∧
    Continuous (fun t : DirichletTime38 => actualGapUpperAllE02_38 ((t : ℝ) • u) m) := by
  have hc (k : ℤ) : Continuous (fun t : DirichletTime38 => lamSeq (realSlice ((t : ℝ) • u)) k) :=
    (periodic_real_path_continuous38 u k).comp_continuous continuous_subtype_val
      (fun t => t.property)
  have hl : Continuous (fun t : DirichletTime38 => (lamMinus (realSlice ((t : ℝ) • u)) m).re) :=
    Complex.continuous_re.comp (hc (2 * m))
  have hu : Continuous (fun t : DirichletTime38 => (lamPlus (realSlice ((t : ℝ) • u)) m).re) :=
    Complex.continuous_re.comp (hc (2 * m + 1))
  have el : (fun t : DirichletTime38 => (lamMinus (realSlice ((t : ℝ) • u)) m).re) =
      fun t : DirichletTime38 => actualGapLowerAllE02_38 ((t : ℝ) • u) m := by
    funext t
    rw [(lamPlus_real _ m).2, Complex.ofReal_re]
  have eu : (fun t : DirichletTime38 => (lamPlus (realSlice ((t : ℝ) • u)) m).re) =
      fun t : DirichletTime38 => actualGapUpperAllE02_38 ((t : ℝ) • u) m := by
    funext t
    rw [(lamPlus_real _ m).1, Complex.ofReal_re]
  exact ⟨el ▸ hl, eu ▸ hu⟩

theorem dirichletGapIndex_path_locallyConstant38 (u : PhysicalL2) (n : ℤ) :
    IsLocallyConstant (fun t : DirichletTime38 => dirichletGapIndex38 ((t : ℝ) • u) n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t₀
  let m := dirichletGapIndex38 ((t₀ : ℝ) • u) n
  have hx₀ := dirichletGapIndex_mem38 ((t₀ : ℝ) • u) n
  have hprev := gap_indices_separated38 ((t₀ : ℝ) • u) (show m - 1 < m by omega)
  have hnext := gap_indices_separated38 ((t₀ : ℝ) • u) (show m < m + 1 by omega)
  have hx : Continuous (fun t : DirichletTime38 => gkMu ((t : ℝ) • u) n) :=
    (continuous_gkMu38 n).comp (continuous_subtype_val.smul continuous_const)
  have hl : ∀ᶠ t : DirichletTime38 in 𝓝 t₀,
      actualGapUpperAllE02_38 ((t : ℝ) • u) (m - 1) < gkMu ((t : ℝ) • u) n :=
    (isOpen_lt (dirichlet_gap_endpoint_path38 u (m - 1)).2 hx).mem_nhds
      (hprev.trans_le hx₀.1)
  have hu : ∀ᶠ t : DirichletTime38 in 𝓝 t₀,
      gkMu ((t : ℝ) • u) n < actualGapLowerAllE02_38 ((t : ℝ) • u) (m + 1) :=
    (isOpen_lt hx (dirichlet_gap_endpoint_path38 u (m + 1)).1).mem_nhds
      (hx₀.2.trans_lt hnext)
  filter_upwards [hl, hu] with t ht₁ ht₂
  exact dirichlet_gap_index_sandwich38 ((t : ℝ) • u) m _ _
    (dirichletGapIndex_mem38 _ n) ht₁ ht₂

theorem dirichletGapIndex_zero38 (n : ℤ) : dirichletGapIndex38 0 n = n := by
  have hl := congrArg Complex.re (lamPlus_real (0 : PhysicalL2) n).2
  have hu := congrArg Complex.re (lamPlus_real (0 : PhysicalL2) n).1
  simp only [realSlice_zero, lamMinus_zero38, lamPlus_zero38, countingCenter_re38,
    Complex.ofReal_re] at hl hu
  apply gap_interval_index_unique38 (0 : PhysicalL2) (dirichletGapIndex_mem38 0 n)
  have hμ : gkMu 0 n = (n : ℝ) * Real.pi := by
    simp only [gkMu, realSlice_zero, muSeq_zero38, countingCenter_re38]
  rw [hμ, ← hl, ← hu]
  exact ⟨le_rfl, le_rfl⟩

theorem dirichletGapIndex_eq38 (u : PhysicalL2) (n : ℤ) : dirichletGapIndex38 u n = n := by
  have h := (dirichletGapIndex_path_locallyConstant38 u n).apply_eq_of_preconnectedSpace
    ⟨1, zero_le_one, le_rfl⟩ ⟨0, le_rfl, zero_le_one⟩
  simpa only [one_smul, zero_smul, dirichletGapIndex_zero38] using h

theorem gkMu_mem_gap38 (u : PhysicalL2) (n : ℤ) :
    gkMu u n ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) := by
  simpa only [dirichletGapIndex_eq38] using dirichletGapIndex_mem38 u n

theorem gkMu_spec (u : PhysicalL2) (n : ℤ) :
    dirichletChar (realSlice u) (gkMu u n : ℂ) = 0 ∧
      gkMu u n ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) ∧
      ∀ μ : ℝ, μ ∈ Icc (actualGapLowerAllE02_38 u n) (actualGapUpperAllE02_38 u n) →
        dirichletChar (realSlice u) (μ : ℂ) = 0 → μ = gkMu u n := by
  refine ⟨gkMu_root38 u n, gkMu_mem_gap38 u n, ?_⟩
  intro x hx hxroot
  obtain ⟨k, hk⟩ := ((muSeq_enumeration38 (realSlice u)).2.1 (x : ℂ)).mp hxroot
  rw [muSeq_eq_gkMu38] at hk
  have he : gkMu u k = x := Complex.ofReal_injective hk
  have hkn : k = n := gap_interval_index_unique38 u (he ▸ gkMu_mem_gap38 u k) hx
  simpa only [hkn] using he.symm

end
end NlsGge.GK38
