import NlsGge.GK38.EigenvalueCompactnessIndexAlignment
import NlsGge.GK38.EigenvalueCompactnessWeakRootLimit
import NlsGge.GK38.EigenvalueCompactnessClusters

/-! # S7: only the actual reference index occurs in a sufficiently small weak cluster -/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot NlsGge.SpectralFoundations
namespace NlsGge.GK38
noncomputable section

theorem endpoint_weak_correct_index38 (u : ℕ → PhysicalL2) (u₀ : PhysicalL2)
    (hw : IsWeakLim u u₀) (n : ℤ) (x : ℝ) (hx : EndpointAt38 u₀ n x) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ k in atTop, ∀ z ∈ ball (x : ℂ) r,
      perChar (realSlice (u k)) z = 0 →
        z = (actualGapLowerAllE02_38 (u k) n : ℂ) ∨
          z = (actualGapUpperAllE02_38 (u k) n : ℂ) := by
  classical
  obtain ⟨r, hr, _, hiso, _⟩ := endpoint_reference_cluster38 u₀ n x hx 1 zero_lt_one
  refine ⟨r, hr, ?_⟩
  by_contra h
  have hf : ∃ᶠ k in atTop, ∃ z : ℂ, z ∈ ball (x : ℂ) r ∧
      perChar (realSlice (u k)) z = 0 ∧
      ¬(z = (actualGapLowerAllE02_38 (u k) n : ℂ) ∨
        z = (actualGapUpperAllE02_38 (u k) n : ℂ)) := by
    simpa only [not_forall, not_imp, exists_prop, and_assoc] using not_eventually.mp h
  obtain ⟨q, hq, hbad⟩ := extraction_of_frequently_atTop hf
  choose z hzin hroot hwrong using hbad
  have hclosed : ∀ k, z k ∈ closedBall (x : ℂ) r := fun k => ball_subset_closedBall (hzin k)
  obtain ⟨z₀, hz₀, s, hs, hzs⟩ := (isCompact_closedBall (x : ℂ) r).tendsto_subseq hclosed
  let p := q ∘ s
  have hp : StrictMono p := hq.comp hs
  have hwP : IsWeakLim (u ∘ p) u₀ := fun v => (hw v).comp hp.tendsto_atTop
  have hreal (k : ℕ) : z k = ((z k).re : ℂ) :=
    Complex.ext (by simp) (by simp [perChar_root_real38 (u (q k)) (z k) (hroot k)])
  have hxr := Complex.continuous_re.continuousAt.tendsto.comp hzs
  have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp hxr
  have hzcast : z₀ = (z₀.re : ℂ) :=
    tendsto_nhds_unique hzs (hcast.congr' (Eventually.of_forall (fun k => (hreal (s k)).symm)))
  have href : perChar (realSlice u₀) (z₀.re : ℂ) = 0 :=
    perChar_real_varyingWeak_root_limit38 hwP hxr (fun k => by
      change perChar (realSlice (u (p k))) ((z (s k)).re : ℂ) = 0
      rw [← hreal (s k)]
      exact hroot (s k))
  have hzEq : z₀ = (x : ℂ) := by
    by_contra hne
    exact hiso z₀ hz₀ hne (by rwa [hzcast])
  have hlim : Tendsto (fun k => (z (s k)).re) atTop (𝓝 x) := by
    simpa only [hzEq, Complex.ofReal_re, Function.comp_def] using! hxr
  have hclass (k : ℕ) : ∃ m : ℤ, EndpointAt38 (u (p k)) m (z (s k)).re := by
    obtain ⟨m, hm⟩ := (perChar_zero_iff (u (p k)) (z (s k))).mp (hroot (s k))
    refine ⟨m, ?_⟩
    rcases hm with hm | hm
    · exact Or.inl (by simpa only [Complex.ofReal_re] using congrArg Complex.re hm)
    · exact Or.inr (by simpa only [Complex.ofReal_re] using congrArg Complex.re hm)
  choose m hm using hclass
  have he := periodic_index_eventually_eq38 hwP hlim hm hx
  obtain ⟨k, hk⟩ := he.exists
  have hend := hm k
  rw [hk] at hend
  apply hwrong (s k)
  rcases hend with hl | hu
  · exact Or.inl ((hreal (s k)).trans (congrArg Complex.ofReal hl))
  · exact Or.inr ((hreal (s k)).trans (congrArg Complex.ofReal hu))

end
end NlsGge.GK38
