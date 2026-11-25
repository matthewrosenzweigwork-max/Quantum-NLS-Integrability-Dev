import Mathlib

                                                                                               
                                                                                                
                                                                                              
set_option autoImplicit false

open Set Filter Topology

namespace NlsGge.Atomic.G4036Unique
noncomputable section

theorem pow_aux (x : ℂ) (m : ℕ) : x * ((m : ℂ) * x ^ (m - 1)) = (m : ℂ) * x ^ m := by
  cases m with
  | zero => simp
  | succ k => simp [pow_succ]; ring

theorem eq_zero_of_punctured {B : ℂ → ℂ} {e : ℂ} (hB : ContinuousAt B e)
    (h : ∀ᶠ z in 𝓝[≠] e, B z = 0) : B e = 0 :=
  tendsto_nhds_unique (hB.tendsto.mono_left nhdsWithin_le_nhds)
    (tendsto_const_nhds.congr' (h.mono fun z hz => hz.symm))

theorem ode_unique_local {S : ℂ → ℂ} {e τ g : ℂ} (hPe : (e - τ) ^ 2 - g / 4 = 0)
    (hS : AnalyticAt ℂ S e)
    (hode : ∀ᶠ z in 𝓝 e, ((z - τ) ^ 2 - g / 4) * deriv S z + (z - τ) * S z = 0) :
    ∀ᶠ z in 𝓝 e, S z = 0 := by
  by_contra hne
  obtain ⟨m, g1, hg1, hg10, hF⟩ := (hS.exists_eventuallyEq_pow_smul_nonzero_iff).mpr hne
  have hP : ∀ z : ℂ, (z - τ) ^ 2 - g / 4 = (z - e) * (z - (2 * τ - e)) := by
    intro z; linear_combination hPe
  have hg1' : AnalyticAt ℂ (deriv g1) e := hg1.deriv
  have hev : ∀ᶠ z in 𝓝 e, (z - e) ^ m *
      ((m : ℂ) * (z - (2 * τ - e)) * g1 z + (z - e) * (z - (2 * τ - e)) * deriv g1 z +
        (z - τ) * g1 z) = 0 := by
    filter_upwards [hode, hF.eventually_nhds, hg1.eventually_analyticAt, hF] with z hz hzF hzg hzS
    have hd : deriv S z = (m : ℂ) * (z - e) ^ (m - 1) * g1 z + (z - e) ^ m * deriv g1 z := by
      have h1 : HasDerivAt (fun y : ℂ => (y - e) ^ m * g1 y)
          ((m : ℂ) * (z - e) ^ (m - 1) * 1 * g1 z + (z - e) ^ m * deriv g1 z) z :=
        (((hasDerivAt_id z).sub_const e).pow m).mul hzg.differentiableAt.hasDerivAt
      have h2 : deriv S z = deriv (fun y : ℂ => (y - e) ^ m * g1 y) z :=
        Filter.EventuallyEq.deriv_eq (hzF.mono fun x hx => by simpa only [smul_eq_mul] using hx)
      rw [h2, h1.deriv]
      ring
    rw [hd, hzS, hP z] at hz
    simp only [smul_eq_mul] at hz
    have := pow_aux (z - e) m
    linear_combination hz - ((z - (2 * τ - e)) * g1 z) * this
  have hpunct : ∀ᶠ z in 𝓝[≠] e, (z - e) ^ m *
      ((m : ℂ) * (z - (2 * τ - e)) * g1 z + (z - e) * (z - (2 * τ - e)) * deriv g1 z +
        (z - τ) * g1 z) = 0 := nhdsWithin_le_nhds hev
  have hB : ∀ᶠ z in 𝓝[≠] e,
      (m : ℂ) * (z - (2 * τ - e)) * g1 z + (z - e) * (z - (2 * τ - e)) * deriv g1 z +
        (z - τ) * g1 z = 0 := by
    filter_upwards [hpunct, self_mem_nhdsWithin] with z hz hzne
    have : (z - e) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hzne)
    exact (mul_eq_zero.mp hz).resolve_left this
  have hBc : ContinuousAt (fun z : ℂ =>
      (m : ℂ) * (z - (2 * τ - e)) * g1 z + (z - e) * (z - (2 * τ - e)) * deriv g1 z +
        (z - τ) * g1 z) e := by
    have h1 := hg1.continuousAt
    have h2 := hg1'.continuousAt
    fun_prop
  have hB0 := eq_zero_of_punctured hBc hB
  simp only [sub_self, zero_mul, add_zero] at hB0
  -- e = tau
  have h2m : ((2 * m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (2 * m)
  have hetau : e = τ := by
    have h3 : g1 e * ((2 * m + 1 : ℕ) : ℂ) * (e - τ) = 0 := by
      push_cast
      linear_combination hB0
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd (mul_eq_zero.mp h |>.resolve_right h2m) hg10
    · exact sub_eq_zero.mp h
  -- collapsed case
  subst hetau
  have hgz : g = 0 := by linear_combination (-4 : ℂ) * hPe
  have hC : ∀ᶠ z in 𝓝[≠] e, (m + 1 : ℂ) * g1 z + (z - e) * deriv g1 z = 0 := by
    filter_upwards [hB, self_mem_nhdsWithin] with z hz hzne
    have hz' : (z - e) * ((m + 1 : ℂ) * g1 z + (z - e) * deriv g1 z) = 0 := by
      linear_combination hz
    exact (mul_eq_zero.mp hz').resolve_left (sub_ne_zero.mpr hzne)
  have hCc : ContinuousAt (fun z : ℂ => (m + 1 : ℂ) * g1 z + (z - e) * deriv g1 z) e := by
    have h1 := hg1.continuousAt
    have h2 := hg1'.continuousAt
    fun_prop
  have hC0 := eq_zero_of_punctured hCc hC
  simp only [sub_self, zero_mul, add_zero] at hC0
  have hm1 : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  exact hg10 ((mul_eq_zero.mp hC0).resolve_left hm1)

/-- Global form: an analytic solution on a connected open set containing a root vanishes. -/
theorem ode_unique {I : Set ℂ} (hIc : IsPreconnected I) {e τ g : ℂ} (he : e ∈ I)
    (hI : IsOpen I) (hPe : (e - τ) ^ 2 - g / 4 = 0) {S : ℂ → ℂ} (hS : AnalyticOnNhd ℂ S I)
    (hode : ∀ z ∈ I, ((z - τ) ^ 2 - g / 4) * deriv S z + (z - τ) * S z = 0) :
    ∀ z ∈ I, S z = 0 := by
  have h0 : S =ᶠ[𝓝 e] 0 := by
    have := ode_unique_local hPe (hS e he) (Filter.mem_of_superset (hI.mem_nhds he) hode)
    exact this.mono fun z hz => hz
  exact fun z hz => hS.eqOn_zero_of_preconnected_of_eventuallyEq_zero hIc he h0 hz

end
end NlsGge.Atomic.G4036Unique
