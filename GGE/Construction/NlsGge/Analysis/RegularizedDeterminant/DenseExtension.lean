import Mathlib

/-!
# Extension of locally Lipschitz maps from a dense set to the real line

A real function on a dense subset `S` of a normed group `X` satisfying the local Lipschitz bound
`|f a - f b| ≤ ‖a - b‖ * K (‖a‖ + ‖b‖)` (with `K` continuous and monotone) extends to all of `X`
with the same bound.
-/

open Filter Topology

namespace NlsGge.Analysis.RegularizedDeterminant

section

variable {X : Type*} [NormedAddCommGroup X]

/-- Along `𝓝[S] x` the function `f` is Cauchy (`S` dense, local Lipschitz bound). -/
private lemma cauchy_map_nhdsWithin (S : Set X) (hS : Dense S) (f : X → ℝ) (K : ℝ → ℝ)
    (hKm : Monotone K)
    (hf : ∀ a ∈ S, ∀ b ∈ S, |f a - f b| ≤ ‖a - b‖ * K (‖a‖ + ‖b‖)) (x : X) :
    Cauchy (map f (𝓝[S] x)) := by
  have : (𝓝[S] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hS x)
  rw [Metric.cauchy_iff]
  refine ⟨inferInstance, fun ε hε => ?_⟩
  set C : ℝ := max (K (2 * ‖x‖ + 2)) 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  set δ : ℝ := min 1 (ε / (4 * C + 4)) with hδ
  have hpos : 0 < ε / (4 * C + 4) := by positivity
  have hδpos : 0 < δ := lt_min one_pos hpos
  refine ⟨f '' (S ∩ Metric.ball x δ), ?_, ?_⟩
  · apply image_mem_map
    exact inter_mem_nhdsWithin S (Metric.ball_mem_nhds x hδpos)
  · rintro _ ⟨a, ⟨haS, hax⟩, rfl⟩ _ ⟨b, ⟨hbS, hbx⟩, rfl⟩
    rw [Real.dist_eq]
    have h1 : ‖a - x‖ < δ := by simpa [dist_eq_norm] using hax
    have h2 : ‖b - x‖ < δ := by simpa [dist_eq_norm] using hbx
    have hδ1 : δ ≤ 1 := min_le_left _ _
    have hδ2 : δ ≤ ε / (4 * C + 4) := min_le_right _ _
    have ha : ‖a‖ ≤ ‖x‖ + δ := by
      have := norm_le_insert' a x
      linarith
    have hb : ‖b‖ ≤ ‖x‖ + δ := by
      have := norm_le_insert' b x
      linarith
    have hK : K (‖a‖ + ‖b‖) ≤ C :=
      (hKm (by linarith : ‖a‖ + ‖b‖ ≤ 2 * ‖x‖ + 2)).trans (le_max_left _ _)
    have hab : ‖a - b‖ ≤ 2 * δ := by
      have := norm_sub_le (a - x) (b - x)
      have e : a - b = (a - x) - (b - x) := by abel
      rw [e]
      linarith
    have hn : 0 ≤ ‖a - b‖ := norm_nonneg _
    calc |f a - f b| ≤ ‖a - b‖ * K (‖a‖ + ‖b‖) := hf a haS b hbS
      _ ≤ ‖a - b‖ * C := mul_le_mul_of_nonneg_left hK hn
      _ ≤ (2 * δ) * C := mul_le_mul_of_nonneg_right hab hC0
      _ ≤ (2 * (ε / (4 * C + 4))) * C := by gcongr
      _ < ε := by
        have h4 : 0 < 4 * C + 4 := by positivity
        have : (2 * (ε / (4 * C + 4))) * C = ε * (2 * C) / (4 * C + 4) := by
          field_simp
        rw [this, div_lt_iff₀ h4]
        nlinarith

/-- A real function on a dense subset of a normed group satisfying a local Lipschitz bound with
continuous monotone modulus `K` extends to the whole space with the same bound. -/
theorem exists_extension_of_dense_locallyLipschitz {X : Type*} [NormedAddCommGroup X]
    (S : Set X) (hS : Dense S) (f : X → ℝ) (K : ℝ → ℝ) (hKc : Continuous K)
    (hKm : Monotone K)
    (hf : ∀ a ∈ S, ∀ b ∈ S, |f a - f b| ≤ ‖a - b‖ * K (‖a‖ + ‖b‖)) :
    ∃ g : X → ℝ, (∀ a ∈ S, g a = f a) ∧
      (∀ x y, |g x - g y| ≤ ‖x - y‖ * K (‖x‖ + ‖y‖)) := by
  classical
  have hcau := cauchy_map_nhdsWithin S hS f K hKm hf
  have hne : ∀ x, (𝓝[S] x).NeBot := fun x => mem_closure_iff_nhdsWithin_neBot.mp (hS x)
  have hex : ∀ x, ∃ y, Tendsto f (𝓝[S] x) (𝓝 y) := fun x =>
    cauchy_map_iff_exists_tendsto.mp (hcau x)
  set g : X → ℝ := fun x => limUnder (𝓝[S] x) f with hg
  have hgt : ∀ x, Tendsto f (𝓝[S] x) (𝓝 (g x)) := fun x => tendsto_nhds_limUnder (hex x)
  refine ⟨g, ?_, ?_⟩
  · intro a haS
    have : (𝓝[S] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hS a)
    refine tendsto_nhds_unique (hgt a) ?_
    rw [tendsto_iff_dist_tendsto_zero]
    have hlim : Tendsto (fun b : X => ‖b - a‖ * K (‖b‖ + ‖a‖)) (𝓝[S] a) (𝓝 0) := by
      have h0 : Tendsto (fun b : X => ‖b - a‖ * K (‖b‖ + ‖a‖)) (𝓝 a) (𝓝 (‖a - a‖ * K (‖a‖ + ‖a‖))) := by
        refine Tendsto.mul ?_ ?_
        · exact ((continuous_id.sub continuous_const).norm).tendsto a
        · exact (hKc.comp (continuous_norm.add continuous_const)).tendsto a
      simp only [sub_self, norm_zero, zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with b hb
    rw [Real.dist_eq]
    exact hf b hb a haS
  · intro x y
    have : (𝓝[S] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hS x)
    have : (𝓝[S] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hS y)
    have hL : Tendsto (fun p : X × X => |f p.1 - f p.2|) (𝓝[S] x ×ˢ 𝓝[S] y)
        (𝓝 |g x - g y|) := by
      have h1 := (hgt x).prodMap (hgt y)
      have h2 : Tendsto (fun p : ℝ × ℝ => |p.1 - p.2|) (𝓝 (g x) ×ˢ 𝓝 (g y))
          (𝓝 |g x - g y|) := by
        rw [← nhds_prod_eq]
        exact (continuous_abs.comp (continuous_fst.sub continuous_snd)).tendsto _
      exact h2.comp h1
    have hR : Tendsto (fun p : X × X => ‖p.1 - p.2‖ * K (‖p.1‖ + ‖p.2‖))
        (𝓝[S] x ×ˢ 𝓝[S] y) (𝓝 (‖x - y‖ * K (‖x‖ + ‖y‖))) := by
      have hc : Continuous (fun p : X × X => ‖p.1 - p.2‖ * K (‖p.1‖ + ‖p.2‖)) := by
        fun_prop
      have h0 := hc.tendsto (x, y)
      rw [nhds_prod_eq] at h0
      exact h0.mono_left (prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds)
    refine le_of_tendsto_of_tendsto hL hR ?_
    have hmem : ∀ᶠ p : X × X in 𝓝[S] x ×ˢ 𝓝[S] y, p.1 ∈ S ∧ p.2 ∈ S := by
      have h1 : ∀ᶠ p : X × X in 𝓝[S] x ×ˢ 𝓝[S] y, p.1 ∈ S :=
        tendsto_fst.eventually (self_mem_nhdsWithin : S ∈ 𝓝[S] x)
      have h2 : ∀ᶠ p : X × X in 𝓝[S] x ×ˢ 𝓝[S] y, p.2 ∈ S :=
        tendsto_snd.eventually (self_mem_nhdsWithin : S ∈ 𝓝[S] y)
      exact h1.and h2
    filter_upwards [hmem] with p hp
    exact hf p.1 hp.1 p.2 hp.2

/-- A function with the local Lipschitz bound is sequentially/filter continuous. -/
theorem tendsto_of_locallyLipschitz {X : Type*} [NormedAddCommGroup X] (g : X → ℝ) (K : ℝ → ℝ)
    (hKc : Continuous K) (hg : ∀ x y, |g x - g y| ≤ ‖x - y‖ * K (‖x‖ + ‖y‖))
    {J : Type*} (l : Filter J) (a : J → X) (x : X) (ha : Tendsto a l (𝓝 x)) :
    Tendsto (fun n => g (a n)) l (𝓝 (g x)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hc : Continuous (fun y : X => ‖y - x‖ * K (‖y‖ + ‖x‖)) := by fun_prop
  have h0 := (hc.tendsto x).comp ha
  simp only [Function.comp_def, sub_self, norm_zero, zero_mul] at h0
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) h0
  rw [Real.dist_eq]
  exact hg (a n) x

end

end NlsGge.Analysis.RegularizedDeterminant
