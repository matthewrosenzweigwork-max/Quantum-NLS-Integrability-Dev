import QuantumNLS.TerraMultiRound23PointSymmetry

/-! Lifting fiber symmetries to the graph of the DEF-049 operator. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ComplexConjugate
namespace QuantumNLS.LocalSpectral.Round23

/-- The pointwise real isometry acts on the interval Hilbert space. -/
def liftFiber (L : ℝ) (T : E2 →ₗᵢ[ℝ] E2) (f : H2 L) : H2 L :=
  T.toContinuousLinearMap.compLp f

/-- A real fiber isometry preserving the boundary scalar and intertwining the
pointwise differential expressions transports the full operator graph. -/
theorem graph_transport (L κ : ℝ) (u v : ℝ → ℂ) (σ : ℤˣ)
    (T : E2 →ₗᵢ[ℝ] E2)
    (hpoint : ∀ x d g, T (lopPt κ (u x) d g) = lopPt κ (v x) (T d) (T g))
    {p : H2 L × H2 L} (hp : p ∈ LuGraph L κ u σ) :
    (liftFiber L T p.1, liftFiber L T p.2) ∈ LuGraph L κ v σ := by
  rcases hp with ⟨g, h, ⟨hfg, hh, hg⟩, hbound, hout⟩
  refine ⟨fun x => T (g x), fun x => T (h x), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · filter_upwards [T.toContinuousLinearMap.coeFn_compLp p.1, hfg] with x hx hxg
    simpa [liftFiber, hxg] using hx
  · exact T.toContinuousLinearMap.comp_memLp' hh
  · intro x hx
    change T (g x) = T (g 0) + ∫ s in (0 : ℝ)..x, T (h s)
    rw [hg x hx, map_add, T.intervalIntegral_comp_comm]
  · change T (g L) = (((σ : ℤ) : ℂ) • T (g 0))
    rw [hbound, Int.cast_smul_eq_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]
  · filter_upwards [T.toContinuousLinearMap.coeFn_compLp p.2, hout] with x hx ho
    change (T.toContinuousLinearMap.compLp p.2) x = lopPt κ (v x) (T (h x)) (T (g x))
    rw [hx, ho]
    exact hpoint x (h x) (g x)

/-- The actual DEF-049 graph is invariant under the anti-linear swap. -/
theorem graph_swapConj (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ)
    {p : H2 L × H2 L} (hp : p ∈ LuGraph L κ u σ) :
    (liftFiber L swapConjIsometry p.1, liftFiber L swapConjIsometry p.2) ∈ LuGraph L κ u σ := by
  apply graph_transport L κ u u σ swapConjIsometry
  · intro x d g
    exact lopPt_swapConj κ (u x) d g
  · exact hp

/-- The actual DEF-049 graph at negative potential is obtained by the
component sign flip. -/
theorem graph_parityFlip (L κ : ℝ) (u : ℝ → ℂ) (σ : ℤˣ)
    {p : H2 L × H2 L} (hp : p ∈ LuGraph L κ u σ) :
    (liftFiber L parityFlipIsometry p.1, liftFiber L parityFlipIsometry p.2) ∈
      LuGraph L κ (fun x => -u x) σ := by
  apply graph_transport L κ u (fun x => -u x) σ parityFlipIsometry
  · intro x d g
    exact lopPt_parityFlip κ (u x) d g
  · exact hp

end QuantumNLS.LocalSpectral.Round23
#print axioms QuantumNLS.LocalSpectral.Round23.graph_transport
#print axioms QuantumNLS.LocalSpectral.Round23.graph_swapConj
#print axioms QuantumNLS.LocalSpectral.Round23.graph_parityFlip
