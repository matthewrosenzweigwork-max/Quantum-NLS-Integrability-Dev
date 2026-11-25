import NlsGge.Analysis.RegularizedDeterminant.Det2

/-!
Invariance of `det2` under real Hilbert-space isometric transport (change of orthonormal
frame), and the rectangular identity `det₂(I + XY) = det₂(I + YX)` for finite-rank `X`.
-/
set_option autoImplicit false
noncomputable section

namespace NlsGge.Analysis.RegularizedDeterminant

open HilbertSchmidt

section Algebra
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem finiteDimensional_range_of_le {B : E →ₗ[ℝ] E} (W : Submodule ℝ E)
    [FiniteDimensional ℝ W] (h : LinearMap.range B ≤ W) :
    FiniteDimensional ℝ (LinearMap.range B) :=
  Submodule.finiteDimensional_of_le h

/-- Rectangular interchange for the intrinsic finite-rank `det₂`; only `X` needs finite rank. -/
theorem finiteRankDet2_comp_comm (X : E →ₗ[ℝ] F) (Y : F →ₗ[ℝ] E)
    (hX : FiniteDimensional ℝ (LinearMap.range X))
    (h1 : FiniteDimensional ℝ (LinearMap.range (X.comp Y)))
    (h2 : FiniteDimensional ℝ (LinearMap.range (Y.comp X))) :
    finiteRankDet2 (X.comp Y) h1 = finiteRankDet2 (Y.comp X) h2 := by
  letI := hX
  set W : Submodule ℝ F := LinearMap.range X
  set U : Submodule ℝ E := W.map Y
  have hW : LinearMap.range (X.comp Y) ≤ W := by
    rintro z ⟨x, rfl⟩
    exact ⟨Y x, rfl⟩
  have hU : LinearMap.range (Y.comp X) ≤ U := by
    rintro z ⟨x, rfl⟩
    exact ⟨X x, ⟨x, rfl⟩, rfl⟩
  rw [finiteRankDet2_eq_restriction _ h1 W hW, finiteRankDet2_eq_restriction _ h2 U hU]
  let Y' : W →ₗ[ℝ] U :=
    { toFun := fun w => ⟨Y (w : F), ⟨(w : F), w.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (map_add Y (a : F) (b : F))
      map_smul' := fun c a => Subtype.ext (map_smul Y c (a : F)) }
  let X' : U →ₗ[ℝ] W :=
    { toFun := fun u => ⟨X (u : E), ⟨(u : E), rfl⟩⟩
      map_add' := fun a b => Subtype.ext (map_add X (a : E) (b : E))
      map_smul' := fun c a => Subtype.ext (map_smul X c (a : E)) }
  have e1 : restrictedEnd (X.comp Y) W hW = X'.comp Y' := by ext; rfl
  have e2 : restrictedEnd (Y.comp X) U hU = Y'.comp X' := by ext; rfl
  rw [e1, e2]
  exact finiteDet2_comp_comm Y' X'

end Algebra

variable {H G : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem transport_sub (S T : HilbertSchmidt H H) (e : H ≃ₗᵢ[ℝ] G) :
    transport S e e - transport T e e = transport (S - T) e e := by
  apply HilbertSchmidt.ext
  intro x
  simp [transportOperator]

theorem continuous_transport (e : H ≃ₗᵢ[ℝ] G) :
    Continuous (fun T : HilbertSchmidt H H => transport T e e) := by
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro S T
  rw [dist_eq_norm, dist_eq_norm, transport_sub, norm_transport]
  simp

theorem finiteRank_transport (T : HilbertSchmidt H H) (hT : HasFiniteRank (toCLM T))
    (e : H ≃ₗᵢ[ℝ] G) : HasFiniteRank (toCLM (transport T e e)) := by
  have : FiniteDimensional ℝ (LinearMap.range (toCLM T).toLinearMap) := hT
  apply finiteDimensional_range_of_le
    ((LinearMap.range (toCLM T).toLinearMap).map e.toLinearEquiv.toLinearMap)
  rintro z ⟨x, rfl⟩
  exact ⟨toCLM T (e.symm x), ⟨e.symm x, rfl⟩, rfl⟩

/-- Finite-rank case of transport invariance. -/
theorem det2_transport_of_finiteRank (T : HilbertSchmidt H H) (hT : HasFiniteRank (toCLM T))
    (e : H ≃ₗᵢ[ℝ] G) : det2 (transport T e e) = det2 T := by
  rw [det2_of_finiteRank _ (finiteRank_transport T hT e), det2_of_finiteRank T hT]
  let X : H →ₗ[ℝ] G := e.toLinearEquiv.toLinearMap.comp (toCLM T).toLinearMap
  let Y : G →ₗ[ℝ] H := e.symm.toLinearEquiv.toLinearMap
  have hX : FiniteDimensional ℝ (LinearMap.range X) := by
    have : FiniteDimensional ℝ (LinearMap.range (toCLM T).toLinearMap) := hT
    rw [LinearMap.range_comp]
    infer_instance
  have hXY : (toCLM (transport T e e)).toLinearMap = X.comp Y := by
    ext x; simp [X, Y, transportOperator]
  have hYX : (toCLM T).toLinearMap = Y.comp X := by
    ext x; simp [X, Y]
  have h1 : FiniteDimensional ℝ (LinearMap.range (X.comp Y)) := by
    rw [← hXY]; exact finiteRank_transport T hT e
  have h2 : FiniteDimensional ℝ (LinearMap.range (Y.comp X)) := by
    rw [← hYX]; exact hT
  have k1 : finiteRankDet2 (toCLM (transport T e e)).toLinearMap
      (finiteRank_transport T hT e) = finiteRankDet2 (X.comp Y) h1 := by
    congr 1
  have k2 : finiteRankDet2 (toCLM T).toLinearMap hT = finiteRankDet2 (Y.comp X) h2 := by
    congr 1
  rw [k1, k2]
  exact finiteRankDet2_comp_comm X Y hX h1 h2

/-- **Isometric transport invariance** of the real HS regularized determinant:
`det₂(I + U B U⁻¹) = det₂(I + B)` for every real linear isometric equivalence `U : H ≃ G`. -/
theorem det2_transport (T : HilbertSchmidt H H) (e : H ≃ₗᵢ[ℝ] G) :
    det2 (transport T e e) = det2 T := by
  have h := det2_unique (H := H) (fun S => det2 (transport S e e))
    (continuous_det2.comp (continuous_transport e))
    (fun B hB => by
      rw [det2_transport_of_finiteRank B hB e, det2_of_finiteRank B hB])
  exact congrFun h T

end NlsGge.Analysis.RegularizedDeterminant
