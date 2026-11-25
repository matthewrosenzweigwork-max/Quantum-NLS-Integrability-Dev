import QuantumNLS.Ext006HeisVacuumR37a

/-! Irreducibility in the literal frozen Heisenberg formulation. Both rows
recover every next occupation column from the preceding column. Density then
proves phase uniqueness on the WHOLE physical Fock space for all implementers. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace
namespace QuantumNLS.Ext006ImplementerUniqueR37a
open Occupation Ext006VacuumRecurrence Ext006BogoliubovAlg Ext006QuasifreeWeak
open Ext006PhysFockCoord Ext006PhysQuasifree Ext006PhysSymplectic
open Ext006HeisVacuumR37a Ext006SmoothOperatorsR34a

lemma first_rows_eq {A B : H →L[ℂ] H} (hs : PhysSymplectic A B)
    {u w p q : H} (hX : A u+B w=A p+B q) (hY : bar A w+bar B u=bar A q+bar B p) : u=p := by
  have h₁ := invpair_identity hs (u := u) (w := w) rfl
    (show bar A w+bar B u=star (A (star w))+star (B (star u)) by rw [bar_apply,bar_apply])
  have h₂ := invpair_identity hs (u := p) (w := q) rfl
    (show bar A q+bar B p=star (A (star q))+star (B (star p)) by rw [bar_apply,bar_apply])
  rw [hX,hY] at h₁
  exact h₁.trans h₂.symm

lemma rows_injective {A B : H →L[ℂ] H} (hs : PhysSymplectic A B)
    {u w p q : H} (hX : A u+B w=A p+B q) (hY : bar A w+bar B u=bar A q+bar B p) :
    u=p ∧ w=q := by
  refine ⟨first_rows_eq hs hX hY,?_⟩
  apply star_injective
  apply first_rows_eq hs (u := star w) (w := star u) (p := star q) (q := star p)
  · simpa only [bar_apply,star_add,star_star] using congrArg star hY
  · simpa only [bar_apply,star_add,star_star] using congrArg star hX

lemma yvec_smul (c : ℂ) (z : Fock) (n : Occ) : yvec (c • z) n=c • yvec z n := by
  apply lp.ext
  funext a
  change (Real.sqrt (n a : ℝ) : ℂ)*(c*z (n-e a))=c*((Real.sqrt (n a : ℝ) : ℂ)*z (n-e a))
  ring

variable {L : ℝ} [Fact (0 < L)]

lemma column_step
    (V W : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (A B : H →L[ℂ] H) (hs : PhysSymplectic A B)
    (hVA : HeisAnn V A B) (hVC : HeisCre V A B)
    (hWA : HeisAnn W A B) (hWC : HeisCre W A B)
    (c : ℂ) (m : Occ)
    (hm : Vtil W (lp.single 2 m 1)=c • Vtil V (lp.single 2 m 1)) (a : ℤ) :
    Vtil W (lp.single 2 (m+e a) 1)=c • Vtil V (lp.single 2 (m+e a) 1) := by
  apply lp.ext
  funext n
  obtain ⟨hVX,hVY⟩ := heis_rows V A B hVA hVC n m
  obtain ⟨hWX,hWY⟩ := heis_rows W A B hWA hWC n m
  have hX : A (uvec W n m)+B (wvec W n m)=A (c • uvec V n m)+B (c • wvec V n m) := by
    rw [← hWX,map_smul,map_smul,← smul_add,← hVX,hm,xvec_smul]
  have hY : bar A (wvec W n m)+bar B (uvec W n m)=
      bar A (c • wvec V n m)+bar B (c • uvec V n m) := by
    rw [← hWY,map_smul,map_smul,← smul_add,← hVY,hm,yvec_smul]
  have hw := congrArg (fun z : H => z a) (rows_injective hs hX hY).2
  change wvec W n m a=c*wvec V n m a at hw
  rw [wvec_apply,inner_Cre_core,wvec_apply,inner_Cre_core,
    ← Vtil_single_apply,← Vtil_single_apply] at hw
  change Vtil W (lp.single 2 (m+e a) 1) n=c*Vtil V (lp.single 2 (m+e a) 1) n
  have hq : (Real.sqrt ((m a : ℝ)+1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (show 0 < (m a : ℝ)+1 by positivity)).ne'
  apply mul_left_cancel₀ hq
  calc
    _ = c*((Real.sqrt ((m a : ℝ)+1) : ℂ)*Vtil V (lp.single 2 (m+e a) 1) n) := hw
    _ = _ := by ring

lemma columns_from_vacuum
    (V W : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (A B : H →L[ℂ] H) (hs : PhysSymplectic A B)
    (hVA : HeisAnn V A B) (hVC : HeisCre V A B)
    (hWA : HeisAnn W A B) (hWC : HeisCre W A B)
    (c : ℂ) (h₀ : Vtil W vacuum=c • Vtil V vacuum) (m : Occ) :
    Vtil W (lp.single 2 m 1)=c • Vtil V (lp.single 2 m 1) := by
  have h : ∀ k : ℕ, ∀ m : Occ, total m=k →
      Vtil W (lp.single 2 m 1)=c • Vtil V (lp.single 2 m 1) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m hmk
      by_cases hm : m=0
      · subst m
        exact h₀
      · obtain ⟨a,ha⟩ : ∃ a, m a ≠ 0 := by
          by_contra! hz
          exact hm (Finsupp.ext hz)
        have hma : 1 ≤ m a := Nat.one_le_iff_ne_zero.mpr ha
        have ht := total_sub_e hma
        have hk := ih (total (m-e a)) (by omega) (m-e a) rfl
        have he := column_step V W A B hs hVA hVC hWA hWC c (m-e a) hk a
        rwa [shift_sub_add hma] at he
  exact h (total m) m rfl

/-- Phase uniqueness for ALL literal frozen HeisAnn/HeisCre implementers,
with no smoothness or creator-word-action assumption on either implementer. -/
theorem implementer_unique_phase
    (V W : Ext025B3PhysicalSectors.Fock L ≃ₗᵢ[ℂ] Ext025B3PhysicalSectors.Fock L)
    (A B : H →L[ℂ] H) (hs : PhysSymplectic A B)
    (hVA : HeisAnn V A B) (hVC : HeisCre V A B)
    (hWA : HeisAnn W A B) (hWC : HeisCre W A B) :
    ∃ c : ℂ, ‖c‖=1 ∧ ∀ x : Ext025B3PhysicalSectors.Fock L, W x=c • V x := by
  obtain ⟨c,hc,h₀⟩ := all_implementer_vacua_phase V W A B hs hVA hVC hWA hWC
  have hunit (m : Occ) : Vtil W (lp.single 2 m 1)=c • Vtil V (lp.single 2 m 1) :=
    columns_from_vacuum V W A B hs hVA hVC hWA hWC c h₀ m
  have hall (z : Fock) : Vtil W z=c • Vtil V z := by
    have hW := (Vtil W).toLinearIsometry.toContinuousLinearMap.hasSum (lp.hasSum_single (by norm_num) z)
    have hV := ((Vtil V).toLinearIsometry.toContinuousLinearMap.hasSum (lp.hasSum_single (by norm_num) z)).const_smul c
    have hterm (m : Occ) : Vtil W (lp.single 2 m (z m))=c • Vtil V (lp.single 2 m (z m)) := by
      have he : (lp.single 2 m (z m) : Fock)=z m • lp.single 2 m 1 := by
        rw [← lp.single_smul]
        simp
      rw [he,map_smul,map_smul,hunit,smul_smul,smul_smul,mul_comm (z m) c]
    change HasSum (fun m : Occ => Vtil W (lp.single 2 m (z m))) (Vtil W z) at hW
    simp only [hterm] at hW
    exact hW.unique hV
  refine ⟨c,hc,fun x => ?_⟩
  apply (Phi (L := L)).injective
  have h := hall (Phi x)
  simpa only [Vtil_apply,LinearIsometryEquiv.symm_apply_apply,map_smul] using h

end QuantumNLS.Ext006ImplementerUniqueR37a

#print axioms QuantumNLS.Ext006ImplementerUniqueR37a.rows_injective

#print axioms QuantumNLS.Ext006ImplementerUniqueR37a.column_step

#print axioms QuantumNLS.Ext006ImplementerUniqueR37a.columns_from_vacuum

#print axioms QuantumNLS.Ext006ImplementerUniqueR37a.implementer_unique_phase

set_option maxHeartbeats 8000000 in
run_cmd do
  let env ← Lean.getEnv
  let mut pending : Array Lean.Name := #[]
  let mut roots : Nat := 0
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "QuantumNLS.Ext006ImplementerUniqueR37a." then
      pending := pending.push n
      roots := roots + 1
  let mut seen : Std.HashSet Lean.Name := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      if let some ci := env.find? n then
        match ci with
        | .axiomInfo _ =>
          unless n == ``propext || n == ``Classical.choice || n == ``Quot.sound do
            throwError "Nonstandard dependency: {n}"
        | _ => pure ()
        pending := pending ++ ci.type.getUsedConstants
        if let some v := ci.value? (allowOpaque := true) then
          pending := pending ++ v.getUsedConstants
      else
        throwError "Missing dependency: {n}"
  Lean.logInfo m!"Round37a aggregate audit PASS: {roots} own constants; {seen.size} transitive constants; standard only."
