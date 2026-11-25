import NlsGge.Atomic.KSTPath

set_option autoImplicit false

open scoped BigOperators

namespace NlsGge.Atomic.KSTPath

private def bitNat (b : Bool) : ℕ := if b then 1 else 0
private def nearNat (b : Bool) : ℕ := if b then 0 else 1

private theorem nearNat_add_bitNat (b : Bool) : nearNat b + bitNat b = 1 := by
  cases b <;> rfl

private theorem nearPair_identity (a b : Bool) :
    nearNat a * nearNat b + bitNat a + bitNat b = 1 + bitNat a * bitNat b := by
  cases a <;> cases b <;> rfl

private def firstVertex {k : ℕ} (_hk : 0 < k) : Fin (2 * k) := ⟨0, by omega⟩

private def lastVertex {k : ℕ} (_hk : 0 < k) : Fin (2 * k) := ⟨2 * k - 1, by omega⟩

private def leftVertex {k : ℕ} (i : Fin (2 * k - 1)) : Fin (2 * k) :=
  ⟨i.val, by have hi := i.isLt; omega⟩

private def rightVertex {k : ℕ} (i : Fin (2 * k - 1)) : Fin (2 * k) :=
  ⟨i.val + 1, by have hi := i.isLt; omega⟩

private theorem vertexIndex_first {k : ℕ} (hk : 0 < k) :
    vertexIndex hk 0 = (⟨0, by omega⟩ : Fin (2 * k)) := by
  apply Fin.ext
  simp [vertexIndex]

private theorem vertexIndex_last {k : ℕ} (hk : 0 < k) :
    vertexIndex hk (2 * k - 1) = lastVertex hk := by
  rw [vertexIndex_eq_mk hk (by omega)]
  rfl

private theorem vertexIndex_leftVertex {k : ℕ} (hk : 0 < k) (i : Fin (2 * k - 1)) :
    vertexIndex hk i.val = leftVertex i := by
  rw [vertexIndex_eq_mk hk (by omega)]
  rfl

private theorem vertexIndex_rightVertex {k : ℕ} (hk : 0 < k) (i : Fin (2 * k - 1)) :
    vertexIndex hk (i.val + 1) = rightVertex i := by
  rw [vertexIndex_eq_mk hk (by omega)]
  rfl

private theorem forcedTailCount_parts {k : ℕ} (hk : 0 < k) (σ : Pattern k) :
    forcedTailCount hk σ =
      nearNat (σ (firstVertex hk)) +
        (∑ i : Fin (2 * k - 1),
          nearNat (σ (leftVertex i)) * nearNat (σ (rightVertex i))) +
        nearNat (σ (lastVertex hk)) := by
  classical
  have hcard : forcedTailCount hk σ =
      ∑ j : Fin (2 * k + 1), if forcedAt hk σ j then 1 else 0 := by
    unfold forcedTailCount
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hsplit (f : Fin (2 * k) → ℕ) :
      (∑ j : Fin (2 * k), f j) = f (firstVertex hk) +
        ∑ i : Fin (2 * k - 1), f (rightVertex i) := by
    have hsize : (2 * k - 1) + 1 = 2 * k := by omega
    have hdecomp := (finCongr hsize).sum_comp f
    rw [← hdecomp, Fin.sum_univ_succ]
    have hzero : (finCongr hsize) 0 = firstVertex hk := by
      apply Fin.ext
      simp [firstVertex]
    have hnext (i : Fin (2 * k - 1)) :
        (finCongr hsize) i.succ = rightVertex i := by
      apply Fin.ext
      simp [rightVertex]
    rw [hzero]
    congr 1
  let f : Fin (2 * k + 1) → ℕ := fun j => if forcedAt hk σ j then 1 else 0
  have hdecomp : (∑ j : Fin (2 * k + 1), f j) =
      f ⟨0, by omega⟩ +
        (∑ i : Fin (2 * k - 1), f ⟨i.val + 1, by have hi := i.isLt; omega⟩) +
        f ⟨2 * k, by omega⟩ := by
    rw [Fin.sum_univ_castSucc]
    have hs := hsplit (fun j : Fin (2 * k) => f (Fin.castSucc j))
    rw [hs]
    simp [firstVertex, rightVertex]
    apply congrArg f
    apply Fin.ext
    rfl
  rw [hcard, hdecomp]
  have hk0 : k ≠ 0 := by omega
  have hfirst : f ⟨0, by omega⟩ = nearNat (σ (firstVertex hk)) := by
    cases h : σ (⟨0, by omega⟩ : Fin (2 * k)) <;>
      simp [f, forcedAt, nearNat, firstVertex, h]
  have hlast : f ⟨2 * k, by omega⟩ = nearNat (σ (lastVertex hk)) := by
    cases h : σ (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) <;>
      simp [f, forcedAt, nearNat, lastVertex, hk0, vertexIndex_last hk, h]
  have hmiddle : ∀ i : Fin (2 * k - 1),
      f ⟨i.val + 1, by have hi := i.isLt; omega⟩ =
        nearNat (σ (leftVertex i)) * nearNat (σ (rightVertex i)) := by
    intro i
    have hi : i.val + 1 < 2 * k := by have hi' := i.isLt; omega
    cases h₁ : σ (⟨i.val, by have hi' := i.isLt; omega⟩ : Fin (2 * k)) <;>
      cases h₂ : σ (⟨i.val + 1, by have hi' := i.isLt; omega⟩ : Fin (2 * k)) <;>
      simp [f, forcedAt, nearNat, hi, leftVertex, rightVertex,
        vertexIndex_leftVertex hk, vertexIndex_rightVertex hk, h₁, h₂]
  rw [hfirst, hlast]
  have hmidSum : (∑ i : Fin (2 * k - 1), f ⟨i.val + 1, by have hi := i.isLt; omega⟩) =
      ∑ i : Fin (2 * k - 1), nearNat (σ (leftVertex i)) * nearNat (σ (rightVertex i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hmiddle i
  rw [hmidSum]


private theorem patternOnes_eq_bit_sum {k : ℕ} (σ : Pattern k) :
    patternOnes σ = ∑ i : Fin (2 * k), bitNat (σ i) := rfl

private theorem adjacentOnePairs_eq_bit_products {k : ℕ} (σ : Pattern k) :
    adjacentOnePairs σ =
      ∑ i : Fin (2 * k - 1), bitNat (σ (leftVertex i)) *
        bitNat (σ (rightVertex i)) := by
  classical
  unfold adjacentOnePairs
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hleft : (⟨i.val, by omega⟩ : Fin (2 * k)) = leftVertex i := by
    apply Fin.ext
    rfl
  have hright : (⟨i.val + 1, by omega⟩ : Fin (2 * k)) = rightVertex i := by
    apply Fin.ext
    rfl
  rw [hleft, hright]
  cases h₁ : σ (leftVertex i) <;> cases h₂ : σ (rightVertex i) <;> rfl

theorem forcedTailCount_identity {k : ℕ} (hk : 0 < k) (σ : Pattern k) :
    forcedTailCount hk σ + 2 * patternOnes σ =
      2 * k + 1 + adjacentOnePairs σ := by
  classical
  let b₀ : ℕ := bitNat (σ (firstVertex hk))
  let bₘ : ℕ := bitNat (σ (lastVertex hk))
  let z₀ : ℕ := nearNat (σ (firstVertex hk))
  let zₘ : ℕ := nearNat (σ (lastVertex hk))
  have hsize : (2 * k - 1) + 1 = 2 * k := by omega
  have hfirst :
      (∑ i : Fin (2 * k - 1), bitNat (σ (leftVertex i))) + bₘ = patternOnes σ := by
    rw [patternOnes_eq_bit_sum]
    dsimp [bₘ]
    have hdecomp := (finCongr hsize).sum_comp (fun i : Fin (2 * k) => bitNat (σ i))
    rw [← hdecomp, Fin.sum_univ_castSucc]
    have hindex (i : Fin (2 * k - 1)) :
        (finCongr hsize) i.castSucc = leftVertex i := by
      apply Fin.ext
      simp [leftVertex]
    have hlastidx : (finCongr hsize) (Fin.last (2 * k - 1)) = lastVertex hk := by
      apply Fin.ext
      simp [lastVertex]
    have hsum : (∑ i : Fin (2 * k - 1), bitNat (σ ((finCongr hsize) i.castSucc))) =
        ∑ i : Fin (2 * k - 1), bitNat (σ (leftVertex i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hindex]
    have hsum' : (∑ i : Fin (2 * k - 1), bitNat (σ (leftVertex i))) =
        ∑ i : Fin (2 * k - 1), bitNat (σ ((finCongr hsize) i.castSucc)) := hsum.symm
    rw [hsum', hlastidx]
  have htail :
      b₀ + (∑ i : Fin (2 * k - 1), bitNat (σ (rightVertex i))) = patternOnes σ := by
    rw [patternOnes_eq_bit_sum]
    dsimp [b₀]
    have hdecomp := (finCongr hsize).sum_comp (fun i : Fin (2 * k) => bitNat (σ i))
    rw [← hdecomp, Fin.sum_univ_succ]
    have hzero : (finCongr hsize) 0 = firstVertex hk := by
      apply Fin.ext
      simp [firstVertex]
    have hnext (i : Fin (2 * k - 1)) :
        (finCongr hsize) i.succ = rightVertex i := by
      apply Fin.ext
      simp [rightVertex]
    rw [← hzero]
    congr 1
  have hincidence :
      (∑ i : Fin (2 * k - 1),
        (bitNat (σ (leftVertex i)) + bitNat (σ (rightVertex i)))) + b₀ + bₘ =
        2 * patternOnes σ := by
    rw [Finset.sum_add_distrib]
    dsimp [b₀, bₘ]
    omega
  have hendpoints : z₀ + zₘ + b₀ + bₘ = 2 := by
    have h0 := nearNat_add_bitNat (σ (firstVertex hk))
    have hm := nearNat_add_bitNat (σ (lastVertex hk))
    dsimp [z₀, zₘ, b₀, bₘ]
    omega
  have hlocal :
      (∑ i : Fin (2 * k - 1),
        nearNat (σ (leftVertex i)) * nearNat (σ (rightVertex i))) +
      (∑ i : Fin (2 * k - 1),
        (bitNat (σ (leftVertex i)) + bitNat (σ (rightVertex i)))) =
      (2 * k - 1) + adjacentOnePairs σ := by
    calc
      _ = ∑ i : Fin (2 * k - 1),
          (nearNat (σ (leftVertex i)) * nearNat (σ (rightVertex i)) +
            bitNat (σ (leftVertex i)) + bitNat (σ (rightVertex i))) := by
          simp only [Finset.sum_add_distrib]
          omega
      _ = ∑ i : Fin (2 * k - 1),
          (1 + bitNat (σ (leftVertex i)) * bitNat (σ (rightVertex i))) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact nearPair_identity (σ (leftVertex i)) (σ (rightVertex i))
      _ = (2 * k - 1) + adjacentOnePairs σ := by
          rw [Finset.sum_add_distrib, ← adjacentOnePairs_eq_bit_products]
          simp
  rw [forcedTailCount_parts hk σ]
  rw [← hincidence]
  dsimp [b₀, bₘ, z₀, zₘ]
  omega

private theorem endpoint_large {n x : ℤ}
    (hnear : ((x - n).natAbs : ℝ) ≤ (n.natAbs : ℝ) / 2) :
    n.natAbs ≤ (n + x).natAbs := by
  have hcast : |(n : ℝ)| ≤ |((n + x : ℤ) : ℝ)| := by
    have heq : (2 : ℝ) * (n : ℝ) =
        ((n + x : ℤ) : ℝ) - ((x - n : ℤ) : ℝ) := by
      push_cast
      ring
    have htri : |(2 : ℝ) * (n : ℝ)| ≤
        |((n + x : ℤ) : ℝ)| + |((x - n : ℤ) : ℝ)| := by
      calc
        |(2 : ℝ) * (n : ℝ)| =
            |((n + x : ℤ) : ℝ) - ((x - n : ℤ) : ℝ)| := by rw [← heq]
        _ ≤ _ := abs_sub _ _
    have hnear' : |((x - n : ℤ) : ℝ)| ≤ |(n : ℝ)| / 2 := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hnear
    have habs : |(2 : ℝ) * (n : ℝ)| = 2 * |(n : ℝ)| := by
      norm_num [abs_mul]
    rw [habs] at htri
    nlinarith [htri, hnear', abs_nonneg (n : ℝ)]
  have hcast' : (n.natAbs : ℝ) ≤ ((n + x).natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, Int.cast_add] using hcast
  exact_mod_cast hcast'

private theorem adjacent_pair_large {n x y : ℤ}
    (hx : ((x - n).natAbs : ℝ) ≤ (n.natAbs : ℝ) / 2)
    (hy : ((y - n).natAbs : ℝ) ≤ (n.natAbs : ℝ) / 2) :
    n.natAbs ≤ (x + y).natAbs := by
  have hcast : |(n : ℝ)| ≤ |((x + y : ℤ) : ℝ)| := by
    have heq : (2 : ℝ) * (n : ℝ) =
        ((x + y : ℤ) : ℝ) - ((x - n : ℤ) : ℝ) - ((y - n : ℤ) : ℝ) := by
      push_cast
      ring
    have htri : |(2 : ℝ) * (n : ℝ)| ≤
        |((x + y : ℤ) : ℝ)| + |((x - n : ℤ) : ℝ)| + |((y - n : ℤ) : ℝ)| := by
      calc
        |(2 : ℝ) * (n : ℝ)| =
            |((x + y : ℤ) : ℝ) - ((x - n : ℤ) : ℝ) - ((y - n : ℤ) : ℝ)| := by rw [← heq]
        _ ≤ |((x + y : ℤ) : ℝ) - ((x - n : ℤ) : ℝ)| + |((y - n : ℤ) : ℝ)| := abs_sub _ _
        _ ≤ |((x + y : ℤ) : ℝ)| + |((x - n : ℤ) : ℝ)| + |((y - n : ℤ) : ℝ)| := by
          have habs := abs_sub ((x + y : ℤ) : ℝ) ((x - n : ℤ) : ℝ)
          linarith
    have hx' : |((x - n : ℤ) : ℝ)| ≤ |(n : ℝ)| / 2 := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hx
    have hy' : |((y - n : ℤ) : ℝ)| ≤ |(n : ℝ)| / 2 := by
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hy
    have habs : |(2 : ℝ) * (n : ℝ)| = 2 * |(n : ℝ)| := by
      norm_num [abs_mul]
    rw [habs] at htri
    nlinarith [htri, hx', hy', abs_nonneg (n : ℝ)]
  have hcast' : (n.natAbs : ℝ) ≤ ((x + y).natAbs : ℝ) := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, Int.cast_add] using hcast
  exact_mod_cast hcast'

private theorem forcedAt_implies_actual_large {k : ℕ} (hk : 0 < k)
    (n : ℤ) (ℓ : Path k) (σ : Pattern k)
    (hpattern : ∀ i, σ i = nearFarBit n (ℓ i))
    (j : Fin (2 * k + 1)) (hforced : forcedAt hk σ j) :
    n.natAbs ≤ (pathArgument hk n ℓ j).natAbs := by
  classical
  by_cases hjzero : j.val = 0
  · have hj : j = ⟨0, by omega⟩ := Fin.ext hjzero
    rw [hj] at hforced ⊢
    have hnearBit : nearFarBit n (ℓ ⟨0, by omega⟩) = false := by
      rw [← hpattern ⟨0, by omega⟩]
      simpa [forcedAt] using hforced
    have hnear := (nearFarBit_eq_false_iff n _).mp hnearBit
    rw [pathArgument_zero]
    exact endpoint_large hnear
  · by_cases hjlast : j.val = 2 * k
    · have hj : j = ⟨2 * k, by omega⟩ := Fin.ext hjlast
      rw [hj] at hforced ⊢
      have hnearBit : nearFarBit n (ℓ (lastVertex hk)) = false := by
        rw [← hpattern (lastVertex hk)]
        have hk0 : k ≠ 0 := by omega
        simpa [forcedAt, vertexIndex_last hk, hk0] using hforced
      have hnear := (nearFarBit_eq_false_iff n _).mp hnearBit
      rw [pathArgument_last]
      have hidx : lastVertex hk = (⟨2 * k - 1, by omega⟩ : Fin (2 * k)) := rfl
      rw [hidx] at hnear
      simpa [Int.add_comm] using endpoint_large hnear
    · have hjzero' : 0 < j.val := Nat.pos_of_ne_zero hjzero
      have hjlast' : j.val < 2 * k := by omega
      have hnearBits :
          σ (vertexIndex hk (j.val - 1)) = false ∧
          σ (vertexIndex hk j.val) = false := by
        simpa [forcedAt, Nat.ne_of_gt hjzero', hjlast'] using hforced
      let i₀ : Fin (2 * k) := ⟨j.val - 1, by omega⟩
      let i₁ : Fin (2 * k) := ⟨j.val, by omega⟩
      have hidx₀ : vertexIndex hk (j.val - 1) = i₀ := by
        rw [vertexIndex_eq_mk hk (by omega)]
      have hidx₁ : vertexIndex hk j.val = i₁ := by
        rw [vertexIndex_eq_mk hk hjlast']
      have hnearBit₀ : nearFarBit n (ℓ i₀) = false := by
        rw [← hpattern i₀]
        rw [← hidx₀]
        exact hnearBits.1
      have hnearBit₁ : nearFarBit n (ℓ i₁) = false := by
        rw [← hpattern i₁]
        rw [← hidx₁]
        exact hnearBits.2
      have hnear₀ := (nearFarBit_eq_false_iff n _).mp hnearBit₀
      have hnear₁ := (nearFarBit_eq_false_iff n _).mp hnearBit₁
      have hlarge := adjacent_pair_large hnear₀ hnear₁
      have harg : pathArgument hk n ℓ j = ℓ i₀ + ℓ i₁ := by
        simpa [i₀, i₁] using pathArgument_interior hk n ℓ j hjzero' hjlast'
      simpa only [harg] using hlarge

theorem forcedTailCount_le_actualLargeArgs {k : ℕ} (hk : 0 < k)
    (n : ℤ) (ℓ : Path k) (σ : Pattern k)
    (hpattern : ∀ i, σ i = nearFarBit n (ℓ i)) :
    forcedTailCount hk σ ≤ actualLargeArgs hk n ℓ := by
  classical
  unfold forcedTailCount actualLargeArgs
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨Finset.mem_univ _, forcedAt_implies_actual_large hk n ℓ σ hpattern j hj.2⟩

theorem source_forced_tail_arguments_card {k : ℕ} (hk : 0 < k)
    (n : ℤ) (ℓ : Path k) (σ : Pattern k)
    (_hadmissible : admissiblePath n ℓ)
    (hpattern : ∀ i, σ i = nearFarBit n (ℓ i)) :
    2 * k + 1 ≤ actualLargeArgs hk n ℓ + 2 * patternOnes σ := by
  have hcount := forcedTailCount_identity hk σ
  have hlarge := forcedTailCount_le_actualLargeArgs hk n ℓ σ hpattern
  omega


end NlsGge.Atomic.KSTPath
