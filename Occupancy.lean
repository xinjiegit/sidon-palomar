/-
SPDX-License-Identifier: GPL-3.0-only
Exact expectations for half-density circular cells under a random affine map.
-/
module

public import Affine
public import CellGeometry

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace SidonResearch

variable {m : ℕ} [NeZero m]

noncomputable def hit (a : ℤ) (j : ZMod m) (ω : Sample) : ℝ := by
  classical
  exact if affine a ω ∈ cell m j then 1 else 0

noncomputable def pairHit (a b : ℤ) (j : ZMod m) (ω : Sample) : ℝ := by
  classical
  exact if affine a ω ∈ cell m j ∧ affine b ω ∈ cell m j then 1 else 0

theorem integrable_hit (a : ℤ) (j : ZMod m) : Integrable (hit a j) sampleMeasure := by
  change Integrable ((affine a ⁻¹' cell m j).indicator (fun _ => (1 : ℝ))) sampleMeasure
  exact (integrable_const 1).indicator
    ((measurableSet_cell j).preimage (affine_measurePreserving a).measurable)

theorem integral_hit (a : ℤ) (j : ZMod m) :
    ∫ ω, hit a j ω ∂sampleMeasure = 1 / (2 * (m : ℝ)) := by
  change (∫ ω, (affine a ⁻¹' cell m j).indicator (fun _ => (1 : ℝ)) ω ∂sampleMeasure) = _
  rw [integral_indicator_const 1
    ((measurableSet_cell j).preimage (affine_measurePreserving a).measurable)]
  simp only [smul_eq_mul, mul_one]
  have hmeasure := (affine_measurePreserving a).measure_preimage
    (measurableSet_cell j).nullMeasurableSet
  rw [MeasureTheory.measureReal_def, hmeasure]
  exact volume_real_cell j

theorem integrable_pairHit (a b : ℤ) (j : ZMod m) : Integrable (pairHit a b j) sampleMeasure := by
  have hfun : pairHit a b j = ((affine a ⁻¹' cell m j) ∩
      (affine b ⁻¹' cell m j)).indicator (fun _ => (1 : ℝ)) := by
    classical
    funext ω
    simp only [pairHit, Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage]
  rw [hfun]
  exact (integrable_const 1).indicator
    (((measurableSet_cell j).preimage (affine_measurePreserving a).measurable).inter
    ((measurableSet_cell j).preimage (affine_measurePreserving b).measurable))

theorem integral_pairHit {a b : ℤ} (hab : a ≠ b) (j : ZMod m) :
    ∫ ω, pairHit a b j ω ∂sampleMeasure = (1 / (2 * (m : ℝ)))^2 := by
  have hmeas := (measurableSet_cell j).prod (measurableSet_cell j)
  have hfun : pairHit a b j = (affinePair a b ⁻¹' (cell m j ×ˢ cell m j)).indicator
      (fun _ => (1 : ℝ)) := by
    classical
    funext ω
    simp only [pairHit, Set.indicator_apply, Set.mem_preimage, Set.mem_prod, affinePair, AddMonoidHom.prod_apply]
  rw [hfun]
  rw [integral_indicator_const 1
    (hmeas.preimage (affinePair_measurePreserving hab).measurable)]
  simp only [smul_eq_mul, mul_one]
  have hmeasure := (affinePair_measurePreserving hab).measure_preimage hmeas.nullMeasurableSet
  rw [MeasureTheory.measureReal_def, hmeasure]
  change sampleMeasure.real (cell m j ×ˢ cell m j) = _
  rw [sampleMeasure, measureReal_prod_prod, volume_real_cell]
  ring

/-- Number retained minus one half the number of ordered same-cell collisions. -/
noncomputable def occupancyScore (A : Finset ℤ) (m : ℕ) [NeZero m] (ω : Sample) : ℝ :=
  (∑ a ∈ A, ∑ j : ZMod m, hit a j ω) -
    (1/2) * ∑ p ∈ A.offDiag, ∑ j : ZMod m, pairHit p.1 p.2 j ω

theorem integrable_occupancyScore (A : Finset ℤ) (m : ℕ) [NeZero m] :
    Integrable (occupancyScore A m) sampleMeasure := by
  apply Integrable.sub
  · exact integrable_finsetSum A fun a _ =>
      integrable_finsetSum Finset.univ fun j _ => integrable_hit a j
  · apply Integrable.const_mul
    exact integrable_finsetSum A.offDiag fun p _ =>
      integrable_finsetSum Finset.univ fun j _ => integrable_pairHit p.1 p.2 j

theorem integral_occupancyScore (A : Finset ℤ) (m : ℕ) [NeZero m] :
    ∫ ω, occupancyScore A m ω ∂sampleMeasure =
      (A.card : ℝ) / 2 - (A.card : ℝ) * ((A.card : ℝ) - 1) / (8 * (m : ℝ)) := by
  have hh : Integrable (fun ω => ∑ a ∈ A, ∑ j : ZMod m, hit a j ω) sampleMeasure :=
    integrable_finsetSum A fun a _ =>
      integrable_finsetSum Finset.univ fun j _ => integrable_hit a j
  have hp : Integrable (fun ω => ∑ p ∈ A.offDiag, ∑ j : ZMod m, pairHit p.1 p.2 j ω)
      sampleMeasure := integrable_finsetSum A.offDiag fun p _ =>
      integrable_finsetSum Finset.univ fun j _ => integrable_pairHit p.1 p.2 j
  unfold occupancyScore
  rw [integral_sub hh (hp.const_mul _), integral_const_mul,
    integral_finsetSum A (fun a _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_hit a j)),
    integral_finsetSum A.offDiag (fun p _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_pairHit p.1 p.2 j))]
  have hs : ∀ a ∈ A, (∫ ω, ∑ j : ZMod m, hit a j ω ∂sampleMeasure) =
      (m : ℝ) * (1/(2*(m : ℝ))) := by
    intro a _
    rw [integral_finsetSum Finset.univ (fun j _ => integrable_hit a j)]
    simp [integral_hit, ZMod.card, nsmul_eq_mul]
  have ht : ∀ p ∈ A.offDiag, (∫ ω, ∑ j : ZMod m, pairHit p.1 p.2 j ω ∂sampleMeasure) =
      (m : ℝ) * (1/(2*(m : ℝ)))^2 := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    rw [integral_finsetSum Finset.univ (fun j _ => integrable_pairHit p.1 p.2 j)]
    simp [integral_pairHit hne, ZMod.card, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hs, Finset.sum_congr rfl ht]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((A.offDiag.card : ℕ) : ℝ) = (A.card : ℝ) * ((A.card : ℝ) - 1) := by
    rw [Finset.offDiag_card, Nat.cast_sub (by nlinarith : A.card ≤ A.card * A.card), Nat.cast_mul]
    ring
  rw [hcard]
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  field_simp
  ring

theorem exists_good_sample (A : Finset ℤ) (m : ℕ) [NeZero m] :
    ∃ ω : Sample, (A.card : ℝ) / 2 -
      (A.card : ℝ) * ((A.card : ℝ) - 1) / (8 * (m : ℝ)) ≤ occupancyScore A m ω := by
  obtain ⟨ω, hω⟩ := exists_integral_le (integrable_occupancyScore A m)
  exact ⟨ω, by rwa [integral_occupancyScore] at hω⟩

end SidonResearch
