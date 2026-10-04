/-
SPDX-License-Identifier: GPL-3.0-only
Exact expectations for variable-density circular cells under a random affine map.
-/
module

public import Affine
public import GeneralCellGeometry

@[expose] public section

open MeasureTheory
open scoped BigOperators

namespace SidonResearch

variable (δ : ℝ) {m : ℕ} [NeZero m]

noncomputable def deltaHit (a : ℤ) (j : ZMod m) (ω : Sample) : ℝ := by
  classical
  exact if affine a ω ∈ deltaCell δ m j then 1 else 0

noncomputable def deltaPairHit (a b : ℤ) (j : ZMod m) (ω : Sample) : ℝ := by
  classical
  exact if affine a ω ∈ deltaCell δ m j ∧ affine b ω ∈ deltaCell δ m j then 1 else 0

theorem integrable_deltaHit (a : ℤ) (j : ZMod m) : Integrable (deltaHit δ a j) sampleMeasure := by
  change Integrable ((affine a ⁻¹' deltaCell δ m j).indicator (fun _ => (1 : ℝ))) sampleMeasure
  exact (integrable_const 1).indicator
    ((measurableSet_deltaCell δ j).preimage (affine_measurePreserving a).measurable)

theorem integral_deltaHit (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) (a : ℤ) (j : ZMod m) :
    ∫ ω, deltaHit δ a j ω ∂sampleMeasure = δ / (m : ℝ) := by
  change (∫ ω, (affine a ⁻¹' deltaCell δ m j).indicator (fun _ => (1 : ℝ)) ω ∂sampleMeasure) = _
  rw [integral_indicator_const 1
    ((measurableSet_deltaCell δ j).preimage (affine_measurePreserving a).measurable)]
  simp only [smul_eq_mul, mul_one]
  have hmeasure := (affine_measurePreserving a).measure_preimage
    (measurableSet_deltaCell δ j).nullMeasurableSet
  rw [MeasureTheory.measureReal_def, hmeasure]
  exact volume_real_deltaCell hδ0 hδ j

theorem integrable_deltaPairHit (a b : ℤ) (j : ZMod m) : Integrable (deltaPairHit δ a b j) sampleMeasure := by
  have hfun : deltaPairHit δ a b j = ((affine a ⁻¹' deltaCell δ m j) ∩
      (affine b ⁻¹' deltaCell δ m j)).indicator (fun _ => (1 : ℝ)) := by
    classical
    funext ω
    simp only [deltaPairHit, Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage]
  rw [hfun]
  exact (integrable_const 1).indicator
    (((measurableSet_deltaCell δ j).preimage (affine_measurePreserving a).measurable).inter
    ((measurableSet_deltaCell δ j).preimage (affine_measurePreserving b).measurable))

theorem integral_deltaPairHit (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) {a b : ℤ} (hab : a ≠ b) (j : ZMod m) :
    ∫ ω, deltaPairHit δ a b j ω ∂sampleMeasure = (δ / (m : ℝ))^2 := by
  have hmeas := (measurableSet_deltaCell δ j).prod (measurableSet_deltaCell δ j)
  have hfun : deltaPairHit δ a b j = (affinePair a b ⁻¹' (deltaCell δ m j ×ˢ deltaCell δ m j)).indicator
      (fun _ => (1 : ℝ)) := by
    classical
    funext ω
    simp only [deltaPairHit, Set.indicator_apply, Set.mem_preimage, Set.mem_prod, affinePair, AddMonoidHom.prod_apply]
  rw [hfun]
  rw [integral_indicator_const 1
    (hmeas.preimage (affinePair_measurePreserving hab).measurable)]
  simp only [smul_eq_mul, mul_one]
  have hmeasure := (affinePair_measurePreserving hab).measure_preimage hmeas.nullMeasurableSet
  rw [MeasureTheory.measureReal_def, hmeasure]
  change sampleMeasure.real (deltaCell δ m j ×ˢ deltaCell δ m j) = _
  rw [sampleMeasure, measureReal_prod_prod, volume_real_deltaCell hδ0 hδ]
  ring

/-- Number retained minus one half the number of ordered same-cell collisions. -/
noncomputable def deltaOccupancyScore (A : Finset ℤ) (m : ℕ) [NeZero m] (ω : Sample) : ℝ :=
  (∑ a ∈ A, ∑ j : ZMod m, deltaHit δ a j ω) -
    (1/2) * ∑ p ∈ A.offDiag, ∑ j : ZMod m, deltaPairHit δ p.1 p.2 j ω

theorem integrable_deltaOccupancyScore (A : Finset ℤ) (m : ℕ) [NeZero m] :
    Integrable (deltaOccupancyScore δ A m) sampleMeasure := by
  apply Integrable.sub
  · exact integrable_finsetSum A fun a _ =>
      integrable_finsetSum Finset.univ fun j _ => integrable_deltaHit δ a j
  · apply Integrable.const_mul
    exact integrable_finsetSum A.offDiag fun p _ =>
      integrable_finsetSum Finset.univ fun j _ => integrable_deltaPairHit δ p.1 p.2 j

theorem integral_deltaOccupancyScore (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) (A : Finset ℤ) (m : ℕ) [NeZero m] :
    ∫ ω, deltaOccupancyScore δ A m ω ∂sampleMeasure =
      δ * (A.card : ℝ) - δ^2 * (A.card : ℝ) * ((A.card : ℝ) - 1) / (2 * (m : ℝ)) := by
  have hh : Integrable (fun ω => ∑ a ∈ A, ∑ j : ZMod m, deltaHit δ a j ω) sampleMeasure :=
    integrable_finsetSum A fun a _ =>
      integrable_finsetSum Finset.univ fun j _ => integrable_deltaHit δ a j
  have hp : Integrable (fun ω => ∑ p ∈ A.offDiag, ∑ j : ZMod m, deltaPairHit δ p.1 p.2 j ω)
      sampleMeasure := integrable_finsetSum A.offDiag fun p _ =>
      integrable_finsetSum Finset.univ fun j _ => integrable_deltaPairHit δ p.1 p.2 j
  unfold deltaOccupancyScore
  rw [integral_sub hh (hp.const_mul _), integral_const_mul,
    integral_finsetSum A (fun a _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_deltaHit δ a j)),
    integral_finsetSum A.offDiag (fun p _ => integrable_finsetSum Finset.univ
      (fun j _ => integrable_deltaPairHit δ p.1 p.2 j))]
  have hs : ∀ a ∈ A, (∫ ω, ∑ j : ZMod m, deltaHit δ a j ω ∂sampleMeasure) =
      (m : ℝ) * (δ/(m : ℝ)) := by
    intro a _
    rw [integral_finsetSum Finset.univ (fun j _ => integrable_deltaHit δ a j)]
    simp [integral_deltaHit δ hδ0 hδ, ZMod.card, nsmul_eq_mul]
  have ht : ∀ p ∈ A.offDiag, (∫ ω, ∑ j : ZMod m, deltaPairHit δ p.1 p.2 j ω ∂sampleMeasure) =
      (m : ℝ) * (δ/(m : ℝ))^2 := by
    intro p hp
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    rw [integral_finsetSum Finset.univ (fun j _ => integrable_deltaPairHit δ p.1 p.2 j)]
    simp [integral_deltaPairHit δ hδ0 hδ hne, ZMod.card, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hs, Finset.sum_congr rfl ht]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((A.offDiag.card : ℕ) : ℝ) = (A.card : ℝ) * ((A.card : ℝ) - 1) := by
    rw [Finset.offDiag_card, Nat.cast_sub (by nlinarith : A.card ≤ A.card * A.card), Nat.cast_mul]
    ring
  rw [hcard]
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  field_simp

theorem exists_good_deltaSample (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) (A : Finset ℤ) (m : ℕ) [NeZero m] :
    ∃ ω : Sample, δ * (A.card : ℝ) -
      δ^2 * (A.card : ℝ) * ((A.card : ℝ) - 1) / (2 * (m : ℝ)) ≤ deltaOccupancyScore δ A m ω := by
  obtain ⟨ω, hω⟩ := exists_integral_le (integrable_deltaOccupancyScore δ A m)
  exact ⟨ω, by rwa [integral_deltaOccupancyScore δ hδ0 hδ] at hω⟩

end SidonResearch
