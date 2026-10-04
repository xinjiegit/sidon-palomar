/-
SPDX-License-Identifier: GPL-3.0-only
The full variable-density affine compression theorem.
-/
module

public import GeneralOccupancy
public import RelationExtraction

@[expose] public section

namespace SidonResearch

/-- Variable-density compression, including its degenerate endpoint `δ = 0`.
The map is injective on the retained set and preserves all additive two-sum
relations, including diagonal relations. -/
theorem affine_compression_delta (A : Finset ℤ) (m : ℕ) [NeZero m]
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) :
    ∃ C ⊆ A, ∃ f : ℤ → ZMod m,
      Freiman2On C f ∧ Set.InjOn f C ∧
        δ * (A.card : ℝ) - δ^2 * (A.card : ℝ) * ((A.card : ℝ)-1)/(2*(m : ℝ)) ≤
          (C.card : ℝ) := by
  classical
  obtain ⟨ω, hω⟩ := exists_good_deltaSample δ hδ0 hδ A m
  let R : ℤ → ZMod m → Prop := fun a j => affine a ω ∈ deltaCell δ m j
  have huniq : ∀ a j k, R a j → R a k → j=k := by
    intro a j k hj hk
    by_contra hne
    exact Set.disjoint_left.mp (deltaCells_disjoint hδ hne) hj hk
  obtain ⟨C, f, hCA, hinj, hR, hcard⟩ := exists_relation_representatives A R huniq
  refine ⟨C, hCA, f, ?_, hinj, le_trans hω ?_⟩
  · intro a ha b hb c hc d hd h
    exact deltaCell_labels_freiman hδ (hR a ha) (hR b hb) (hR c hc) (hR d hd)
      (affine_preserves h ω)
  · simpa only [deltaOccupancyScore, deltaHit, deltaPairHit, R, div_eq_mul_inv, mul_comm, one_mul] using hcard

/-- Exact integer rounding of the full compression bound. -/
theorem affine_compression_delta_ceil (A : Finset ℤ) (m : ℕ) [NeZero m]
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) :
    ∃ C ⊆ A, ∃ f : ℤ → ZMod m,
      Freiman2On C f ∧ Set.InjOn f C ∧
        ⌈δ * (A.card : ℝ) - δ^2 * (A.card : ℝ) * ((A.card : ℝ)-1)/(2*(m : ℝ))⌉ ≤
          (C.card : ℤ) := by
  obtain ⟨C, hCA, f, hf, hinj, hcard⟩ := affine_compression_delta A m δ hδ0 hδ
  refine ⟨C, hCA, f, hf, hinj, ?_⟩
  exact Int.ceil_le.mpr (by exact_mod_cast hcard)

end SidonResearch

#print axioms SidonResearch.affine_compression_delta
#print axioms SidonResearch.affine_compression_delta_ceil
