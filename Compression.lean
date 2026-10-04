module

public import Occupancy
public import RelationExtraction

@[expose] public section

namespace SidonResearch

/-- Exact half-density affine compression. The map preserves all existing
two-sum equalities and is separately proved injective on its chosen domain. -/
theorem affine_compression (A : Finset ℤ) (m : ℕ) [NeZero m] :
    ∃ C ⊆ A, ∃ f : ℤ → ZMod m,
      Freiman2On C f ∧ Set.InjOn f C ∧
        (A.card : ℝ)/2 - (A.card : ℝ)*((A.card : ℝ)-1)/(8*(m : ℝ)) ≤
          (C.card : ℝ) := by
  classical
  obtain ⟨ω, hω⟩ := exists_good_sample A m
  let R : ℤ → ZMod m → Prop := fun a j => affine a ω ∈ cell m j
  have huniq : ∀ a j k, R a j → R a k → j=k := by
    intro a j k hj hk
    by_contra hne
    exact Set.disjoint_left.mp (cells_disjoint hne) hj hk
  obtain ⟨C, f, hCA, hinj, hR, hcard⟩ := exists_relation_representatives A R huniq
  refine ⟨C, hCA, f, ?_, hinj, le_trans hω ?_⟩
  · intro a ha b hb c hc d hd h
    exact cell_labels_freiman (hR a ha) (hR b hb) (hR c hc) (hR d hd)
      (affine_preserves h ω)
  · simpa only [occupancyScore, hit, pairHit, R, div_eq_mul_inv, one_mul, mul_comm] using hcard

/-- Integer rounding is exact and costs no additional element. -/
theorem affine_compression_ceil (A : Finset ℤ) (m : ℕ) [NeZero m] :
    ∃ C ⊆ A, ∃ f : ℤ → ZMod m,
      Freiman2On C f ∧ Set.InjOn f C ∧
        ⌈(A.card : ℝ)/2 - (A.card : ℝ)*((A.card : ℝ)-1)/(8*(m : ℝ))⌉ ≤
          (C.card : ℤ) := by
  obtain ⟨C, hCA, f, hf, hinj, hcard⟩ := affine_compression A m
  refine ⟨C, hCA, f, hf, hinj, ?_⟩
  exact Int.ceil_le.mpr (by exact_mod_cast hcard)

end SidonResearch
