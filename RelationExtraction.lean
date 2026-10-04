module

public import Extraction

@[expose] public section

open scoped BigOperators
namespace SidonResearch
variable {α β : Type*} [DecidableEq α] [Fintype β] [Nonempty β] [DecidableEq β]

/-- A cell assignment relation with at most one label at every point permits
fiber deletion with one half of the ordered-pair collision score. -/
theorem exists_relation_representatives (A : Finset α) (R : α → β → Prop)
    [∀ a j, Decidable (R a j)]
    (huniq : ∀ a j k, R a j → R a k → j = k) :
    ∃ C : Finset α, ∃ f : α → β, C ⊆ A ∧ Set.InjOn f C ∧
      (∀ a ∈ C, R a (f a)) ∧
      (∑ a ∈ A, ∑ j, if R a j then (1 : ℝ) else 0) -
        (∑ p ∈ A.offDiag, ∑ j, if R p.1 j ∧ R p.2 j then (1 : ℝ) else 0) / 2
        ≤ (C.card : ℝ) := by
  classical
  let P : α → Prop := fun a => ∃ j, R a j
  let f : α → β := fun a => if h : P a then h.choose else Classical.arbitrary β
  have hf (a : α) (ha : P a) : R a (f a) := by
    dsimp [f]
    rw [dif_pos ha]
    exact ha.choose_spec
  have hrel (a : α) (j : β) : R a j ↔ P a ∧ f a = j := by
    constructor
    · intro h
      have hp : P a := ⟨j, h⟩
      exact ⟨hp, huniq a (f a) j (hf a hp) h⟩
    · rintro ⟨hp, rfl⟩
      exact hf a hp
  let B := A.filter P
  have hBA : B ⊆ A := Finset.filter_subset _ _
  obtain ⟨C, hCB, hinj, -, hbound⟩ := exists_injective_representatives B f
  refine ⟨C, f, hCB.trans hBA, hinj, ?_, ?_⟩
  · intro a ha
    exact hf a (Finset.mem_filter.mp (hCB ha)).2
  have hsingle (a : α) : (∑ j, if R a j then (1 : ℝ) else 0) =
      if P a then 1 else 0 := by
    simp_rw [hrel]
    by_cases hp : P a <;> simp [hp]
  have hpair (a b : α) : (∑ j, if R a j ∧ R b j then (1 : ℝ) else 0) =
      if P a ∧ P b ∧ f a = f b then 1 else 0 := by
    simp_rw [hrel]
    by_cases ha : P a <;> by_cases hb : P b <;>
      simp only [ha, hb, true_and, false_and, and_false, ite_false, Finset.sum_const_zero]
    by_cases h : f a = f b
    · simp [h]
    · have hfalse (j : β) : ¬(f a = j ∧ f b = j) := by
        rintro ⟨ha, hb⟩
        exact h (ha.trans hb.symm)
      simp [h, hfalse]
  have hcard : (∑ a ∈ A, ∑ j, if R a j then (1 : ℝ) else 0) = (B.card : ℝ) := by
    simp_rw [hsingle]
    dsimp [B]
    rw [Finset.card_filter]
    push_cast
    rfl
  have hpairs : (∑ p ∈ A.offDiag, ∑ j,
      if R p.1 j ∧ R p.2 j then (1 : ℝ) else 0) = collisionCount B f := by
    simp_rw [hpair]
    have hoff : B.offDiag = A.offDiag.filter (fun p => P p.1 ∧ P p.2) := by
      ext p
      simp only [Finset.mem_offDiag, Finset.mem_filter, B]
      tauto
    rw [collisionCount_eq_offDiag, hoff, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases ha : P p.1 <;> by_cases hb : P p.2 <;> simp [ha, hb]
  rw [hcard, hpairs]
  exact hbound

end SidonResearch
