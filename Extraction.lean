module

public import Basic

@[expose] public section

open scoped BigOperators
namespace SidonResearch

variable {α β : Type*}

/-- The real-valued number of ordered collisions between distinct elements. -/
noncomputable def collisionCount [DecidableEq α] [DecidableEq β] (A : Finset α) (f : α → β) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ A, if a ≠ b ∧ f a = f b then 1 else 0

lemma collisionCount_nonneg [DecidableEq α] [DecidableEq β] (A : Finset α) (f : α → β) : 0 ≤ collisionCount A f := by
  classical
  unfold collisionCount
  positivity

lemma collisionCount_insert [DecidableEq α] [DecidableEq β] (A : Finset α) (f : α → β)
    (a : α) (ha : a ∉ A) :
    collisionCount (insert a A) f = collisionCount A f +
      2 * ∑ b ∈ A, (if a ≠ b ∧ f a = f b then (1 : ℝ) else 0) := by
  classical
  simp only [collisionCount, Finset.sum_insert ha]
  have hsym : ∑ x ∈ A, (if x ≠ a ∧ f x = f a then (1 : ℝ) else 0) =
      ∑ x ∈ A, (if a ≠ x ∧ f a = f x then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [ne_comm (a := x), eq_comm (a := f x)]
  simp only [ne_eq, not_true_eq_false, false_and, ite_false, zero_add,
    Finset.sum_add_distrib]
  simp only [ne_eq] at hsym
  rw [hsym]
  ring

/-- At most one deletion is needed for each unordered collision. -/
theorem card_image_lower_bound [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) :
    (A.card : ℝ) - collisionCount A f / 2 ≤ (A.image f).card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [collisionCount]
  | @insert a A ha ih =>
    rw [collisionCount_insert A f a ha, Finset.card_insert_of_notMem ha,
      Finset.image_insert, Nat.cast_add, Nat.cast_one]
    by_cases hf : f a ∈ A.image f
    · rw [Finset.insert_eq_of_mem hf]
      obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hf
      have hne : a ≠ b := by intro h; exact ha (h ▸ hb)
      have hlower : 1 ≤ ∑ b ∈ A, (if a ≠ b ∧ f a = f b then (1 : ℝ) else 0) := by
        have h := Finset.single_le_sum (f := fun b =>
          if a ≠ b ∧ f a = f b then (1 : ℝ) else 0) (by intros; positivity) hb
        simpa [hne, hab] using h
      linarith
    · rw [Finset.card_insert_of_notMem hf, Nat.cast_add, Nat.cast_one]
      have hnonneg : 0 ≤ ∑ b ∈ A, (if a ≠ b ∧ f a = f b then (1 : ℝ) else 0) := by positivity
      linarith

/-- Choosing one representative of every nonempty fiber attains the image size. -/
theorem exists_injective_representatives [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) :
    ∃ C : Finset α, C ⊆ A ∧ Set.InjOn f C ∧ C.image f = A.image f ∧
      (A.card : ℝ) - collisionCount A f / 2 ≤ C.card := by
  classical
  obtain ⟨C, hCA, hinj, himage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (A : Set α) (A.image f) (by simpa using Set.surjOn_image f (A : Set α))
  refine ⟨C, hCA, hinj, himage, ?_⟩
  have hc : C.card = (A.image f).card := by rw [← himage, Finset.card_image_of_injOn hinj]
  rw [hc]
  exact card_image_lower_bound A f

/-- The collision count equals the sum over ordered distinct pairs. -/
lemma collisionCount_eq_offDiag [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) :
    collisionCount A f = ∑ p ∈ A.offDiag,
      (if f p.1 = f p.2 then (1 : ℝ) else 0) := by
  classical
  have hoff : A.offDiag = (A ×ˢ A).filter (fun p => p.1 ≠ p.2) := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hoff, Finset.sum_filter, Finset.sum_product]
  unfold collisionCount
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases h : a = b <;> simp [h]

/-- The collision count is an actual finite cardinality. -/
lemma collisionCount_eq_card [DecidableEq α] [DecidableEq β]
    (A : Finset α) (f : α → β) :
    collisionCount A f = ((A.offDiag.filter (fun p => f p.1 = f p.2)).card : ℝ) := by
  rw [collisionCount_eq_offDiag, Finset.card_filter]
  push_cast
  rfl

end SidonResearch
