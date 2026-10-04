module

public import Mathlib

@[expose] public section

/-! Strict Sidon sets and forward Freiman 2-homomorphisms.
Repeated summands are included: none of the four variables is assumed distinct. -/
namespace SidonResearch

variable {α β : Type*}

/-- Strict Sidon property: unordered two-element multisets, with repetitions,
are determined by their sum. -/
def IsSidon [Add α] (A : Finset α) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A → ∀ ⦃d⦄, d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- A forward Freiman 2-homomorphism, with no reflection assumption. -/
def Freiman2On [Add α] [Add β] (A : Finset α) (f : α → β) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A → ∀ ⦃d⦄, d ∈ A →
    a + b = c + d → f a + f b = f c + f d

theorem IsSidon.mono [Add α] {A B : Finset α} (hA : IsSidon A) (hBA : B ⊆ A) :
    IsSidon B := by
  intro a ha b hb c hc d hd h
  exact hA (hBA ha) (hBA hb) (hBA hc) (hBA hd) h

theorem Freiman2On.mono [Add α] [Add β] {A B : Finset α} {f : α → β}
    (hf : Freiman2On A f) (hBA : B ⊆ A) : Freiman2On B f := by
  intro a ha b hb c hc d hd h
  exact hf (hBA ha) (hBA hb) (hBA hc) (hBA hd) h

/-- Injectivity plus the forward implication suffices for Sidon pullback. -/
theorem IsSidon.pullback [Add α] [Add β] {A : Finset α} {D : Finset β} {f : α → β}
    (hD : IsSidon D) (hf : Freiman2On A f) (hinj : Set.InjOn f A)
    (hmap : ∀ a ∈ A, f a ∈ D) : IsSidon A := by
  intro a ha b hb c hc d hd h
  rcases hD (hmap a ha) (hmap b hb) (hmap c hc) (hmap d hd)
      (hf ha hb hc hd h) with h | h
  · exact Or.inl ⟨hinj ha hc h.1, hinj hb hd h.2⟩
  · exact Or.inr ⟨hinj ha hd h.1, hinj hb hc h.2⟩

/-- Translation preserves the strict Sidon property in any abelian group. -/
theorem IsSidon.translate [AddCommGroup α] [DecidableEq α] {D : Finset α}
    (hD : IsSidon D) (t : α) : IsSidon (D.image (fun x => t + x)) := by
  intro a ha b hb c hc d hd h
  rcases Finset.mem_image.mp ha with ⟨a', ha', rfl⟩
  rcases Finset.mem_image.mp hb with ⟨b', hb', rfl⟩
  rcases Finset.mem_image.mp hc with ⟨c', hc', rfl⟩
  rcases Finset.mem_image.mp hd with ⟨d', hd', rfl⟩
  have heq : a' + b' = c' + d' := by
    apply add_left_cancel (a := t + t)
    calc
      (t + t) + (a' + b') = (t + a') + (t + b') := by abel
      _ = (t + c') + (t + d') := h
      _ = (t + t) + (c' + d') := by abel
  rcases hD ha' hb' hc' hd' heq with h | h
  · exact Or.inl ⟨by rw [h.1], by rw [h.2]⟩
  · exact Or.inr ⟨by rw [h.1], by rw [h.2]⟩

end SidonResearch
