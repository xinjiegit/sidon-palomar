/-
SPDX-License-Identifier: GPL-3.0-only
Adapter from the completely proved, vendored Singer construction to the generic
strict Sidon predicate of this project. Repeated summands are included.
-/
module

public import Basic
public import SingerLibrary

@[expose] public section

namespace SidonResearch

/-- Singer's finite cyclic Sidon construction, including repeated summands. -/
theorem exists_singer (p : ℕ) (hp : p.Prime) :
    ∃ D : Finset (ZMod (p * p + p + 1)),
      IsSidon D ∧ D.card = p+1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS, hcard⟩ := Erdos30.Singer.singer_sidon_set p hp
  let f : ℤ → ZMod (p*p+p+1) := fun a => a
  have hcast {a b c d : ℤ} (h : f a + f b = f c + f d) :
      (↑p * ↑p + ↑p + 1 : ℤ) ∣ (a+b)-(c+d) := by
    have hz : (((a+b)-(c+d) : ℤ) : ZMod (p*p+p+1)) = 0 := by
      push_cast
      exact sub_eq_zero.mpr h
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hd
  have hinj : Set.InjOn f (↑S : Set ℤ) := by
    intro a ha b hb heq
    have h := hS ha ha ha hb (hcast (by rw [heq]))
    rcases h with h | h
    · exact h.2
    · exact h.1
  refine ⟨S.image f, ?_, ?_⟩
  · intro a ha b hb c hc d hd heq
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
    rcases hS ha' hb' hc' hd' (hcast heq) with h | h
    · exact Or.inl ⟨congrArg f h.1, congrArg f h.2⟩
    · exact Or.inr ⟨congrArg f h.1, congrArg f h.2⟩
  · rw [Finset.card_image_of_injOn hinj]
    exact hcard

end SidonResearch
