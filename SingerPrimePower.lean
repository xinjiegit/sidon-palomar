/-
SPDX-License-Identifier: GPL-3.0-only
Prime-power adapter for the complete vendored finite-field Singer proof.
-/
module

public import Basic
public import SingerPrimePowerLibrary

@[expose] public section

namespace SidonResearch

/-- Strict modular Sidon sets remain Sidon and retain cardinality on reduction. -/
private theorem modular_to_cyclic (m : ℕ) (S : Finset ℤ)
    (hS : Erdos30.IsSidonMod m S) :
    ∃ D : Finset (ZMod m), IsSidon D ∧ D.card = S.card := by
  classical
  let f : ℤ → ZMod m := fun a => a
  have hcast {a b c d : ℤ} (h : f a + f b = f c + f d) :
      (m : ℤ) ∣ (a+b)-(c+d) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    exact sub_eq_zero.mpr h
  have hinj : Set.InjOn f (↑S : Set ℤ) := by
    intro a ha b hb heq
    rcases hS ha ha ha hb (hcast (by rw [heq])) with h | h
    · exact h.2
    · exact h.1
  refine ⟨S.image f, ?_, Finset.card_image_of_injOn hinj⟩
  intro a ha b hb c hc d hd heq
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨c', hc', rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨d', hd', rfl⟩ := Finset.mem_image.mp hd
  rcases hS ha' hb' hc' hd' (hcast heq) with h | h
  · exact Or.inl ⟨congrArg f h.1, congrArg f h.2⟩
  · exact Or.inr ⟨congrArg f h.1, congrArg f h.2⟩

/-- Singer's theorem for every positive power of a prime. All field-theoretic
construction steps are proved in `SingerPrimePowerLibrary`; no Singer axiom. -/
theorem exists_singer_primePower (q : ℕ) (hq : IsPrimePow q) :
    ∃ D : Finset (ZMod (q*q+q+1)), IsSidon D ∧ D.card = q+1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  letI : Fact p.Prime := ⟨Nat.prime_iff.mpr hp⟩
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  obtain ⟨S, hS, hcard⟩ :=
    Erdos30.SingerPrimePower.singer_primePower_sidon_set_KL p k
  have hS' : Erdos30.IsSidonMod ((p^k)*(p^k)+p^k+1 : ℕ) S := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one] using hS
  obtain ⟨D, hD, hc⟩ := modular_to_cyclic _ S hS'
  exact ⟨D, hD, hc.trans hcard⟩

end SidonResearch

#print axioms SidonResearch.exists_singer_primePower
