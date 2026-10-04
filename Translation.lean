module

public import Basic

@[expose] public section

open scoped BigOperators
namespace SidonResearch
variable {α G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Exact counting identity underlying averaging translated Sidon sets. -/
lemma sum_card_translate_filter (A : Finset α) (f : α → G) (D : Finset G) :
    ∑ t : G, (A.filter fun a => f a - t ∈ D).card = A.card * D.card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner (a : α) : ∑ t : G, (if f a - t ∈ D then 1 else 0) = D.card := by
    calc
      _ = ∑ t : G, (if t ∈ D then 1 else 0) := by
        exact Finset.sum_equiv (Equiv.subLeft (f a)) (by simp) (by simp)
      _ = D.card := by simp
  simp_rw [hinner]
  simp

/-- Averaging is stated without division and hence includes empty sets. -/
theorem exists_large_translate_filter (A : Finset α) (f : α → G) (D : Finset G) :
    ∃ t : G, (A.card : ℝ) * D.card ≤ Fintype.card G *
      ((A.filter fun a => f a - t ∈ D).card : ℝ) := by
  classical
  have hsum := sum_card_translate_filter A f D
  have hsumR : ∑ t : G, ((A.filter fun a => f a - t ∈ D).card : ℝ) =
      (A.card : ℝ) * D.card := by exact_mod_cast hsum
  have hpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have havg : ∑ _t : G, ((A.card : ℝ) * D.card / Fintype.card G) ≤
      ∑ t : G, ((A.filter fun a => f a - t ∈ D).card : ℝ) := by
    rw [hsumR]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    exact le_rfl
  obtain ⟨t, -, ht⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  refine ⟨t, ?_⟩
  simpa [mul_comm] using (div_le_iff₀ hpos).mp ht

/-- A strict Sidon model in a finite abelian group extracts a strict Sidon subset
through an injective forward Freiman map. No inverse Freiman implication is used. -/
theorem extract_sidon [Add α] (A : Finset α) (f : α → G) (D : Finset G)
    (hf : Freiman2On A f) (hinj : Set.InjOn f A) (hD : IsSidon D) :
    ∃ B : Finset α, B ⊆ A ∧ IsSidon B ∧
      (A.card : ℝ) * D.card ≤ Fintype.card G * (B.card : ℝ) := by
  classical
  obtain ⟨t, ht⟩ := exists_large_translate_filter A f D
  let B := A.filter (fun a => f a - t ∈ D)
  have hBA : B ⊆ A := Finset.filter_subset _ _
  refine ⟨B, hBA, ?_, ht⟩
  apply (hD.translate t).pullback (hf.mono hBA) (hinj.mono hBA)
  intro a ha
  refine Finset.mem_image.mpr ⟨f a - t, (Finset.mem_filter.mp ha).2, ?_⟩
  abel

end SidonResearch
