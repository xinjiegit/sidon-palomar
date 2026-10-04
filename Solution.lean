module

public import Main

/-!
# Proved declarations for Comparator

This module does not import `Challenge`. The mathematical definitions are
repeated verbatim, and the theorem statements have the same names and types.
The proof bodies invoke the complete local development in `Main`.
-/

namespace PalomarSidon

@[expose] public section

/-- Strict Sidon property. None of the four summands is required to be distinct. -/
def IsSidon {G : Type*} [Add G] (A : Finset G) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A → ∀ ⦃d⦄, d ∈ A →
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- Preserve existing two-sum equalities; no converse is required. -/
def Freiman2On {G K : Type*} [Add G] [Add K] (A : Finset G) (f : G → K) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ A → ∀ ⦃c⦄, c ∈ A → ∀ ⦃d⦄, d ∈ A →
    a + b = c + d → f a + f b = f c + f d

end

public section

/-- Every sufficiently large integer set contains a strict Sidon subset with
the advertised asymptotic constant. The threshold depends only on epsilon. -/
theorem universal_integer_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧
        (2 / (3 * Real.sqrt 3) - ε) * Real.sqrt A.card ≤ (B.card : ℝ) := by
  simpa only [IsSidon, SidonResearch.IsSidon] using
    SidonResearch.universal_sidon_lower_bound ε hε

/-- For every prime power q, a finite universal bound with both ceilings.
`IsPrimePow q` is Mathlib's usual positive prime-power predicate. -/
theorem finite_prime_power_bound (A : Finset ℤ) (q : ℕ) (hq : IsPrimePow q) :
    ∃ B ⊆ A, IsSidon B ∧
      ⌈(((q : ℝ) + 1) / ((q : ℝ)^2 + q + 1)) *
        (⌈(A.card : ℝ) / 2 - (A.card : ℝ) * ((A.card : ℝ) - 1) /
          (8 * ((q : ℝ)^2 + q + 1))⌉ : ℤ)⌉ ≤ (B.card : ℤ) := by
  simpa only [IsSidon, SidonResearch.IsSidon] using
    SidonResearch.finite_sidon_bound_ceil A q hq

/-- An injective forward Freiman map into a cyclic group, with the full
variable-density bound, including the endpoint delta = 0 and integer rounding. -/
theorem affine_compression (A : Finset ℤ) (m : ℕ) (hm : 0 < m)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    ∃ C ⊆ A, ∃ f : ℤ → ZMod m,
      Freiman2On C f ∧ Set.InjOn f C ∧
        ⌈δ * (A.card : ℝ) - δ^2 * (A.card : ℝ) * ((A.card : ℝ) - 1) /
          (2 * (m : ℝ))⌉ ≤ (C.card : ℤ) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  simpa only [Freiman2On, SidonResearch.Freiman2On] using
    SidonResearch.affine_compression_delta_ceil A m δ hδ0 hδ

/-- A single threshold works in every finite-dimensional real vector space. -/
theorem universal_real_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ d : ℕ, ∀ A : Finset (Fin d → ℝ), N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧
        (2 / (3 * Real.sqrt 3) - ε) * Real.sqrt A.card ≤ (B.card : ℝ) := by
  simpa only [IsSidon, SidonResearch.IsSidon] using
    SidonResearch.universal_sidon_lower_bound_real ε hε

/-- The same constant holds in every torsion-free abelian group. -/
theorem universal_torsion_free_bound
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ A : Finset G, N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧
        (2 / (3 * Real.sqrt 3) - ε) * Real.sqrt A.card ≤ (B.card : ℝ) := by
  simpa only [IsSidon, SidonResearch.IsSidon] using
    SidonResearch.universal_sidon_lower_bound_torsionFree (G := G) ε hε

end

end PalomarSidon

#print axioms PalomarSidon.universal_integer_bound
#print axioms PalomarSidon.finite_prime_power_bound
#print axioms PalomarSidon.affine_compression
#print axioms PalomarSidon.universal_real_bound
#print axioms PalomarSidon.universal_torsion_free_bound
