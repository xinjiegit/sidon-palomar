module

public import Mathlib

/-!
# A universal strict Sidon subset bound

This independent statement surface imports only Mathlib. Its deliberate `sorry`
holes are replaced by proofs in `Solution.lean`, which Comparator checks against
these declarations and the exact definitions below.

The principal result is the epsilon formulation of
`H(n) ≥ (2 / (3 * sqrt 3) + o(1)) * sqrt n`, uniformly over arbitrary integer
sets, independently of their diameter. Strict Sidon means unordered pairs with
repetition, so three-term arithmetic progressions are forbidden as well.

The finite prime-power bound retains both integer ceilings. The compression
theorem gives an injective forward Freiman 2-homomorphism for every positive
modulus and every density in `[0, 1/2]`; it does not assert reflection of sums.
The real-space threshold is uniform in the dimension. The final theorem also
transfers the integer bound to every torsion-free abelian group.
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
  sorry

/-- For every prime power q, a finite universal bound with both ceilings.
`IsPrimePow q` is Mathlib's usual positive prime-power predicate. -/
theorem finite_prime_power_bound (A : Finset ℤ) (q : ℕ) (hq : IsPrimePow q) :
    ∃ B ⊆ A, IsSidon B ∧
      ⌈(((q : ℝ) + 1) / ((q : ℝ)^2 + q + 1)) *
        (⌈(A.card : ℝ) / 2 - (A.card : ℝ) * ((A.card : ℝ) - 1) /
          (8 * ((q : ℝ)^2 + q + 1))⌉ : ℤ)⌉ ≤ (B.card : ℤ) := by
  sorry

/-- An injective forward Freiman map into a cyclic group, with the full
variable-density bound, including the endpoint delta = 0 and integer rounding. -/
theorem affine_compression (A : Finset ℤ) (m : ℕ) (hm : 0 < m)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    ∃ C ⊆ A, ∃ f : ℤ → ZMod m,
      Freiman2On C f ∧ Set.InjOn f C ∧
        ⌈δ * (A.card : ℝ) - δ^2 * (A.card : ℝ) * ((A.card : ℝ) - 1) /
          (2 * (m : ℝ))⌉ ≤ (C.card : ℤ) := by
  sorry

/-- A single threshold works in every finite-dimensional real vector space. -/
theorem universal_real_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ d : ℕ, ∀ A : Finset (Fin d → ℝ), N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧
        (2 / (3 * Real.sqrt 3) - ε) * Real.sqrt A.card ≤ (B.card : ℝ) := by
  sorry

/-- The same constant holds in every torsion-free abelian group. -/
theorem universal_torsion_free_bound
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ A : Finset G, N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧
        (2 / (3 * Real.sqrt 3) - ε) * Real.sqrt A.card ≤ (B.card : ℝ) := by
  sorry

end

end PalomarSidon
