module

public import Finite
public import Asymptotic
public import Transfer
public import GeneralCompression

@[expose] public section

namespace SidonResearch

/-- The universal strict Sidon lower bound, with no structural hypotheses on A.
This is the epsilon formulation of H(n) ≥ (2/(3√3)+o(1))√n. -/
theorem universal_sidon_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧
        (2/(3*Real.sqrt 3)-ε)*Real.sqrt A.card ≤ (B.card : ℝ) := by
  apply asymptotic_of_finite_bound
  · intro A q hq
    exact finite_sidon_bound A q hq
  · exact hε

/-- The cardinality threshold is uniform over all finite real dimensions. -/
theorem universal_sidon_lower_bound_real (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ d : ℕ, ∀ A : Finset (Fin d → ℝ), N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧
        (2/(3*Real.sqrt 3)-ε)*Real.sqrt A.card ≤ (B.card : ℝ) := by
  obtain ⟨N, hN⟩ := universal_sidon_lower_bound ε hε
  exact ⟨N, fun d => real_space_bound_transfer
    (fun n => (2/(3*Real.sqrt 3)-ε)*Real.sqrt n) N hN d⟩

/-- The same bound holds in every torsion-free abelian ambient group. -/
theorem universal_sidon_lower_bound_torsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ A : Finset G, N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧
        (2/(3*Real.sqrt 3)-ε)*Real.sqrt A.card ≤ (B.card : ℝ) := by
  obtain ⟨N, hN⟩ := universal_sidon_lower_bound ε hε
  exact ⟨N, integer_bound_transfer
    (fun n => (2/(3*Real.sqrt 3)-ε)*Real.sqrt n) N hN⟩

end SidonResearch

#print SidonResearch.universal_sidon_lower_bound
#print axioms SidonResearch.universal_sidon_lower_bound
#print axioms SidonResearch.affine_compression
#print axioms SidonResearch.finite_sidon_bound
#print axioms SidonResearch.finite_sidon_bound_ceil
#print axioms SidonResearch.universal_sidon_lower_bound_real
#print axioms SidonResearch.universal_sidon_lower_bound_torsionFree
#print axioms SidonResearch.affine_compression_delta_ceil
