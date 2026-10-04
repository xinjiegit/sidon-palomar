module

public import Compression
public import SingerPrimePower
public import Translation

@[expose] public section

namespace SidonResearch

/-- Fully rounded finite bound, keeping both ceilings in the research report. -/
theorem finite_sidon_bound_ceil (A : Finset ℤ) (q : ℕ) (hq : IsPrimePow q) :
    ∃ B ⊆ A, IsSidon B ∧
      ⌈(((q : ℝ)+1)/((q : ℝ)^2+q+1)) *
        (⌈(A.card : ℝ)/2 - (A.card : ℝ)*((A.card : ℝ)-1)/
          (8*((q : ℝ)^2+q+1))⌉ : ℤ)⌉ ≤ (B.card : ℤ) := by
  let m := q*q+q+1
  have hm0 : 0 < m := by dsimp [m]; omega
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  obtain ⟨C, hCA, f, hf, hinj, hC⟩ := affine_compression_ceil A m
  obtain ⟨D, hD, hDcard⟩ := exists_singer_primePower q hq
  obtain ⟨B, hBC, hB, hcard⟩ := extract_sidon C f D hf hinj hD
  refine ⟨B, hBC.trans hCA, hB, Int.ceil_le.mpr ?_⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmcast : (m : ℝ) = (q : ℝ)^2+q+1 := by simp [m, pow_two]
  have hC' : (⌈(A.card : ℝ)/2 - (A.card : ℝ)*((A.card : ℝ)-1)/
      (8*(m : ℝ))⌉ : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hC
  have hmul := mul_le_mul_of_nonneg_left hC'
    (show 0 ≤ ((q : ℝ)+1)/(m : ℝ) by positivity)
  rw [hDcard, ZMod.card] at hcard
  have hB' : (((q : ℝ)+1)/(m : ℝ)) * (C.card : ℝ) ≤ (B.card : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmR).mpr
    simpa [mul_comm, Nat.cast_add, Nat.cast_one] using hcard
  simpa only [hmcast, Int.cast_natCast] using le_trans hmul hB'

/-- The finite bound for every prime-power Singer parameter. -/
theorem finite_sidon_bound_primePower (A : Finset ℤ) (q : ℕ) (hq : IsPrimePow q) :
    ∃ B ⊆ A, IsSidon B ∧
      (((q : ℝ)+1)/((q : ℝ)^2+q+1)) *
        ((A.card : ℝ)/2 - (A.card : ℝ)*((A.card : ℝ)-1)/
          (8*((q : ℝ)^2+q+1))) ≤ (B.card : ℝ) := by
  let m := q*q+q+1
  have hm0 : 0 < m := by dsimp [m]; omega
  letI : NeZero m := ⟨Nat.ne_of_gt hm0⟩
  obtain ⟨C, hCA, f, hf, hinj, hC⟩ := affine_compression A m
  obtain ⟨D, hD, hDcard⟩ := exists_singer_primePower q hq
  obtain ⟨B, hBC, hB, hcard⟩ := extract_sidon C f D hf hinj hD
  refine ⟨B, hBC.trans hCA, hB, ?_⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmcast : (m : ℝ) = (q : ℝ)^2+q+1 := by simp [m, pow_two]
  rw [hDcard, ZMod.card] at hcard
  have hmul := mul_le_mul_of_nonneg_left hC
    (show 0 ≤ ((q : ℝ)+1)/(m : ℝ) by positivity)
  have hB' : (((q : ℝ)+1)/(m : ℝ)) * (C.card : ℝ) ≤ (B.card : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hmR).mpr
    simpa [mul_comm, Nat.cast_add, Nat.cast_one] using hcard
  simpa only [hmcast] using le_trans hmul hB'

/-- Prime specialization used to choose asymptotically optimal moduli. -/
theorem finite_sidon_bound (A : Finset ℤ) (q : ℕ) (hq : q.Prime) :
    ∃ B ⊆ A, IsSidon B ∧
      (((q : ℝ)+1)/((q : ℝ)^2+q+1)) *
        ((A.card : ℝ)/2 - (A.card : ℝ)*((A.card : ℝ)-1)/
          (8*((q : ℝ)^2+q+1))) ≤ (B.card : ℝ) :=
  finite_sidon_bound_primePower A q hq.isPrimePow

end SidonResearch
