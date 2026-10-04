/-
SPDX-License-Identifier: GPL-3.0-only
Derived from d0d1/singer-theorem-lean, commit
0c890589afc58e8955a5d7c3a609daff6447da31 (2026-05-12).
Authors: David B. Hulak, Arthur F. Ramos, Ruy J. G. B. de Queiroz.
Source: https://github.com/d0d1/singer-theorem-lean
Changes: consolidate six prime-power core modules, remove unused interval
and asymptotic imports/wrappers, and port to Lean 4.31. Full source proof.
-/
module

public import SingerLibrary

@[expose] public section

-- BEGIN upstream SingerPrimePowerCore.lean
/-
Prime-power Singer finite-field core for the public Singer/Sidon Lean artifact.

This file is exported from the Erdős 30 research repository at d0d1/erdos
from `work/erdos-30/formal/Erdos30/SingerPrimePowerCore.lean` at commit
`ca225a0bb39ce131d31d8a949133b3c17f60acfa`.

Public-export edit: the top comment was neutralized for this artifact.
-/


namespace Erdos30.SingerPrimePower

open Module FiniteField

variable (p : ℕ) [Fact p.Prime] (k : ℕ) [NeZero k]

/-- The base finite field of the prime-power Singer construction.
For `k = 1` this is (non-canonically isomorphic to) `ZMod p`; for
general `k` it is the field of `p^k` elements. -/
abbrev K : Type := GaloisField p k

/-- The degree-3 extension supplying the Singer construction. Its
cardinality is `(p^k)^3 = q^3` where `q = p^k`. Uses Mathlib's
`FiniteField.Extension` to obtain the algebra instance over `K`. -/
abbrev L : Type := FiniteField.Extension (K p k) p 3

/-- Cardinality of the base field. -/
theorem card_K : Nat.card (K p k) = p ^ k :=
  GaloisField.card p k (NeZero.ne k)

/-- Cardinality of the degree-3 extension. -/
theorem card_L : Nat.card (L p k) = (p ^ k) ^ 3 := by
  rw [show (L p k) = FiniteField.Extension (K p k) p 3 from rfl,
      FiniteField.natCard_extension, card_K]

set_option linter.unusedSectionVars false in
/-- The extension `L` has degree 3 over the base `K`. -/
theorem finrank_KL : Module.finrank (K p k) (L p k) = 3 :=
  FiniteField.finrank_extension (K p k) p 3

set_option linter.unusedSectionVars false in
/-- The trace `Algebra.trace K L` is surjective. -/
theorem trace_surjective_KL :
    Function.Surjective (Algebra.trace (K p k) (L p k)) :=
  Algebra.trace_surjective (K p k) (L p k)

/-- The trace-kernel has `K`-dimension 2 (rank-nullity over a
degree-3 extension). Mirrors `Erdos30/Singer.lean:39-49`. -/
theorem finrank_ker_trace_KL :
    Module.finrank (K p k) (Algebra.trace (K p k) (L p k)).ker = 2 := by
  have h_rn := LinearMap.finrank_range_add_finrank_ker
    (Algebra.trace (K p k) (L p k))
  rw [finrank_KL] at h_rn
  have htop : (Algebra.trace (K p k) (L p k)).range = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ (trace_surjective_KL p k)
  rw [show finrank (K p k) ↥(Algebra.trace (K p k) (L p k)).range =
      finrank (K p k) (K p k) from by rw [htop]; exact finrank_top (K p k) (K p k),
    finrank_self] at h_rn
  omega

end Erdos30.SingerPrimePower
-- END upstream SingerPrimePowerCore.lean

-- BEGIN upstream SingerPrimePowerAlgebra.lean
/-
Prime-power Singer finite-field core for the public Singer/Sidon Lean artifact.

This file is exported from the Erdős 30 research repository at d0d1/erdos
from `work/erdos-30/formal/Erdos30/SingerPrimePowerAlgebra.lean` at commit
`ca225a0bb39ce131d31d8a949133b3c17f60acfa`.

Public-export edit: the top comment was neutralized for this artifact.
-/


set_option maxHeartbeats 800000

namespace Erdos30.SingerPrimePower

open Module Submodule Finset Polynomial FiniteDimensional

variable (p : ℕ) [Fact p.Prime] (k : ℕ) [NeZero k]

/-- Minimal polynomial of α ∉ K in `L` has degree 3 over `K`.
Mirrors `Erdos30/Singer.lean:53-66`. -/
theorem minpoly_degree_eq_three_KL (α : L p k)
    (hα : α ∉ Set.range (algebraMap (K p k) (L p k))) :
    (minpoly (K p k) α).natDegree = 3 := by
  have hint : IsIntegral (K p k) α := Algebra.IsIntegral.isIntegral α
  have hdvd : (minpoly (K p k) α).natDegree ∣ 3 := by
    have h := minpoly.degree_dvd hint
    rwa [finrank_KL p k] at h
  have hne1 : (minpoly (K p k) α).natDegree ≠ 1 := by
    intro h1
    exact hα (IntermediateField.mem_bot.mp (by
      rw [← IntermediateField.finrank_eq_one_iff.mp
        (by rw [IntermediateField.adjoin.finrank hint]; exact h1)]
      exact IntermediateField.subset_adjoin (K p k) {α} (Set.mem_singleton α)))
  exact (Nat.Prime.eq_one_or_self_of_dvd (by decide) _ hdvd).resolve_left hne1

/-- {α⁰·v, α¹·v, α²·v} are K-linearly independent when α ∉ K and v ≠ 0.
Mirrors `Erdos30/Singer.lean:68-92`. -/
theorem linIndep_smul_v_KL (α v : L p k)
    (hα : α ∉ Set.range (algebraMap (K p k) (L p k)))
    (hv : v ≠ 0) :
    LinearIndependent (K p k) (fun i : Fin 3 => α ^ (i : ℕ) * v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hfactor : (∑ i : Fin 3, g i • α ^ (i : ℕ)) * v = 0 := by
    have heq : ∑ i : Fin 3, g i • (α ^ (i : ℕ) * v) =
               (∑ i : Fin 3, g i • α ^ (i : ℕ)) * v := by
      simp [Finset.sum_mul, Algebra.smul_mul_assoc]
    rw [← heq]; exact hg
  have hsum : ∑ i : Fin 3, g i • α ^ (i : ℕ) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hv
  have hdeg := minpoly_degree_eq_three_KL p k α hα
  have hli := @linearIndependent_pow _ _ (K p k) _ _ α
  rw [Fintype.linearIndependent_iff] at hli
  intro i
  have hsum_t : ∑ j : Fin (minpoly (K p k) α).natDegree,
      (g ∘ Fin.cast hdeg) j • α ^ (j : ℕ) = 0 := by
    convert hsum using 1
    exact Fintype.sum_equiv (Fin.castOrderIso hdeg).toEquiv _ _
      (fun j => by simp [Function.comp, Fin.castOrderIso, Fin.cast])
  have h := hli _ hsum_t (Fin.cast hdeg.symm i)
  simp [Function.comp, Fin.cast] at h; exact h

/-- Multiplication by α ∉ K has no proper invariant subspace in `L/K`.
Mirrors `Erdos30/Singer.lean:97-121`. -/
theorem no_proper_invariant_subspace_KL (α : L p k)
    (hα : α ∉ Set.range (algebraMap (K p k) (L p k)))
    (V : Submodule (K p k) (L p k)) (hVbot : V ≠ ⊥) (hVtop : V ≠ ⊤)
    (hinv : ∀ v : L p k, v ∈ V → α • v ∈ V) : False := by
  have hinv_pow : ∀ (n : ℕ) (v : L p k), v ∈ V → α ^ n • v ∈ V := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih => intro v hv; have h := ih _ (hinv v hv); rwa [← mul_smul, ← pow_succ] at h
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVbot
  have hVlt : finrank (K p k) V < 3 := by
    have := finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hVtop)
    rw [finrank_top, finrank_KL p k] at this; exact this
  have hmem : ∀ i : Fin 3, α ^ (i : ℕ) * v ∈ V := fun i => by
    have h := hinv_pow i v hv_mem
    rwa [Algebra.smul_def] at h
  have hli : LinearIndependent (K p k) (fun i : Fin 3 => α ^ (i : ℕ) * v) :=
    linIndep_smul_v_KL p k α v hα hv_ne
  have hli_V : LinearIndependent (K p k) (fun i : Fin 3 =>
      (⟨α ^ (i : ℕ) * v, hmem i⟩ : V)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.linearIndependent_iff] at hli
    apply hli g
    have := congr_arg Subtype.val hg
    simpa using this
  exact absurd hVlt (not_lt.mpr
    (le_of_eq (Fintype.card_fin 3).symm |>.trans hli_V.fintype_card_le_finrank))

/-- Two distinct 2-dim subspaces of `L/K` intersect in dimension 1.
Mirrors `Erdos30/Singer.lean:126-138`. -/
theorem finrank_inf_of_distinct_twodim_KL
    (V W : Submodule (K p k) (L p k))
    (hV : finrank (K p k) V = 2) (hW : finrank (K p k) W = 2) (hne : V ≠ W) :
    finrank (K p k) ↥(V ⊓ W) = 1 := by
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h_sup_le : finrank (K p k) ↥(V ⊔ W) ≤ 3 := by
    have := Submodule.finrank_le (V ⊔ W)
    rw [finrank_KL p k] at this; exact this
  have hV_lt_sup : V < V ⊔ W := lt_of_le_of_ne le_sup_left (fun heq =>
    hne (eq_of_le_of_finrank_le (heq ▸ le_sup_right) (by omega)).symm)
  have h_sup_gt : 2 < finrank (K p k) ↥(V ⊔ W) := by
    have := finrank_lt_finrank_of_lt hV_lt_sup
    rw [hV] at this; exact this
  rw [hV, hW] at hgrass
  omega

end Erdos30.SingerPrimePower
-- END upstream SingerPrimePowerAlgebra.lean

-- BEGIN upstream SingerPrimePowerBridge.lean
/-
Prime-power Singer finite-field core for the public Singer/Sidon Lean artifact.

This file is exported from the Erdős 30 research repository at d0d1/erdos
from `work/erdos-30/formal/Erdos30/SingerPrimePowerBridge.lean` at commit
`ca225a0bb39ce131d31d8a949133b3c17f60acfa`.

Public-export edit: the top comment was neutralized for this artifact.
-/


set_option maxHeartbeats 800000

namespace Erdos30.SingerPrimePower

open Module Submodule Erdos30

variable (p : ℕ) [Fact p.Prime] (k : ℕ) [NeZero k]

/-- Multiplication by a nonzero element of `L` is a `K`-linear
automorphism. Mirrors `SingerBridge.lean:29-38`. -/
noncomputable def mulLinearEquiv_KL (α : L p k) (hα : α ≠ 0) :
    L p k ≃ₗ[K p k] L p k where
  toFun := fun x => α * x
  map_add' := mul_add α
  map_smul' := fun r x => by simp [Algebra.smul_def, mul_left_comm]
  invFun := fun x => α⁻¹ * x
  left_inv := fun x => by
    show α⁻¹ * (α * x) = x
    rw [← mul_assoc, inv_mul_cancel₀ hα, one_mul]
  right_inv := fun x => by
    show α * (α⁻¹ * x) = x
    rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul]

/-- The scaled submodule `αV := {αv : v ∈ V}` as a `K`-submodule
of `L`. Mirrors `SingerBridge.lean:41-44`. -/
noncomputable def scaledSubmodule_KL (α : L p k) (hα : α ≠ 0)
    (V : Submodule (K p k) (L p k)) :
    Submodule (K p k) (L p k) :=
  V.map (mulLinearEquiv_KL p k α hα).toLinearMap

set_option linter.unusedSectionVars false in
lemma mem_scaledSubmodule_KL_iff (α : L p k) (hα : α ≠ 0)
    (V : Submodule (K p k) (L p k)) (x : L p k) :
    x ∈ scaledSubmodule_KL p k α hα V ↔ ∃ v ∈ V, α * v = x := by
  simp [scaledSubmodule_KL, Submodule.mem_map, mulLinearEquiv_KL]

set_option linter.unusedSectionVars false in
lemma finrank_scaledSubmodule_KL (α : L p k) (hα : α ≠ 0)
    (V : Submodule (K p k) (L p k)) :
    finrank (K p k) (scaledSubmodule_KL p k α hα V) = finrank (K p k) V :=
  LinearEquiv.finrank_eq
    ((mulLinearEquiv_KL p k α hα).submoduleMap V |>.symm)

private lemma ker_trace_ne_bot_KL :
    (Algebra.trace (K p k) (L p k)).ker ≠ ⊥ := fun h => by
  have := finrank_ker_trace_KL p k
  rw [h, finrank_bot (R := K p k) (M := L p k)] at this
  omega

private lemma ker_trace_ne_top_KL :
    (Algebra.trace (K p k) (L p k)).ker ≠ ⊤ := fun h => by
  have h2 := finrank_ker_trace_KL p k
  have h3 := finrank_KL p k
  rw [h, finrank_top, h3] at h2
  omega

/-- The scaled trace kernel `αV ≠ V` when α ∉ K.
Mirrors `SingerBridge.lean:72-84`. -/
lemma scaledSubmodule_ne_ker_trace_KL (α : L p k) (hα_ne : α ≠ 0)
    (hα : α ∉ Set.range (algebraMap (K p k) (L p k))) :
    scaledSubmodule_KL p k α hα_ne (Algebra.trace (K p k) (L p k)).ker ≠
    (Algebra.trace (K p k) (L p k)).ker := by
  set V := (Algebra.trace (K p k) (L p k)).ker
  intro heq
  have hinv : ∀ v : L p k, v ∈ V → α • v ∈ V := by
    intro v hv
    have hmem : α * v ∈ scaledSubmodule_KL p k α hα_ne V :=
      (mem_scaledSubmodule_KL_iff p k α hα_ne V (α * v)).mpr ⟨v, hv, rfl⟩
    rw [heq] at hmem
    rwa [Algebra.smul_def]
  exact no_proper_invariant_subspace_KL p k α hα V
    (ker_trace_ne_bot_KL p k) (ker_trace_ne_top_KL p k) hinv

set_option linter.unusedSectionVars false in
/-- α⁻¹ ∉ K when α ∉ K. Mirrors `SingerBridge.lean:87-92`. -/
lemma inv_not_in_range_KL (α : L p k) (_hα_ne : α ≠ 0)
    (hα : α ∉ Set.range (algebraMap (K p k) (L p k))) :
    α⁻¹ ∉ Set.range (algebraMap (K p k) (L p k)) := by
  intro ⟨a, ha⟩
  apply hα
  exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_inv]⟩

/-- **Key geometric fact.** When α ∉ K, V ⊓ α⁻¹V has dimension 1.
Mirrors `SingerBridge.lean:98-111`. -/
theorem finrank_inf_scaled_ker_trace_KL (α : L p k) (hα_ne : α ≠ 0)
    (hα : α ∉ Set.range (algebraMap (K p k) (L p k))) :
    finrank (K p k) ↥((Algebra.trace (K p k) (L p k)).ker ⊓
      scaledSubmodule_KL p k α⁻¹ (inv_ne_zero hα_ne)
        (Algebra.trace (K p k) (L p k)).ker) = 1 := by
  set V := (Algebra.trace (K p k) (L p k)).ker
  have hV2 : finrank (K p k) V = 2 := finrank_ker_trace_KL p k
  have hαinv_ne := inv_ne_zero hα_ne
  have hαinv_not_base := inv_not_in_range_KL p k α hα_ne hα
  have hW2 : finrank (K p k) (scaledSubmodule_KL p k α⁻¹ hαinv_ne V) = 2 := by
    rw [finrank_scaledSubmodule_KL, hV2]
  have hne : V ≠ scaledSubmodule_KL p k α⁻¹ hαinv_ne V :=
    fun h => scaledSubmodule_ne_ker_trace_KL p k α⁻¹ hαinv_ne hαinv_not_base h.symm
  exact finrank_inf_of_distinct_twodim_KL p k V _ hV2 hW2 hne

end Erdos30.SingerPrimePower
-- END upstream SingerPrimePowerBridge.lean

-- BEGIN upstream SingerPrimePowerUnits.lean
/-
Prime-power Singer finite-field core for the public Singer/Sidon Lean artifact.

This file is exported from the Erdős 30 research repository at d0d1/erdos
from `work/erdos-30/formal/Erdos30/SingerPrimePowerUnits.lean` at commit
`ca225a0bb39ce131d31d8a949133b3c17f60acfa`.

Public-export edit: the top comment was neutralized for this artifact.
-/


set_option maxHeartbeats 800000

namespace Erdos30.SingerPrimePower

open Module Submodule Erdos30 Finset

variable (p : ℕ) [Fact p.Prime] (k : ℕ) [NeZero k]

noncomputable instance : Fintype (K p k) := Fintype.ofFinite _
noncomputable instance : Fintype (L p k) := Fintype.ofFinite _
noncomputable instance : Fintype (K p k)ˣ := Fintype.ofFinite _
noncomputable instance : Fintype (L p k)ˣ := Fintype.ofFinite _

/-- `K× ↪ L×` via `algebraMap`. Mirrors `SingerBridge.lean:116-117`. -/
noncomputable def baseUnitsSubgroup_KL : Subgroup (L p k)ˣ :=
  (Units.map (algebraMap (K p k) (L p k)).toMonoidHom).range

instance : (baseUnitsSubgroup_KL p k).Normal := inferInstance

set_option linter.unusedSectionVars false in
private lemma units_map_injective_KL :
    Function.Injective
      (Units.map (algebraMap (K p k) (L p k)).toMonoidHom) := by
  apply Units.map_injective
  exact (algebraMap (K p k) (L p k)).injective

/-- The base units subgroup has cardinality `q - 1` where `q = p^k`. -/
lemma baseUnitsSubgroup_card_KL :
    Nat.card (baseUnitsSubgroup_KL p k) = p ^ k - 1 := by
  refine (Nat.card_congr
    ((Units.map (algebraMap (K p k) (L p k)).toMonoidHom).ofInjective
      (units_map_injective_KL p k)).toEquiv.symm).trans ?_
  rw [Nat.card_units, card_K]

/-- `L×` has cardinality `q³ - 1` where `q = p^k`. -/
lemma L_units_card_KL :
    Nat.card (L p k)ˣ = (p ^ k) ^ 3 - 1 := by
  rw [Nat.card_units, card_L]

/-- **The Singer index.** `[L× : K×] = q² + q + 1` where `q = p^k`. -/
lemma baseUnitsSubgroup_index_KL :
    (baseUnitsSubgroup_KL p k).index = (p ^ k) ^ 2 + p ^ k + 1 := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := hp_prime.pos
  have hp_one_lt : 1 < p := hp_prime.one_lt
  have hpk_pos : 0 < p ^ k := pow_pos hp_pos k
  have hk_pos : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  have hpk_ge_two : 2 ≤ p ^ k := by
    calc 2 ≤ p := hp_one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right (le_of_lt hp_one_lt) hk_pos
  have hpk_sub_pos : 0 < p ^ k - 1 := Nat.sub_pos_of_lt hpk_ge_two
  have hmul := Subgroup.card_mul_index (baseUnitsSubgroup_KL p k)
  rw [baseUnitsSubgroup_card_KL, L_units_card_KL] at hmul
  have hfact : (p ^ k) ^ 3 - 1 =
      (p ^ k - 1) * ((p ^ k) ^ 2 + p ^ k + 1) := by
    zify [hpk_pos, Nat.one_le_pow 3 (p ^ k) hpk_pos]
    ring
  rw [hfact] at hmul
  exact Nat.eq_of_mul_eq_mul_left hpk_sub_pos hmul

set_option linter.unusedSectionVars false in
/-- Membership characterisation: `u ∈ baseUnitsSubgroup_KL` iff
`↑u ∈ range(algebraMap K L)`. Mirrors `SingerBridge.lean:147-156`. -/
lemma mem_baseUnitsSubgroup_KL_iff (u : (L p k)ˣ) :
    u ∈ baseUnitsSubgroup_KL p k ↔
    (↑u : L p k) ∈ Set.range (algebraMap (K p k) (L p k)) := by
  simp only [baseUnitsSubgroup_KL, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v.val, by simp [Units.coe_map]⟩
  · rintro ⟨a, ha⟩
    have ha_ne : a ≠ 0 := by
      intro h
      simp [h] at ha
      exact Units.ne_zero u ha.symm
    exact ⟨Units.mk0 a ha_ne, Units.ext (by simp [Units.coe_map, ha])⟩

end Erdos30.SingerPrimePower
-- END upstream SingerPrimePowerUnits.lean

-- BEGIN upstream SingerPrimePowerSidon.lean
/-
Prime-power Singer finite-field core for the public Singer/Sidon Lean artifact.

This file is exported from the Erdős 30 research repository at d0d1/erdos
from `work/erdos-30/formal/Erdos30/SingerPrimePowerSidon.lean` at commit
`ca225a0bb39ce131d31d8a949133b3c17f60acfa`.

Public-export edit: the top comment was neutralized for this artifact.
-/


set_option maxHeartbeats 32000000

namespace Erdos30.SingerPrimePower

open Module Submodule Erdos30

variable (p : ℕ) [Fact p.Prime] (k : ℕ) [NeZero k]

/-- Map a nonzero element of `L` to its class in the Singer
quotient group `L× / baseUnitsSubgroup_KL`. Mirrors
`SingerSidon.lean:32-34`. -/
noncomputable def singerMk_KL (x : L p k) (hx : x ≠ 0) :
    (L p k)ˣ ⧸ baseUnitsSubgroup_KL p k :=
  QuotientGroup.mk (Units.mk0 x hx)

lemma singerMk_KL_eq_iff (a b : L p k) (ha : a ≠ 0) (hb : b ≠ 0) :
    singerMk_KL p k a ha = singerMk_KL p k b hb ↔
    a⁻¹ * b ∈ Set.range (algebraMap (K p k) (L p k)) := by
  unfold singerMk_KL
  rw [QuotientGroup.eq, mem_baseUnitsSubgroup_KL_iff]
  simp [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_mk0]

set_option linter.unusedSectionVars false in
private lemma proportional_of_finrank_one_KL
    (W : Submodule (K p k) (L p k))
    (hW : finrank (K p k) W = 1)
    (w₁ w₂ : L p k) (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W)
    (hw₁_ne : w₁ ≠ 0) (hw₂_ne : w₂ ≠ 0) :
    ∃ c : K p k, c ≠ 0 ∧ w₂ = c • w₁ := by
  have hsub : span (K p k) {w₁} ≤ W :=
    span_le.mpr (Set.singleton_subset_iff.mpr hw₁)
  have heq' : W = span (K p k) ({w₁} : Set (L p k)) :=
    (eq_of_le_of_finrank_le hsub
      (by rw [finrank_span_singleton hw₁_ne]; omega)).symm
  have hmem : w₂ ∈ span (K p k) ({w₁} : Set (L p k)) := heq' ▸ hw₂
  rw [mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, fun h => hw₂_ne (by simp [h] at hc; exact hc.symm), hc.symm⟩

/-- **Prime-power Singer Sidon property in the quotient group.**
If `u * v = α * (w * x)` with `u, v, w, x` nonzero elements of
`ker(Tr K L)` and `α ∈ K×`, then in the quotient
`L× / baseUnitsSubgroup_KL` either `[u] = [w] ∧ [v] = [x]`, or
`[u] = [x] ∧ [v] = [w]`. Mirrors `SingerSidon.lean:57-127`. -/
theorem singer_quotient_sidon_KL
    (u v w x : L p k)
    (hu : u ∈ (Algebra.trace (K p k) (L p k)).ker)
    (hv : v ∈ (Algebra.trace (K p k) (L p k)).ker)
    (hw : w ∈ (Algebra.trace (K p k) (L p k)).ker)
    (hx : x ∈ (Algebra.trace (K p k) (L p k)).ker)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hx0 : x ≠ 0)
    (α : K p k) (hα : α ≠ 0)
    (hmul : u * v = (algebraMap (K p k) (L p k) α) * (w * x)) :
    (singerMk_KL p k u hu0 = singerMk_KL p k w hw0 ∧
      singerMk_KL p k v hv0 = singerMk_KL p k x hx0) ∨
    (singerMk_KL p k u hu0 = singerMk_KL p k x hx0 ∧
      singerMk_KL p k v hv0 = singerMk_KL p k w hw0) := by
  set V := (Algebra.trace (K p k) (L p k)).ker
  have hαF_ne : (algebraMap (K p k) (L p k) α) ≠ 0 := by simp [hα]
  have hβ_ne : u * w⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hw0)
  have h_key : (u * w⁻¹) * v = (algebraMap (K p k) (L p k) α) * x := by
    have h := hmul; field_simp at h ⊢; linear_combination h
  by_cases hβ_base : (u * w⁻¹) ∈ Set.range (algebraMap (K p k) (L p k))
  case pos =>
    left; constructor
    · rw [singerMk_KL_eq_iff]
      obtain ⟨c, hc⟩ := hβ_base
      refine ⟨c⁻¹, ?_⟩
      simp only [map_inv₀]; rw [hc]; field_simp
    · rw [singerMk_KL_eq_iff]
      obtain ⟨c, hc⟩ := hβ_base
      have hcF_ne : (algebraMap (K p k) (L p k) c) ≠ 0 :=
        fun heq => hβ_ne (by rw [← hc, heq])
      refine ⟨α⁻¹ * c, ?_⟩
      simp only [map_mul, map_inv₀]
      have h := h_key; rw [← hc] at h
      generalize algebraMap (K p k) (L p k) α = αF at h hαF_ne ⊢
      generalize algebraMap (K p k) (L p k) c = cF at h hcF_ne ⊢
      field_simp; linear_combination h
  case neg =>
    right
    have h1dim :
        finrank (K p k)
          ↥(V ⊓ scaledSubmodule_KL p k (u * w⁻¹)⁻¹
            (inv_ne_zero hβ_ne) V) = 1 :=
      finrank_inf_scaled_ker_trace_KL p k (u * w⁻¹) hβ_ne hβ_base
    have hw_inf : w ∈
        V ⊓ scaledSubmodule_KL p k (u * w⁻¹)⁻¹ (inv_ne_zero hβ_ne) V := by
      refine Submodule.mem_inf.mpr ⟨hw, ?_⟩
      rw [mem_scaledSubmodule_KL_iff]
      exact ⟨u, hu, by field_simp⟩
    have hv_inf : v ∈
        V ⊓ scaledSubmodule_KL p k (u * w⁻¹)⁻¹ (inv_ne_zero hβ_ne) V := by
      refine Submodule.mem_inf.mpr ⟨hv, ?_⟩
      rw [mem_scaledSubmodule_KL_iff]
      refine ⟨(u * w⁻¹) * v, ?_, by field_simp⟩
      rw [h_key, show (algebraMap (K p k) (L p k) α) * x = α • x
        from (Algebra.smul_def α x).symm]
      exact V.smul_mem α hx
    obtain ⟨c, hc_ne, hvc⟩ :=
      proportional_of_finrank_one_KL p k _ h1dim w v hw_inf hv_inf hw0 hv0
    have hcF_ne : (algebraMap (K p k) (L p k) c) ≠ 0 := by simp [hc_ne]
    have hvc' : v = (algebraMap (K p k) (L p k) c) * w := by
      rw [hvc, Algebra.smul_def]
    have hcu : (algebraMap (K p k) (L p k) c) * u =
        (algebraMap (K p k) (L p k) α) * x := by
      have h := h_key; rw [hvc'] at h
      generalize algebraMap (K p k) (L p k) α = αF at h hαF_ne ⊢
      generalize algebraMap (K p k) (L p k) c = cF at h hcF_ne hvc' ⊢
      field_simp at h ⊢; linear_combination h
    constructor
    · rw [singerMk_KL_eq_iff]
      refine ⟨c * α⁻¹, ?_⟩
      simp only [map_mul, map_inv₀]
      generalize algebraMap (K p k) (L p k) α = αF at hαF_ne hcu ⊢
      generalize algebraMap (K p k) (L p k) c = cF at hcF_ne hcu ⊢
      field_simp; linear_combination hcu
    · rw [singerMk_KL_eq_iff]
      refine ⟨c⁻¹, ?_⟩
      simp only [map_inv₀]
      rw [hvc']
      generalize algebraMap (K p k) (L p k) c = cF at hcF_ne ⊢
      field_simp

end Erdos30.SingerPrimePower
-- END upstream SingerPrimePowerSidon.lean

-- BEGIN upstream SingerPrimePowerTheorem.lean
/-
Prime-power Singer finite-field core for the public Singer/Sidon Lean artifact.

This file is exported from the Erdős 30 research repository at d0d1/erdos
from `work/erdos-30/formal/Erdos30/SingerPrimePowerTheorem.lean` at commit
`ca225a0bb39ce131d31d8a949133b3c17f60acfa`.

Public-export edits: the top comment was neutralized for this artifact, and a
stale source line-number reference in the final theorem docstring was removed.
-/


set_option maxHeartbeats 400000000

open Erdos30 Erdos30.SingerPrimePower

namespace Erdos30.SingerPrimePower

variable (p : ℕ) [Fact p.Prime] (k : ℕ) [NeZero k]

/-- The Singer quotient group `Q'_KL := L× / baseUnitsSubgroup_KL`. -/
private noncomputable abbrev V_KL := (Algebra.trace (K p k) (L p k)).ker
private noncomputable abbrev Q_KL := (L p k)ˣ ⧸ baseUnitsSubgroup_KL p k

/-- A quotient of the cyclic group `L×` (cyclic because `L` is a
finite field) is cyclic. This instance is not automatically
synthesized in this abstract setup, unlike the prime-only
version where Lean happens to find it. -/
private noncomputable instance instIsCyclicQ_KL : IsCyclic (Q_KL p k) := by
  haveI : IsCyclic ((L p k)ˣ) := inferInstance
  exact isCyclic_of_surjective (QuotientGroup.mk' (baseUnitsSubgroup_KL p k))
    (QuotientGroup.mk'_surjective (baseUnitsSubgroup_KL p k))

noncomputable section

/-! ## Representatives of projective lines in `ker(Tr)` -/

private noncomputable def kerBasis_KL :=
  (Module.finBasis (K p k) ↥(V_KL p k)).reindex
    ((Fin.castOrderIso (finrank_ker_trace_KL p k)).toEquiv)

private noncomputable def repV_KL (i : Option (K p k)) : V_KL p k :=
  match i with
  | none => (kerBasis_KL p k) ⟨0, by omega⟩
  | some c => (kerBasis_KL p k) ⟨1, by omega⟩ + c • (kerBasis_KL p k) ⟨0, by omega⟩

private noncomputable def rep_KL (i : Option (K p k)) : L p k := (repV_KL p k i).val

private lemma rep_KL_mem (i : Option (K p k)) :
    rep_KL p k i ∈ (Algebra.trace (K p k) (L p k)).ker := (repV_KL p k i).2

private lemma rep_KL_ne_zero (i : Option (K p k)) : rep_KL p k i ≠ 0 := by
  intro h; have hV : repV_KL p k i = 0 := Subtype.ext h
  cases i with
  | none => exact (kerBasis_KL p k).ne_zero ⟨0, by omega⟩ hV
  | some c =>
    have heq := congr_arg (kerBasis_KL p k).repr hV
    simp only [repV_KL, map_add, map_smul, (kerBasis_KL p k).repr_self, map_zero] at heq
    have h1 := DFunLike.congr_fun heq ⟨1, by omega⟩
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      Finsupp.zero_apply,
      show (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) from rfl,
      show ((⟨0, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2)) = False from
        by simp [Fin.ext_iff],
      ite_true, ite_false, mul_zero, add_zero] at h1
    exact one_ne_zero h1

private lemma rep_KL_proportional_imp_eq (i j : Option (K p k)) (α : K p k)
    (hprop : repV_KL p k j = α • repV_KL p k i) : i = j := by
  have heq := congr_arg (kerBasis_KL p k).repr hprop
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some c =>
      simp only [repV_KL, map_add, map_smul, (kerBasis_KL p k).repr_self] at heq
      have h1 := DFunLike.congr_fun heq ⟨1, by omega⟩
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
        show (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) from rfl,
        show ((⟨0, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2)) = False from
          by simp [Fin.ext_iff],
        ite_true, ite_false, mul_zero, add_zero, mul_one] at h1
      exact absurd h1 one_ne_zero
  | some a =>
    cases j with
    | none =>
      simp only [repV_KL, map_add, map_smul, (kerBasis_KL p k).repr_self] at heq
      have h1 := DFunLike.congr_fun heq ⟨1, by omega⟩
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
        show (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) from rfl,
        show ((⟨0, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2)) = False from
          by simp [Fin.ext_iff],
        ite_true, ite_false, mul_zero, add_zero, mul_one] at h1
      exfalso; exact rep_KL_ne_zero p k none (show rep_KL p k none = 0 from by
        show (repV_KL p k none).val = 0
        have := hprop; rw [show α = 0 from h1.symm, zero_smul] at this
        exact congrArg Subtype.val this)
    | some b =>
      simp only [repV_KL, map_add, map_smul, (kerBasis_KL p k).repr_self] at heq
      have h1 := DFunLike.congr_fun heq ⟨1, by omega⟩
      have h0 := DFunLike.congr_fun heq ⟨0, by omega⟩
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
        show (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) from rfl,
        show ((⟨0, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2)) = False from
          by simp [Fin.ext_iff],
        show (⟨0, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2) from rfl,
        show ((⟨1, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2)) = False from
          by simp [Fin.ext_iff],
        ite_true, ite_false, mul_zero, add_zero, mul_one, zero_add] at h1 h0
      congr 1; rw [← h1, one_mul] at h0; exact h0.symm

private lemma singerMk_KL_rep_injective :
    Function.Injective
      (fun i => singerMk_KL p k (rep_KL p k i) (rep_KL_ne_zero p k i)) := by
  intro i j hij
  rw [singerMk_KL_eq_iff] at hij
  obtain ⟨α, hα⟩ := hij
  have hri := rep_KL_ne_zero p k i
  have hprop_field :
      rep_KL p k j = (algebraMap (K p k) (L p k) α) * rep_KL p k i := by
    have h1 : (rep_KL p k i) * ((rep_KL p k i)⁻¹ * rep_KL p k j) = rep_KL p k j := by
      rw [← mul_assoc, mul_inv_cancel₀ hri, one_mul]
    rw [← h1, hα]; ring
  have hV : repV_KL p k j = α • repV_KL p k i := by
    apply Subtype.ext
    change rep_KL p k j = (α • repV_KL p k i).val
    rw [show (α • repV_KL p k i).val = α • (repV_KL p k i).val from rfl]
    rw [show α • (repV_KL p k i).val =
      (algebraMap (K p k) (L p k) α) * (repV_KL p k i).val
      from Algebra.smul_def α _]
    exact hprop_field
  exact rep_KL_proportional_imp_eq p k i j α hV

/-! ## Cyclic group cardinality and isomorphism -/

private lemma Q_KL_card_eq : Nat.card (Q_KL p k) = (p ^ k) ^ 2 + p ^ k + 1 := by
  rw [show Nat.card (Q_KL p k) = (baseUnitsSubgroup_KL p k).index from
    (Subgroup.index_eq_card _).symm]
  exact baseUnitsSubgroup_index_KL p k

private noncomputable def mulEquivQ_KL :
    Multiplicative (ZMod ((p ^ k) ^ 2 + p ^ k + 1)) ≃* Q_KL p k := by
  haveI : NeZero ((p ^ k) ^ 2 + p ^ k + 1) := ⟨by positivity⟩
  haveI : IsCyclic (Q_KL p k) := inferInstance
  let g := Classical.choose (IsCyclic.exists_generator (α := Q_KL p k))
  have hg : ∀ x : Q_KL p k, x ∈ Subgroup.zpowers g :=
    Classical.choose_spec (IsCyclic.exists_generator (α := Q_KL p k))
  have htop : Subgroup.zpowers g = ⊤ := by ext x; exact ⟨fun _ => trivial, fun _ => hg x⟩
  have hord : orderOf g = (p ^ k) ^ 2 + p ^ k + 1 := by
    have h1 : Nat.card ↥(Subgroup.zpowers g) = orderOf g := Nat.card_zpowers g
    have h2 : Nat.card ↥(Subgroup.zpowers g) = Nat.card (Q_KL p k) := by
      rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
    have := Q_KL_card_eq p k; omega
  let φ : Multiplicative (ZMod ((p ^ k) ^ 2 + p ^ k + 1)) →* Q_KL p k :=
    MonoidHom.mk' (fun j => g ^ (ZMod.val (Multiplicative.toAdd j))) (fun a b => by
      show g ^ ZMod.val (Multiplicative.toAdd a + Multiplicative.toAdd b) =
        g ^ ZMod.val (Multiplicative.toAdd a) * g ^ ZMod.val (Multiplicative.toAdd b)
      rw [← pow_add, pow_eq_pow_iff_modEq, hord]
      unfold Nat.ModEq; rw [ZMod.val_add]
      exact Nat.mod_mod_of_dvd _ (dvd_refl _))
  have hφ_apply : ∀ j, φ j = g ^ (ZMod.val (Multiplicative.toAdd j)) := fun _ => rfl
  exact MulEquiv.ofBijective φ ⟨by
    intro a b hab
    have hab' : g ^ (ZMod.val (Multiplicative.toAdd a)) =
        g ^ (ZMod.val (Multiplicative.toAdd b)) := by
      rw [← hφ_apply, ← hφ_apply]; exact hab
    have hinj := @pow_injOn_Iio_orderOf (Q_KL p k) _ g
    have ha : ZMod.val (Multiplicative.toAdd a) ∈ Set.Iio (orderOf g) := by
      rw [Set.mem_Iio, hord]; exact ZMod.val_lt _
    have hb : ZMod.val (Multiplicative.toAdd b) ∈ Set.Iio (orderOf g) := by
      rw [Set.mem_Iio, hord]; exact ZMod.val_lt _
    cases a; cases b; exact congrArg _ (ZMod.val_injective _ (hinj ha hb hab')),
  by
    intro x
    obtain ⟨m, hm⟩ := (hg x : ∃ m : ℤ, g ^ m = x)
    have hpos : (0 : ℤ) < (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ) := by positivity
    have hmod_nn : 0 ≤ m % (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ) :=
      Int.emod_nonneg _ (by linarith)
    have hmod_lt :
        (m % (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ)).toNat < (p ^ k) ^ 2 + p ^ k + 1 := by
      have := Int.emod_lt_of_pos m hpos; omega
    let j : Multiplicative (ZMod ((p ^ k) ^ 2 + p ^ k + 1)) :=
      Multiplicative.ofAdd
        ((m % (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ)).toNat :
          ZMod ((p ^ k) ^ 2 + p ^ k + 1))
    refine ⟨j, ?_⟩
    have hφj : φ j = g ^ (m % (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ)).toNat := by
      rw [hφ_apply]; congr 1; exact ZMod.val_natCast_of_lt hmod_lt
    have key : g ^ ((m % (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ)).toNat : ℤ) = g ^ m := by
      rw [zpow_eq_zpow_iff_modEq, hord]
      change ((m % (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ)).toNat : ℤ) %
          (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ) =
        m % (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ)
      rw [Int.toNat_of_nonneg hmod_nn, Int.emod_emod_of_dvd _ dvd_rfl]
    calc φ j = g ^ (m % (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ)).toNat := hφj
      _ = g ^ ((m % (((p ^ k) ^ 2 + p ^ k + 1 : ℕ) : ℤ)).toNat : ℤ) :=
        (zpow_natCast g _).symm
      _ = g ^ m := key
      _ = x := hm⟩

/-! ## Finset construction and `IsSidonMod` proof -/

/-- **Prime-power Singer set.** For each prime `p` and exponent
`k ≥ 1`, there exists `S : Finset ℤ` with
`IsSidonMod (q² + q + 1) S` and `S.card = q + 1` where
`q := p^k`. Mirrors `singer_sidon_set_of`. -/
theorem singer_primePower_sidon_set_KL :
    ∃ S : Finset ℤ,
      IsSidonMod ((p ^ k : ℤ) * (p ^ k : ℤ) + (p ^ k : ℤ) + 1) S ∧
      S.card = p ^ k + 1 := by
  haveI : NeZero ((p ^ k) ^ 2 + p ^ k + 1) := ⟨by positivity⟩
  let φ := mulEquivQ_KL p k
  let f : Option (K p k) → ℤ := fun i =>
    ↑(ZMod.val (Multiplicative.toAdd
      (φ.symm (singerMk_KL p k (rep_KL p k i) (rep_KL_ne_zero p k i)))))
  let S : Finset ℤ := Finset.univ.image f
  refine ⟨S, ?_, ?_⟩
  · intro a b c d ha hb hc hd hdvd
    rw [Finset.mem_image] at ha hb hc hd
    obtain ⟨ia, _, rfl⟩ := ha; obtain ⟨ib, _, rfl⟩ := hb
    obtain ⟨ic, _, rfl⟩ := hc; obtain ⟨id, _, rfl⟩ := hd
    set qa := singerMk_KL p k (rep_KL p k ia) (rep_KL_ne_zero p k ia)
    set qb := singerMk_KL p k (rep_KL p k ib) (rep_KL_ne_zero p k ib)
    set qc := singerMk_KL p k (rep_KL p k ic) (rep_KL_ne_zero p k ic)
    set qd := singerMk_KL p k (rep_KL p k id) (rep_KL_ne_zero p k id)
    have hzmod : Multiplicative.toAdd (φ.symm qa) + Multiplicative.toAdd (φ.symm qb) =
        Multiplicative.toAdd (φ.symm qc) + Multiplicative.toAdd (φ.symm qd) := by
      have h0 : ((((ZMod.val (Multiplicative.toAdd (φ.symm qa)) : ℤ) +
          (ZMod.val (Multiplicative.toAdd (φ.symm qb)) : ℤ)) -
          ((ZMod.val (Multiplicative.toAdd (φ.symm qc)) : ℤ) +
          (ZMod.val (Multiplicative.toAdd (φ.symm qd)) : ℤ)) : ℤ) :
            ZMod ((p ^ k) ^ 2 + p ^ k + 1)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        convert hdvd using 1
        push_cast; ring
      simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val] at h0
      exact sub_eq_zero.mp h0
    have hQ : qa * qb = qc * qd := by
      have hmult : φ.symm qa * φ.symm qb = φ.symm qc * φ.symm qd := by
        show Multiplicative.ofAdd (Multiplicative.toAdd (φ.symm qa) +
            Multiplicative.toAdd (φ.symm qb)) =
          Multiplicative.ofAdd (Multiplicative.toAdd (φ.symm qc) +
            Multiplicative.toAdd (φ.symm qd))
        exact congrArg _ hzmod
      have hφ := congrArg φ hmult
      simp only [map_mul, MulEquiv.apply_symm_apply] at hφ
      exact hφ
    have hmul_l : qa * qb = singerMk_KL p k (rep_KL p k ia * rep_KL p k ib)
        (mul_ne_zero (rep_KL_ne_zero p k ia) (rep_KL_ne_zero p k ib)) := by
      show QuotientGroup.mk (Units.mk0 _ _) * QuotientGroup.mk (Units.mk0 _ _) =
        QuotientGroup.mk (Units.mk0 _ _)
      rw [← QuotientGroup.mk_mul]; congr 1; ext; rfl
    have hmul_r : qc * qd = singerMk_KL p k (rep_KL p k ic * rep_KL p k id)
        (mul_ne_zero (rep_KL_ne_zero p k ic) (rep_KL_ne_zero p k id)) := by
      show QuotientGroup.mk (Units.mk0 _ _) * QuotientGroup.mk (Units.mk0 _ _) =
        QuotientGroup.mk (Units.mk0 _ _)
      rw [← QuotientGroup.mk_mul]; congr 1; ext; rfl
    rw [hmul_l, hmul_r] at hQ
    rw [singerMk_KL_eq_iff] at hQ
    obtain ⟨α, hα⟩ := hQ
    have hab_ne : rep_KL p k ia * rep_KL p k ib ≠ 0 :=
      mul_ne_zero (rep_KL_ne_zero p k ia) (rep_KL_ne_zero p k ib)
    have hcd_ne : rep_KL p k ic * rep_KL p k id ≠ 0 :=
      mul_ne_zero (rep_KL_ne_zero p k ic) (rep_KL_ne_zero p k id)
    have hα_ne : α ≠ 0 := by
      intro h0; rw [h0, map_zero] at hα
      exact mul_ne_zero (inv_ne_zero hab_ne) hcd_ne hα.symm
    have hcd_eq : rep_KL p k ic * rep_KL p k id =
        (algebraMap (K p k) (L p k)) α * (rep_KL p k ia * rep_KL p k ib) := by
      calc rep_KL p k ic * rep_KL p k id
          = (rep_KL p k ia * rep_KL p k ib) *
            ((rep_KL p k ia * rep_KL p k ib)⁻¹ * (rep_KL p k ic * rep_KL p k id)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hab_ne, one_mul]
        _ = (rep_KL p k ia * rep_KL p k ib) *
            (algebraMap (K p k) (L p k)) α := by rw [hα]
        _ = (algebraMap (K p k) (L p k)) α *
            (rep_KL p k ia * rep_KL p k ib) := mul_comm _ _
    have hsq := singer_quotient_sidon_KL p k
      (rep_KL p k ic) (rep_KL p k id) (rep_KL p k ia) (rep_KL p k ib)
      (rep_KL_mem p k ic) (rep_KL_mem p k id)
      (rep_KL_mem p k ia) (rep_KL_mem p k ib)
      (rep_KL_ne_zero p k ic) (rep_KL_ne_zero p k id)
      (rep_KL_ne_zero p k ia) (rep_KL_ne_zero p k ib)
      α hα_ne hcd_eq
    cases hsq with
    | inl h =>
      left; constructor
      · exact congrArg f (singerMk_KL_rep_injective p k h.1.symm)
      · exact congrArg f (singerMk_KL_rep_injective p k h.2.symm)
    | inr h =>
      right; constructor
      · exact congrArg f (singerMk_KL_rep_injective p k h.2.symm)
      · exact congrArg f (singerMk_KL_rep_injective p k h.1.symm)
  · rw [Finset.card_image_of_injective _ (by
      intro i j hij
      have h1 : (ZMod.val (Multiplicative.toAdd
          (φ.symm (singerMk_KL p k (rep_KL p k i) (rep_KL_ne_zero p k i)))) : ℤ) =
        ↑(ZMod.val (Multiplicative.toAdd
          (φ.symm (singerMk_KL p k (rep_KL p k j) (rep_KL_ne_zero p k j))))) := hij
      have h2 := Nat.cast_injective h1
      have h3 := ZMod.val_injective _ h2
      have h4 : φ.symm (singerMk_KL p k (rep_KL p k i) (rep_KL_ne_zero p k i)) =
          φ.symm (singerMk_KL p k (rep_KL p k j) (rep_KL_ne_zero p k j)) :=
        Multiplicative.toAdd.injective h3
      have h5 := φ.symm.injective h4
      exact singerMk_KL_rep_injective p k h5)]
    have hKcard : Fintype.card (K p k) = p ^ k := by
      rw [← Nat.card_eq_fintype_card]; exact card_K p k
    simp [Finset.card_univ, Fintype.card_option, hKcard]

end

end Erdos30.SingerPrimePower

-- END upstream SingerPrimePowerTheorem.lean
