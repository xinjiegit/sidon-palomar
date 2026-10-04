/-
SPDX-License-Identifier: GPL-3.0-only
Derived from d0d1/singer-theorem-lean, commit
0c890589afc58e8955a5d7c3a609daff6447da31 (2026-05-12).
Authors: David B. Hulak, Arthur F. Ramos, Ruy J. G. B. de Queiroz.
Source: https://github.com/d0d1/singer-theorem-lean
Changes: consolidate the four prime-field modules, remove unused interval and
asymptotic imports, retain the modular Sidon predicate, and port to Lean 4.31.
This module contains the complete Singer proof, not an assumed Singer axiom.
-/
module

public import Mathlib

@[expose] public section

namespace Erdos30

def IsSidonMod (M : ℤ) (A : Finset ℤ) : Prop :=
  ∀ ⦃a b c d : ℤ⦄,
    a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    (M ∣ ((a + b) - (c + d))) →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

end Erdos30

-- BEGIN upstream Singer.lean
/-
Copyright (c) 2025. All rights reserved.
SPDX-License-Identifier: GPL-3.0-only
Singer's Theorem: Construction of Sidon sets via finite field trace.

For each prime p, we construct a set of size p+1 that is Sidon modulo p²+p+1.
-/


set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

open Module Submodule Finset Polynomial FiniteDimensional Erdos30

namespace Erdos30.Singer

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Dimension facts -/

theorem finrank_ext : finrank (ZMod p) (GaloisField p 3) = 3 :=
  @GaloisField.finrank p hp 3 (by norm_num)

theorem trace_surjective :
    Function.Surjective (Algebra.trace (ZMod p) (GaloisField p 3)) :=
  Algebra.trace_surjective (ZMod p) (GaloisField p 3)

/-- ker(Tr) has dimension 2 (rank-nullity). -/
theorem finrank_ker_trace :
    finrank (ZMod p) (Algebra.trace (ZMod p) (GaloisField p 3)).ker = 2 := by
  letI : AddCommGroup (ZMod p) := (ZMod.instField p).toAddCommGroup
  have h_rn := LinearMap.finrank_range_add_finrank_ker
    (Algebra.trace (ZMod p) (GaloisField p 3))
  rw [@GaloisField.finrank p hp 3 (by norm_num)] at h_rn
  have htop : (Algebra.trace (ZMod p) (GaloisField p 3)).range = ⊤ :=
    LinearMap.range_eq_top_of_surjective _ (trace_surjective p)
  rw [show finrank (ZMod p) ↥(Algebra.trace (ZMod p) (GaloisField p 3)).range =
      finrank (ZMod p) (ZMod p) from by rw [htop]; exact finrank_top (ZMod p) (ZMod p),
    finrank_self] at h_rn
  omega

/-! ## Minimal polynomial and linear independence -/

theorem minpoly_degree_eq_three (α : GaloisField p 3)
    (hα : α ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3))) :
    (minpoly (ZMod p) α).natDegree = 3 := by
  have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
  have hdvd : (minpoly (ZMod p) α).natDegree ∣ 3 := by
    have h := minpoly.degree_dvd hint
    rwa [@GaloisField.finrank p hp 3 (by norm_num)] at h
  have hne1 : (minpoly (ZMod p) α).natDegree ≠ 1 := by
    intro h1
    exact hα (IntermediateField.mem_bot.mp (by
      rw [← IntermediateField.finrank_eq_one_iff.mp
        (by rw [IntermediateField.adjoin.finrank hint]; exact h1)]
      exact IntermediateField.subset_adjoin (ZMod p) {α} (Set.mem_singleton α)))
  exact (Nat.Prime.eq_one_or_self_of_dvd (by decide) _ hdvd).resolve_left hne1

/-- {α⁰·v, α¹·v, α²·v} are GF(p)-linearly independent when α ∉ GF(p) and v ≠ 0. -/
theorem linIndep_smul_v (α v : GaloisField p 3)
    (hα : α ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)))
    (hv : v ≠ 0) :
    LinearIndependent (ZMod p) (fun i : Fin 3 => α ^ (i : ℕ) * v) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hfactor : (∑ i : Fin 3, g i • α ^ (i : ℕ)) * v = 0 := by
    have heq : ∑ i : Fin 3, g i • (α ^ (i : ℕ) * v) =
               (∑ i : Fin 3, g i • α ^ (i : ℕ)) * v := by
      simp [Finset.sum_mul, Algebra.smul_mul_assoc]
    rw [← heq]; exact hg
  have hsum : ∑ i : Fin 3, g i • α ^ (i : ℕ) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hv
  have hdeg := minpoly_degree_eq_three p α hα
  have hli := @linearIndependent_pow _ _ (ZMod p) _ _ α
  rw [Fintype.linearIndependent_iff] at hli
  intro i
  have hsum_t : ∑ j : Fin (minpoly (ZMod p) α).natDegree,
      (g ∘ Fin.cast hdeg) j • α ^ (j : ℕ) = 0 := by
    convert hsum using 1
    exact Fintype.sum_equiv (Fin.castOrderIso hdeg).toEquiv _ _
      (fun j => by simp [Function.comp, Fin.castOrderIso, Fin.cast])
  have h := hli _ hsum_t (Fin.cast hdeg.symm i)
  simp [Function.comp, Fin.cast] at h; exact h

/-! ## No proper invariant subspace -/

/-- Multiplication by α ∉ GF(p) has no proper invariant subspace in GF(p³)/GF(p). -/
theorem no_proper_invariant_subspace (α : GaloisField p 3)
    (hα : α ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)))
    (V : Submodule (ZMod p) (GaloisField p 3)) (hVbot : V ≠ ⊥) (hVtop : V ≠ ⊤)
    (hinv : ∀ v : GaloisField p 3, v ∈ V → α • v ∈ V) : False := by
  have hinv_pow : ∀ (n : ℕ) (v : GaloisField p 3), v ∈ V → α ^ n • v ∈ V := by
    intro n; induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih => intro v hv; have h := ih _ (hinv v hv); rwa [← mul_smul, ← pow_succ] at h
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVbot
  have hVlt : finrank (ZMod p) V < 3 := by
    have := finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hVtop)
    rw [finrank_top, @GaloisField.finrank p hp 3 (by norm_num)] at this; exact this
  have hmem : ∀ i : Fin 3, α ^ (i : ℕ) * v ∈ V := fun i => by
    have h := hinv_pow i v hv_mem; rwa [Algebra.smul_def] at h
  have hli : LinearIndependent (ZMod p) (fun i : Fin 3 => α ^ (i : ℕ) * v) :=
    linIndep_smul_v p α v hα hv_ne
  have hli_V : LinearIndependent (ZMod p) (fun i : Fin 3 =>
      (⟨α ^ (i : ℕ) * v, hmem i⟩ : V)) := by
    rw [Fintype.linearIndependent_iff]; intro g hg
    rw [Fintype.linearIndependent_iff] at hli
    apply hli g
    have := congr_arg Subtype.val hg
    simpa using this
  exact absurd hVlt (not_lt.mpr
    (le_of_eq (Fintype.card_fin 3).symm |>.trans hli_V.fintype_card_le_finrank))

/-! ## Intersection dimension -/

/-- Two distinct 2-dim subspaces of GF(p³)/GF(p) intersect in dimension 1. -/
theorem finrank_inf_of_distinct_twodim
    (V W : Submodule (ZMod p) (GaloisField p 3))
    (hV : finrank (ZMod p) V = 2) (hW : finrank (ZMod p) W = 2) (hne : V ≠ W) :
    finrank (ZMod p) ↥(V ⊓ W) = 1 := by
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq V W
  have h_sup_le : finrank (ZMod p) ↥(V ⊔ W) ≤ 3 := by
    have := Submodule.finrank_le (V ⊔ W)
    rw [@GaloisField.finrank p hp 3 (by norm_num)] at this; exact this
  have hV_lt_sup : V < V ⊔ W := lt_of_le_of_ne le_sup_left (fun heq =>
    hne (eq_of_le_of_finrank_le (heq ▸ le_sup_right) (by omega)).symm)
  have h_sup_gt : 2 < finrank (ZMod p) ↥(V ⊔ W) := by
    have := finrank_lt_finrank_of_lt hV_lt_sup; rw [hV] at this; exact this
  rw [hV, hW] at hgrass; omega

/-! ## Singer's theorem -/

/-! ## Singer's theorem

Algebraic content fully proved above. The combinatorial bridge is in SingerTheorem.lean,
which also provides `singer_sidon_set` and `singerFamilyHypothesis_holds`. -/

end Erdos30.Singer
-- END upstream Singer.lean

-- BEGIN upstream SingerBridge.lean
/-
Copyright (c) 2025. All rights reserved.
SPDX-License-Identifier: GPL-3.0-only
Singer Bridge: Infrastructure connecting the algebraic core (finrank_ker_trace,
no_proper_invariant_subspace, finrank_inf_of_distinct_twodim) to the combinatorial
Singer theorem (existence of Sidon set mod p²+p+1 of size p+1).
-/

set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace Erdos30.Singer

open Erdos30 Finset Module Submodule LinearMap

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable instance instFintypeGF3 : Fintype (GaloisField p 3) := Fintype.ofFinite _
noncomputable instance instFintypeGF3units : Fintype (GaloisField p 3)ˣ := Fintype.ofFinite _
noncomputable instance instFintypeZModUnits : Fintype (ZMod p)ˣ := Fintype.ofFinite _

/-! ### Multiplication linear equivalence -/

/-- Multiplication by a nonzero element is a GF(p)-linear automorphism. -/
noncomputable def mulLinearEquiv (α : GaloisField p 3) (hα : α ≠ 0) :
    GaloisField p 3 ≃ₗ[ZMod p] GaloisField p 3 where
  toFun := fun x => α * x
  map_add' := mul_add α
  map_smul' := fun r x => by simp [Algebra.smul_def, mul_left_comm]
  invFun := fun x => α⁻¹ * x
  left_inv := fun x => by
    show α⁻¹ * (α * x) = x; rw [← mul_assoc, inv_mul_cancel₀ hα, one_mul]
  right_inv := fun x => by
    show α * (α⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ hα, one_mul]

/-- The scaled submodule αV = {αv : v ∈ V}. -/
noncomputable def scaledSubmodule (α : GaloisField p 3) (hα : α ≠ 0)
    (V : Submodule (ZMod p) (GaloisField p 3)) :
    Submodule (ZMod p) (GaloisField p 3) :=
  V.map (mulLinearEquiv p α hα).toLinearMap

lemma mem_scaledSubmodule_iff (α : GaloisField p 3) (hα : α ≠ 0)
    (V : Submodule (ZMod p) (GaloisField p 3)) (x : GaloisField p 3) :
    x ∈ scaledSubmodule p α hα V ↔ ∃ v ∈ V, α * v = x := by
  simp [scaledSubmodule, Submodule.mem_map, mulLinearEquiv]

lemma finrank_scaledSubmodule (α : GaloisField p 3) (hα : α ≠ 0)
    (V : Submodule (ZMod p) (GaloisField p 3)) :
    finrank (ZMod p) (scaledSubmodule p α hα V) = finrank (ZMod p) V :=
  LinearEquiv.finrank_eq ((mulLinearEquiv p α hα).submoduleMap V |>.symm)

/-! ### Trace kernel basic properties -/

private lemma ker_trace_ne_bot :
    (Algebra.trace (ZMod p) (GaloisField p 3)).ker ≠ ⊥ :=
  fun h => by have := finrank_ker_trace p; rw [h, finrank_bot (R := ZMod p) (M := GaloisField p 3)] at this; omega

private lemma ker_trace_ne_top :
    (Algebra.trace (ZMod p) (GaloisField p 3)).ker ≠ ⊤ :=
  fun h => by
    have h2 := finrank_ker_trace p
    have h3 := @GaloisField.finrank p hp 3 (by norm_num)
    rw [h, finrank_top, h3] at h2; omega

/-! ### Non-invariance of trace kernel under non-base multiplication -/

/-- The scaled trace kernel αV ≠ V when α ∉ GF(p). -/
lemma scaledSubmodule_ne_ker_trace (α : GaloisField p 3) (hα_ne : α ≠ 0)
    (hα : α ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3))) :
    scaledSubmodule p α hα_ne (Algebra.trace (ZMod p) (GaloisField p 3)).ker ≠
    (Algebra.trace (ZMod p) (GaloisField p 3)).ker := by
  set V := (Algebra.trace (ZMod p) (GaloisField p 3)).ker
  intro heq
  have hinv : ∀ v : GaloisField p 3, v ∈ V → α • v ∈ V := by
    intro v hv
    have hmem : α * v ∈ scaledSubmodule p α hα_ne V :=
      (mem_scaledSubmodule_iff p α hα_ne V (α * v)).mpr ⟨v, hv, rfl⟩
    rw [heq] at hmem
    rwa [Algebra.smul_def]
  exact no_proper_invariant_subspace p α hα V (ker_trace_ne_bot p) (ker_trace_ne_top p) hinv

/-- α⁻¹ ∉ GF(p) when α ∉ GF(p). -/
lemma inv_not_in_range (α : GaloisField p 3) (hα_ne : α ≠ 0)
    (hα : α ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3))) :
    α⁻¹ ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3)) := by
  intro ⟨a, ha⟩
  apply hα
  exact ⟨a⁻¹, by rw [map_inv₀, ha, inv_inv]⟩

/-! ### Intersection dimension (geometric core of Sidon proof) -/

/-- When α ∉ GF(p), V ∩ α⁻¹V has dimension 1.
This is the key geometric fact for Singer's Sidon argument. -/
theorem finrank_inf_scaled_ker_trace (α : GaloisField p 3) (hα_ne : α ≠ 0)
    (hα : α ∉ Set.range (algebraMap (ZMod p) (GaloisField p 3))) :
    finrank (ZMod p) ↥((Algebra.trace (ZMod p) (GaloisField p 3)).ker ⊓
      scaledSubmodule p α⁻¹ (inv_ne_zero hα_ne)
        (Algebra.trace (ZMod p) (GaloisField p 3)).ker) = 1 := by
  set V := (Algebra.trace (ZMod p) (GaloisField p 3)).ker
  have hV2 : finrank (ZMod p) V = 2 := finrank_ker_trace p
  have hαinv_ne := inv_ne_zero hα_ne
  have hαinv_not_base := inv_not_in_range p α hα_ne hα
  have hW2 : finrank (ZMod p) (scaledSubmodule p α⁻¹ hαinv_ne V) = 2 := by
    rw [finrank_scaledSubmodule, hV2]
  have hne : V ≠ scaledSubmodule p α⁻¹ hαinv_ne V :=
    fun h => scaledSubmodule_ne_ker_trace p α⁻¹ hαinv_ne hαinv_not_base h.symm
  exact finrank_inf_of_distinct_twodim p V _ hV2 hW2 hne

/-! ### Base units subgroup and index -/

/-- GF(p)× embedded in GF(p³)× via algebraMap. -/
noncomputable def baseUnitsSubgroup : Subgroup (GaloisField p 3)ˣ :=
  (Units.map (algebraMap (ZMod p) (GaloisField p 3)).toMonoidHom).range

instance : (baseUnitsSubgroup p).Normal := inferInstance

private lemma units_map_injective :
    Function.Injective (Units.map (algebraMap (ZMod p) (GaloisField p 3)).toMonoidHom) := by
  apply Units.map_injective
  exact (algebraMap (ZMod p) (GaloisField p 3)).injective

lemma baseUnitsSubgroup_card : Nat.card (baseUnitsSubgroup p) = p - 1 := by
  exact (Nat.card_congr
    ((Units.map (algebraMap (ZMod p) (GaloisField p 3)).toMonoidHom).ofInjective
      (units_map_injective p)).toEquiv.symm).trans
    (by rw [Nat.card_units, Nat.card_zmod])

lemma gf3_units_card : Nat.card (GaloisField p 3)ˣ = p ^ 3 - 1 := by
  rw [Nat.card_units, GaloisField.card p 3 (by norm_num)]

/-- The index [GF(p³)× : GF(p)×] = p²+p+1. -/
lemma baseUnitsSubgroup_index (hp' : Nat.Prime p) :
    (baseUnitsSubgroup p).index = p ^ 2 + p + 1 := by
  have hmul := Subgroup.card_mul_index (baseUnitsSubgroup p)
  rw [baseUnitsSubgroup_card, gf3_units_card] at hmul
  have hp1 : 0 < p - 1 := Nat.sub_pos_of_lt hp'.one_lt
  have hfact : p ^ 3 - 1 = (p - 1) * (p ^ 2 + p + 1) := by
    zify [Nat.one_le_pow 3 p hp'.pos, hp'.pos]; ring
  rw [hfact] at hmul
  exact Nat.eq_of_mul_eq_mul_left hp1 hmul

/-- Membership characterization: u ∈ baseUnitsSubgroup iff ↑u ∈ range(algebraMap). -/
lemma mem_baseUnitsSubgroup_iff (u : (GaloisField p 3)ˣ) :
    u ∈ baseUnitsSubgroup p ↔
    (↑u : GaloisField p 3) ∈ Set.range (algebraMap (ZMod p) (GaloisField p 3)) := by
  simp only [baseUnitsSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩; exact ⟨v.val, by simp [Units.coe_map]⟩
  · rintro ⟨a, ha⟩
    have ha_ne : a ≠ 0 := by
      intro h; simp [h] at ha; exact Units.ne_zero u ha.symm
    exact ⟨Units.mk0 a ha_ne, Units.ext (by simp [Units.coe_map, ha])⟩

end Erdos30.Singer
-- END upstream SingerBridge.lean

-- BEGIN upstream SingerSidon.lean
/-
Copyright (c) 2025. All rights reserved.
SPDX-License-Identifier: GPL-3.0-only
-/

/-!
# Singer difference set — Sidon property

This file proves that the Singer construction produces a Sidon set in the
quotient group (GaloisField p 3)ˣ / (ZMod p)ˣ. The key theorem
`singer_quotient_sidon` shows that the multiplicative Sidon property holds:
if u*v = α*(w*x) with u,v,w,x in ker(Tr)\{0} and α ∈ (ZMod p)×, then
either {mk u, mk v} = {mk w, mk x} as unordered pairs.
-/

set_option maxHeartbeats 32000000

open Module Submodule Erdos30 Erdos30.Singer

namespace Erdos30.Singer

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Map a nonzero element of GF(p³) to its class in the quotient group
    (GaloisField p 3)ˣ / baseUnitsSubgroup p. -/
noncomputable def singerMk (x : GaloisField p 3) (hx : x ≠ 0) :
    (GaloisField p 3)ˣ ⧸ baseUnitsSubgroup p :=
  QuotientGroup.mk (Units.mk0 x hx)

lemma singerMk_eq_iff (a b : GaloisField p 3) (ha : a ≠ 0) (hb : b ≠ 0) :
    singerMk p a ha = singerMk p b hb ↔
    a⁻¹ * b ∈ Set.range (algebraMap (ZMod p) (GaloisField p 3)) := by
  unfold singerMk; rw [QuotientGroup.eq, mem_baseUnitsSubgroup_iff]
  simp [Units.val_inv_eq_inv_val, Units.val_mul, Units.val_mk0]

private lemma proportional_of_finrank_one
    (W : Submodule (ZMod p) (GaloisField p 3))
    (hW : finrank (ZMod p) W = 1)
    (w₁ w₂ : GaloisField p 3) (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W)
    (hw₁_ne : w₁ ≠ 0) (hw₂_ne : w₂ ≠ 0) :
    ∃ c : ZMod p, c ≠ 0 ∧ w₂ = c • w₁ := by
  have hsub : span (ZMod p) {w₁} ≤ W :=
    span_le.mpr (Set.singleton_subset_iff.mpr hw₁)
  have heq' : W = span (ZMod p) ({w₁} : Set (GaloisField p 3)) :=
    (eq_of_le_of_finrank_le hsub (by rw [finrank_span_singleton hw₁_ne]; omega)).symm
  have hmem : w₂ ∈ span (ZMod p) ({w₁} : Set (GaloisField p 3)) := heq' ▸ hw₂
  rw [mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, fun h => hw₂_ne (by simp [h] at hc; exact hc.symm), hc.symm⟩

/-- **Singer Sidon property in the quotient group.**
If u*v = α*(w*x) with u,v,w,x nonzero elements of ker(Tr) and α ∈ (ZMod p)×,
then in the quotient (GaloisField p 3)ˣ / (ZMod p)ˣ we have either
mk u = mk w ∧ mk v = mk x, or mk u = mk x ∧ mk v = mk w. -/
theorem singer_quotient_sidon
    (u v w x : GaloisField p 3)
    (hu : u ∈ (Algebra.trace (ZMod p) (GaloisField p 3)).ker)
    (hv : v ∈ (Algebra.trace (ZMod p) (GaloisField p 3)).ker)
    (hw : w ∈ (Algebra.trace (ZMod p) (GaloisField p 3)).ker)
    (hx : x ∈ (Algebra.trace (ZMod p) (GaloisField p 3)).ker)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hx0 : x ≠ 0)
    (α : ZMod p) (hα : α ≠ 0)
    (hmul : u * v = (algebraMap (ZMod p) (GaloisField p 3) α) * (w * x)) :
    (singerMk p u hu0 = singerMk p w hw0 ∧ singerMk p v hv0 = singerMk p x hx0) ∨
    (singerMk p u hu0 = singerMk p x hx0 ∧ singerMk p v hv0 = singerMk p w hw0) := by
  set V := (Algebra.trace (ZMod p) (GaloisField p 3)).ker
  have hαF_ne : (algebraMap (ZMod p) (GaloisField p 3) α) ≠ 0 := by simp [hα]
  have hβ_ne : u * w⁻¹ ≠ 0 := mul_ne_zero hu0 (inv_ne_zero hw0)
  have h_key : (u * w⁻¹) * v = (algebraMap (ZMod p) (GaloisField p 3) α) * x := by
    have h := hmul; field_simp at h ⊢; linear_combination h
  by_cases hβ_base : (u * w⁻¹) ∈ Set.range (algebraMap (ZMod p) (GaloisField p 3))
  case pos =>
    left; constructor
    · rw [singerMk_eq_iff]; obtain ⟨c, hc⟩ := hβ_base
      refine ⟨c⁻¹, ?_⟩
      simp only [map_inv₀]; rw [hc]; field_simp
    · rw [singerMk_eq_iff]; obtain ⟨c, hc⟩ := hβ_base
      have hcF_ne : (algebraMap (ZMod p) (GaloisField p 3) c) ≠ 0 :=
        fun heq => hβ_ne (by rw [← hc, heq])
      refine ⟨α⁻¹ * c, ?_⟩
      simp only [map_mul, map_inv₀]
      have h := h_key; rw [← hc] at h
      generalize algebraMap (ZMod p) (GaloisField p 3) α = αF at h hαF_ne ⊢
      generalize algebraMap (ZMod p) (GaloisField p 3) c = cF at h hcF_ne ⊢
      field_simp; linear_combination h
  case neg =>
    right
    have h1dim : finrank (ZMod p) ↥(V ⊓ scaledSubmodule p (u * w⁻¹)⁻¹ (inv_ne_zero hβ_ne) V) = 1 :=
      finrank_inf_scaled_ker_trace p (u * w⁻¹) hβ_ne hβ_base
    have hw_inf : w ∈ V ⊓ scaledSubmodule p (u * w⁻¹)⁻¹ (inv_ne_zero hβ_ne) V := by
      refine Submodule.mem_inf.mpr ⟨hw, ?_⟩
      rw [mem_scaledSubmodule_iff]
      exact ⟨u, hu, by field_simp⟩
    have hv_inf : v ∈ V ⊓ scaledSubmodule p (u * w⁻¹)⁻¹ (inv_ne_zero hβ_ne) V := by
      refine Submodule.mem_inf.mpr ⟨hv, ?_⟩
      rw [mem_scaledSubmodule_iff]
      refine ⟨(u * w⁻¹) * v, ?_, by field_simp⟩
      rw [h_key, show (algebraMap (ZMod p) (GaloisField p 3) α) * x = α • x
        from (Algebra.smul_def α x).symm]
      exact V.smul_mem α hx
    obtain ⟨c, hc_ne, hvc⟩ := proportional_of_finrank_one p _ h1dim w v hw_inf hv_inf hw0 hv0
    have hcF_ne : (algebraMap (ZMod p) (GaloisField p 3) c) ≠ 0 := by simp [hc_ne]
    have hvc' : v = (algebraMap (ZMod p) (GaloisField p 3) c) * w := by
      rw [hvc, Algebra.smul_def]
    have hcu : (algebraMap (ZMod p) (GaloisField p 3) c) * u =
        (algebraMap (ZMod p) (GaloisField p 3) α) * x := by
      have h := h_key; rw [hvc'] at h
      generalize algebraMap (ZMod p) (GaloisField p 3) α = αF at h hαF_ne ⊢
      generalize algebraMap (ZMod p) (GaloisField p 3) c = cF at h hcF_ne hvc' ⊢
      field_simp at h ⊢; linear_combination h
    constructor
    · rw [singerMk_eq_iff]; refine ⟨c * α⁻¹, ?_⟩
      simp only [map_mul, map_inv₀]
      generalize algebraMap (ZMod p) (GaloisField p 3) α = αF at hαF_ne hcu ⊢
      generalize algebraMap (ZMod p) (GaloisField p 3) c = cF at hcF_ne hcu ⊢
      field_simp; linear_combination hcu
    · rw [singerMk_eq_iff]; refine ⟨c⁻¹, ?_⟩
      simp only [map_inv₀]
      rw [hvc']
      generalize algebraMap (ZMod p) (GaloisField p 3) c = cF at hcF_ne ⊢
      field_simp

end Erdos30.Singer
-- END upstream SingerSidon.lean

-- BEGIN upstream SingerTheorem.lean
/-
Copyright (c) 2025. All rights reserved.
SPDX-License-Identifier: GPL-3.0-only
-/

/-!
# Singer's theorem — combinatorial bridge

This file proves that for each prime p, there exists a Sidon set mod (p²+p+1)
of size p+1. This is the final step connecting the algebraic Singer construction
(proved in SingerSidon.lean) to the combinatorial `IsSidonMod` property.

## Main result

`singer_sidon_set_of` : For each prime p, ∃ S : Finset ℤ with IsSidonMod (p²+p+1) S
and S.card = p+1.
-/

set_option maxHeartbeats 200000000

open Erdos30 Erdos30.Singer

namespace Erdos30.Singer

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

noncomputable section

/-! ## Representatives of projective lines in ker(Tr) -/

private abbrev V' := (Algebra.trace (ZMod p) (GaloisField p 3)).ker
private abbrev Q' := (GaloisField p 3)ˣ ⧸ baseUnitsSubgroup p

private def kerBasis' :=
  (Module.finBasis (ZMod p) ↥(V' p)).reindex
    ((Fin.castOrderIso (finrank_ker_trace p)).toEquiv)

private def repV (i : Option (ZMod p)) : V' p :=
  match i with
  | none => (kerBasis' p) ⟨0, by omega⟩
  | some c => (kerBasis' p) ⟨1, by omega⟩ + c • (kerBasis' p) ⟨0, by omega⟩

private def rep (i : Option (ZMod p)) : GaloisField p 3 := (repV p i).val

private lemma rep_mem (i : Option (ZMod p)) :
    rep p i ∈ (Algebra.trace (ZMod p) (GaloisField p 3)).ker := (repV p i).2

private lemma rep_ne_zero (i : Option (ZMod p)) : rep p i ≠ 0 := by
  intro h; have hV : repV p i = 0 := Subtype.ext h
  cases i with
  | none => exact (kerBasis' p).ne_zero ⟨0, by omega⟩ hV
  | some c =>
    have heq := congr_arg (kerBasis' p).repr hV
    simp only [repV, map_add, map_smul, (kerBasis' p).repr_self, map_zero] at heq
    have h1 := DFunLike.congr_fun heq ⟨1, by omega⟩
    simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      Finsupp.zero_apply,
      show (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) from rfl,
      show ((⟨0, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2)) = False from by simp [Fin.ext_iff],
      ite_true, ite_false, mul_zero, add_zero] at h1
    exact one_ne_zero h1

private lemma rep_proportional_imp_eq (i j : Option (ZMod p)) (α : ZMod p)
    (hprop : repV p j = α • repV p i) : i = j := by
  have heq := congr_arg (kerBasis' p).repr hprop
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some c =>
      simp only [repV, map_add, map_smul, (kerBasis' p).repr_self] at heq
      have h1 := DFunLike.congr_fun heq ⟨1, by omega⟩
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
        show (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) from rfl,
        show ((⟨0, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2)) = False from by simp [Fin.ext_iff],
        ite_true, ite_false, mul_zero, add_zero, mul_one] at h1
      exact absurd h1 one_ne_zero
  | some a =>
    cases j with
    | none =>
      simp only [repV, map_add, map_smul, (kerBasis' p).repr_self] at heq
      have h1 := DFunLike.congr_fun heq ⟨1, by omega⟩
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
        show (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) from rfl,
        show ((⟨0, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2)) = False from by simp [Fin.ext_iff],
        ite_true, ite_false, mul_zero, add_zero, mul_one] at h1
      exfalso; exact rep_ne_zero p none (show rep p none = 0 from by
        show (repV p none).val = 0
        have := hprop; rw [show α = 0 from h1.symm, zero_smul] at this
        exact congrArg Subtype.val this)
    | some b =>
      simp only [repV, map_add, map_smul, (kerBasis' p).repr_self] at heq
      have h1 := DFunLike.congr_fun heq ⟨1, by omega⟩
      have h0 := DFunLike.congr_fun heq ⟨0, by omega⟩
      simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
        show (⟨1, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2) from rfl,
        show ((⟨0, by omega⟩ : Fin 2) = (⟨1, by omega⟩ : Fin 2)) = False from by simp [Fin.ext_iff],
        show (⟨0, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2) from rfl,
        show ((⟨1, by omega⟩ : Fin 2) = (⟨0, by omega⟩ : Fin 2)) = False from by simp [Fin.ext_iff],
        ite_true, ite_false, mul_zero, add_zero, mul_one, zero_add] at h1 h0
      congr 1; rw [← h1, one_mul] at h0; exact h0.symm

private lemma singerMk_rep_injective :
    Function.Injective (fun i => singerMk p (rep p i) (rep_ne_zero p i)) := by
  intro i j hij
  rw [singerMk_eq_iff] at hij
  obtain ⟨α, hα⟩ := hij
  have hri := rep_ne_zero p i
  have hprop_field : rep p j = (algebraMap (ZMod p) (GaloisField p 3) α) * rep p i := by
    have h1 : (rep p i) * ((rep p i)⁻¹ * rep p j) = rep p j := by
      rw [← mul_assoc, mul_inv_cancel₀ hri, one_mul]
    rw [← h1, hα]; ring
  have hV : repV p j = α • repV p i := by
    apply Subtype.ext
    change rep p j = (α • repV p i).val
    rw [show (α • repV p i).val = α • (repV p i).val from rfl]
    rw [show α • (repV p i).val = (algebraMap (ZMod p) (GaloisField p 3) α) * (repV p i).val
      from Algebra.smul_def α _]
    exact hprop_field
  exact rep_proportional_imp_eq p i j α hV

/-! ## Cyclic group isomorphism -/

private lemma Q_card_eq (hp' : Nat.Prime p) : Nat.card (Q' p) = p ^ 2 + p + 1 := by
  rw [show Nat.card (Q' p) = (baseUnitsSubgroup p).index from
    (Subgroup.index_eq_card _).symm]
  exact baseUnitsSubgroup_index p hp'

private noncomputable def mulEquivQ (hp' : Nat.Prime p) :
    Multiplicative (ZMod (p ^ 2 + p + 1)) ≃* Q' p := by
  haveI : NeZero (p ^ 2 + p + 1) := ⟨by omega⟩
  haveI : IsCyclic (Q' p) := inferInstance
  let g := Classical.choose (IsCyclic.exists_generator (α := Q' p))
  have hg : ∀ x : Q' p, x ∈ Subgroup.zpowers g :=
    Classical.choose_spec (IsCyclic.exists_generator (α := Q' p))
  have htop : Subgroup.zpowers g = ⊤ := by ext x; exact ⟨fun _ => trivial, fun _ => hg x⟩
  have hord : orderOf g = p ^ 2 + p + 1 := by
    have h1 : Nat.card ↥(Subgroup.zpowers g) = orderOf g := Nat.card_zpowers g
    have h2 : Nat.card ↥(Subgroup.zpowers g) = Nat.card (Q' p) := by
      rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
    have := Q_card_eq p hp'; omega
  let φ : Multiplicative (ZMod (p ^ 2 + p + 1)) →* Q' p :=
    MonoidHom.mk' (fun k => g ^ (ZMod.val (Multiplicative.toAdd k))) (fun a b => by
      show g ^ ZMod.val (Multiplicative.toAdd a + Multiplicative.toAdd b) =
        g ^ ZMod.val (Multiplicative.toAdd a) * g ^ ZMod.val (Multiplicative.toAdd b)
      rw [← pow_add, pow_eq_pow_iff_modEq, hord]
      unfold Nat.ModEq; rw [ZMod.val_add]
      exact Nat.mod_mod_of_dvd _ (dvd_refl _))
  have hφ_apply : ∀ k, φ k = g ^ (ZMod.val (Multiplicative.toAdd k)) := fun _ => rfl
  exact MulEquiv.ofBijective φ ⟨by
    intro a b hab
    have hab' : g ^ (ZMod.val (Multiplicative.toAdd a)) =
        g ^ (ZMod.val (Multiplicative.toAdd b)) := by rw [← hφ_apply, ← hφ_apply]; exact hab
    have hinj := @pow_injOn_Iio_orderOf (Q' p) _ g
    have ha : ZMod.val (Multiplicative.toAdd a) ∈ Set.Iio (orderOf g) := by
      rw [Set.mem_Iio, hord]; exact ZMod.val_lt _
    have hb : ZMod.val (Multiplicative.toAdd b) ∈ Set.Iio (orderOf g) := by
      rw [Set.mem_Iio, hord]; exact ZMod.val_lt _
    cases a; cases b; exact congrArg _ (ZMod.val_injective _ (hinj ha hb hab')),
  by
    intro x
    obtain ⟨m, hm⟩ := (hg x : ∃ m : ℤ, g ^ m = x)
    have hpos : (0 : ℤ) < ((p ^ 2 + p + 1 : ℕ) : ℤ) := by positivity
    have hmod_nn : 0 ≤ m % ((p ^ 2 + p + 1 : ℕ) : ℤ) := Int.emod_nonneg _ (by linarith)
    have hmod_lt : (m % ((p ^ 2 + p + 1 : ℕ) : ℤ)).toNat < p ^ 2 + p + 1 := by
      have := Int.emod_lt_of_pos m hpos; omega
    let k : Multiplicative (ZMod (p ^ 2 + p + 1)) :=
      Multiplicative.ofAdd ((m % ((p ^ 2 + p + 1 : ℕ) : ℤ)).toNat : ZMod (p ^ 2 + p + 1))
    refine ⟨k, ?_⟩
    have hφk : φ k = g ^ (m % ((p ^ 2 + p + 1 : ℕ) : ℤ)).toNat := by
      rw [hφ_apply]; congr 1; exact ZMod.val_natCast_of_lt hmod_lt
    have key : g ^ ((m % ((p ^ 2 + p + 1 : ℕ) : ℤ)).toNat : ℤ) = g ^ m := by
      rw [zpow_eq_zpow_iff_modEq, hord]
      change ((m % ((p ^ 2 + p + 1 : ℕ) : ℤ)).toNat : ℤ) % ((p ^ 2 + p + 1 : ℕ) : ℤ) =
        m % ((p ^ 2 + p + 1 : ℕ) : ℤ)
      rw [Int.toNat_of_nonneg hmod_nn, Int.emod_emod_of_dvd _ dvd_rfl]
    calc φ k = g ^ (m % ((p ^ 2 + p + 1 : ℕ) : ℤ)).toNat := hφk
      _ = g ^ ((m % ((p ^ 2 + p + 1 : ℕ) : ℤ)).toNat : ℤ) := (zpow_natCast g _).symm
      _ = g ^ m := key
      _ = x := hm⟩

/-! ## Finset construction and IsSidonMod proof -/

/-- The Singer Sidon set: a Finset ℤ of size p+1 that is IsSidonMod (p²+p+1). -/
theorem singer_sidon_set_of (hp' : Nat.Prime p) :
    ∃ S : Finset ℤ, IsSidonMod (↑p * ↑p + ↑p + 1 : ℤ) S ∧ S.card = p + 1 := by
  haveI : NeZero (p ^ 2 + p + 1) := ⟨by omega⟩
  -- Cyclic isomorphism
  let φ := mulEquivQ p hp'
  -- Map each representative to its ZMod coordinate via φ⁻¹
  let f : Option (ZMod p) → ℤ := fun i =>
    ↑(ZMod.val (Multiplicative.toAdd (φ.symm (singerMk p (rep p i) (rep_ne_zero p i)))))
  let S : Finset ℤ := Finset.univ.image f
  refine ⟨S, ?_, ?_⟩
  · -- IsSidonMod
    intro a b c d ha hb hc hd hdvd
    -- a, b, c, d ∈ S = image of f
    rw [Finset.mem_image] at ha hb hc hd
    obtain ⟨ia, _, rfl⟩ := ha; obtain ⟨ib, _, rfl⟩ := hb
    obtain ⟨ic, _, rfl⟩ := hc; obtain ⟨id, _, rfl⟩ := hd
    -- Abbreviations for the four quotient elements
    set qa := singerMk p (rep p ia) (rep_ne_zero p ia)
    set qb := singerMk p (rep p ib) (rep_ne_zero p ib)
    set qc := singerMk p (rep p ic) (rep_ne_zero p ic)
    set qd := singerMk p (rep p id) (rep_ne_zero p id)
    -- Step 1: divisibility → ZMod equality
    have hzmod : Multiplicative.toAdd (φ.symm qa) + Multiplicative.toAdd (φ.symm qb) =
        Multiplicative.toAdd (φ.symm qc) + Multiplicative.toAdd (φ.symm qd) := by
      have h0 : ((((ZMod.val (Multiplicative.toAdd (φ.symm qa)) : ℤ) +
          (ZMod.val (Multiplicative.toAdd (φ.symm qb)) : ℤ)) -
          ((ZMod.val (Multiplicative.toAdd (φ.symm qc)) : ℤ) +
          (ZMod.val (Multiplicative.toAdd (φ.symm qd)) : ℤ)) : ℤ) : ZMod (p ^ 2 + p + 1)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        convert hdvd using 1
        push_cast; ring
      simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, ZMod.natCast_zmod_val] at h0
      exact sub_eq_zero.mp h0
    -- Step 2: ZMod equality → Multiplicative equality → Q' product equality
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
    -- Step 3: Products become singerMk of field products
    have hmul_l : qa * qb = singerMk p (rep p ia * rep p ib)
        (mul_ne_zero (rep_ne_zero p ia) (rep_ne_zero p ib)) := by
      show QuotientGroup.mk (Units.mk0 _ _) * QuotientGroup.mk (Units.mk0 _ _) =
        QuotientGroup.mk (Units.mk0 _ _)
      rw [← QuotientGroup.mk_mul]; congr 1; ext; rfl
    have hmul_r : qc * qd = singerMk p (rep p ic * rep p id)
        (mul_ne_zero (rep_ne_zero p ic) (rep_ne_zero p id)) := by
      show QuotientGroup.mk (Units.mk0 _ _) * QuotientGroup.mk (Units.mk0 _ _) =
        QuotientGroup.mk (Units.mk0 _ _)
      rw [← QuotientGroup.mk_mul]; congr 1; ext; rfl
    -- Step 4: singerMk equality → algebraMap factor via singerMk_eq_iff
    rw [hmul_l, hmul_r] at hQ
    rw [singerMk_eq_iff] at hQ
    obtain ⟨α, hα⟩ := hQ
    have hab_ne : rep p ia * rep p ib ≠ 0 := mul_ne_zero (rep_ne_zero p ia) (rep_ne_zero p ib)
    have hcd_ne : rep p ic * rep p id ≠ 0 := mul_ne_zero (rep_ne_zero p ic) (rep_ne_zero p id)
    have hα_ne : α ≠ 0 := by
      intro h0; rw [h0, map_zero] at hα
      exact mul_ne_zero (inv_ne_zero hab_ne) hcd_ne hα.symm
    have hcd_eq : rep p ic * rep p id =
        (algebraMap (ZMod p) (GaloisField p 3)) α * (rep p ia * rep p ib) := by
      calc rep p ic * rep p id
          = (rep p ia * rep p ib) * ((rep p ia * rep p ib)⁻¹ * (rep p ic * rep p id)) := by
            rw [← mul_assoc, mul_inv_cancel₀ hab_ne, one_mul]
        _ = (rep p ia * rep p ib) * (algebraMap (ZMod p) (GaloisField p 3)) α := by rw [hα]
        _ = (algebraMap (ZMod p) (GaloisField p 3)) α * (rep p ia * rep p ib) := mul_comm _ _
    -- Step 5: Apply singer_quotient_sidon
    have hsq := singer_quotient_sidon p (rep p ic) (rep p id) (rep p ia) (rep p ib)
      (rep_mem p ic) (rep_mem p id) (rep_mem p ia) (rep_mem p ib)
      (rep_ne_zero p ic) (rep_ne_zero p id) (rep_ne_zero p ia) (rep_ne_zero p ib)
      α hα_ne hcd_eq
    -- Step 6: From singerMk equality to index equality via injectivity
    cases hsq with
    | inl h =>
      left; constructor
      · exact congrArg f (singerMk_rep_injective p h.1.symm)
      · exact congrArg f (singerMk_rep_injective p h.2.symm)
    | inr h =>
      right; constructor
      · exact congrArg f (singerMk_rep_injective p h.2.symm)
      · exact congrArg f (singerMk_rep_injective p h.1.symm)
  · -- card S = p + 1
    rw [Finset.card_image_of_injective _ (by
      intro i j hij
      -- f(i) = f(j) means val(toAdd(φ⁻¹(singerMk(rep i)))) = val(toAdd(φ⁻¹(singerMk(rep j))))
      -- nat→int cast is injective, val is injective, toAdd is bijective, φ⁻¹ is bijective
      -- So singerMk(rep i) = singerMk(rep j), hence i = j by singerMk_rep_injective
      have h1 : (ZMod.val (Multiplicative.toAdd (φ.symm (singerMk p (rep p i) (rep_ne_zero p i)))) : ℤ) =
        ↑(ZMod.val (Multiplicative.toAdd (φ.symm (singerMk p (rep p j) (rep_ne_zero p j))))) := hij
      have h2 := Nat.cast_injective h1
      have h3 := ZMod.val_injective _ h2
      -- h3 : toAdd(φ⁻¹(singerMk(rep i))) = toAdd(φ⁻¹(singerMk(rep j)))
      have h4 : φ.symm (singerMk p (rep p i) (rep_ne_zero p i)) =
          φ.symm (singerMk p (rep p j) (rep_ne_zero p j)) :=
        Multiplicative.toAdd.injective h3
      have h5 := φ.symm.injective h4
      exact singerMk_rep_injective p h5)]
    simp [Finset.card_univ, Fintype.card_option, ZMod.card]

end
end Erdos30.Singer

namespace Erdos30.Singer

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-- Singer's theorem: for each prime p, there exists a Sidon set mod (p²+p+1) of size p+1. -/
theorem singer_sidon_set (hp' : Nat.Prime p) :
    ∃ S : Finset ℤ, IsSidonMod (↑p * ↑p + ↑p + 1 : ℤ) S ∧ S.card = p + 1 :=
  singer_sidon_set_of p hp'

end Erdos30.Singer
-- END upstream SingerTheorem.lean
