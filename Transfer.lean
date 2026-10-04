module

public import Basic

@[expose] public section

/-! Diameter-independent transfer to integers for every finite subset of a
 torsion-free abelian group, hence in particular for every finite subset of ℝ^d. -/

namespace SidonResearch

open scoped BigOperators

/-- Finitely many distinct integer polynomials remain distinct at some integer. -/
theorem exists_eval_injOn (A : Finset (Polynomial ℤ)) :
    ∃ z : ℤ, Set.InjOn (Polynomial.eval z) (↑A : Set (Polynomial ℤ)) := by
  classical
  let P : Polynomial ℤ := ∏ uv ∈ A.offDiag, (uv.1 - uv.2)
  have hP : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro uv huv
    exact sub_ne_zero.mpr (Finset.mem_offDiag.mp huv).2.2
  have hz : ∃ z : ℤ, Polynomial.eval z P ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (Polynomial.zero_of_eval_zero P h)
  obtain ⟨z, hz⟩ := hz
  refine ⟨z, ?_⟩
  intro u hu v hv huv
  by_contra hne
  have hmem : (u,v) ∈ A.offDiag := Finset.mem_offDiag.mpr ⟨hu, hv, hne⟩
  have hprod : (∏ uv ∈ A.offDiag,
      (Polynomial.eval z (uv.1-uv.2))) ≠ 0 := by
    simpa only [P, Polynomial.eval_prod] using hz
  have := Finset.prod_ne_zero_iff.mp hprod (u,v) hmem
  apply this
  simpa only [Polynomial.eval_sub, sub_eq_zero] using huv

/-- Every finitely generated torsion-free abelian group embeds additively
in the additive group of integer polynomials. -/
theorem exists_polynomial_embedding (M : Type*) [AddCommGroup M]
    [IsAddTorsionFree M] [Module.Finite ℤ M] :
    ∃ f : M →+ Polynomial ℤ, Function.Injective f := by
  classical
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := M)
  let e : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let g : (ℕ →₀ ℤ) ≃+ Polynomial ℤ :=
    AddMonoidAlgebra.coeffAddEquiv.symm.trans (Polynomial.toFinsuppIso ℤ).symm.toAddEquiv
  let f : M →+ Polynomial ℤ :=
    { toFun := fun x => g (Finsupp.embDomain e (b.repr x))
      map_zero' := by simp
      map_add' := by intro x y; simp [Finsupp.embDomain_add] }
  refine ⟨f, ?_⟩
  intro x y h
  apply b.repr.injective
  apply Finsupp.embDomain_injective e
  exact g.injective h

/-- A finite subset of any torsion-free abelian group admits an injective
forward Freiman 2-homomorphism into the integers. No size or diameter assumption
is imposed on the ambient group or on the integer image. -/
theorem exists_freiman2_int {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]
    (A : Finset M) :
    ∃ f : M → ℤ, Freiman2On A f ∧ Set.InjOn f (↑A : Set M) := by
  classical
  let S : Submodule ℤ M := Submodule.span ℤ (↑A : Set M)
  letI : Module.Finite ℤ S := Module.Finite.span_of_finite ℤ A.finite_toSet
  letI : IsAddTorsionFree S :=
    Function.Injective.isAddTorsionFree S.subtype.toAddMonoidHom Subtype.val_injective
  obtain ⟨g, hg⟩ := exists_polynomial_embedding S
  let liftA : A → S := fun a => ⟨a, Submodule.subset_span a.property⟩
  let D : Finset (Polynomial ℤ) := Finset.univ.image (fun a : A => g (liftA a))
  obtain ⟨z, hz⟩ := exists_eval_injOn D
  let h : S →+ ℤ := (Polynomial.evalRingHom z).toAddMonoidHom.comp g
  let f : M → ℤ := fun a => if ha : a ∈ S then h ⟨a,ha⟩ else 0
  have hf (a : M) (ha : a ∈ A) : f a = h ⟨a, Submodule.subset_span ha⟩ := by
    simp only [f, dif_pos (show a ∈ S from Submodule.subset_span ha)]
  refine ⟨f, ?_, ?_⟩
  · intro a ha b hb c hc d hd heq
    rw [hf a ha, hf b hb, hf c hc, hf d hd, ← map_add, ← map_add]
    congr 1
    exact Subtype.ext heq
  · intro a ha b hb hab
    rw [hf a ha, hf b hb] at hab
    have hea : g ⟨a, Submodule.subset_span ha⟩ ∈ D :=
      Finset.mem_image.mpr ⟨⟨a,ha⟩, Finset.mem_univ _, rfl⟩
    have heb : g ⟨b, Submodule.subset_span hb⟩ ∈ D :=
      Finset.mem_image.mpr ⟨⟨b,hb⟩, Finset.mem_univ _, rfl⟩
    have he := hg (hz hea heb hab)
    exact congrArg Subtype.val he

/-- Pull a Sidon subset of the integer model back without any cardinality loss. -/
theorem sidon_subset_of_image {M : Type*} [AddCommGroup M]
    (A : Finset M) (f : M → ℤ) (hf : Freiman2On A f)
    (hinj : Set.InjOn f (↑A : Set M)) (D : Finset ℤ)
    (hD : D ⊆ A.image f) (hsidon : IsSidon D) :
    ∃ B ⊆ A, IsSidon B ∧ B.card = D.card := by
  classical
  let B := A.filter (fun a => f a ∈ D)
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hmap : ∀ b ∈ B, f b ∈ D := fun b hb => (Finset.mem_filter.mp hb).2
  have himage : B.image f = D := by
    ext z
    constructor
    · intro hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      exact hmap b hb
    · intro hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (hD hz)
      exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hb,hz⟩, rfl⟩
  refine ⟨B, hBA, hsidon.pullback (hf.mono hBA) (hinj.mono hBA) hmap, ?_⟩
  rw [← himage, Finset.card_image_of_injOn (hinj.mono hBA)]

/-- Every universal integer lower bound transfers verbatim to any torsion-free
abelian group. Both the threshold and the cardinality bound are unchanged. -/
theorem integer_bound_transfer {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]
    (L : ℕ → ℝ) (N : ℕ)
    (h : ∀ A : Finset ℤ, N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧ L A.card ≤ (B.card : ℝ)) :
    ∀ A : Finset M, N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧ L A.card ≤ (B.card : ℝ) := by
  classical
  intro A hA
  obtain ⟨f, hf, hinj⟩ := exists_freiman2_int A
  have hcard : (A.image f).card = A.card := Finset.card_image_of_injOn hinj
  obtain ⟨D, hD, hsidon, hsize⟩ := h (A.image f) (by simpa only [hcard] using hA)
  obtain ⟨B, hBA, hB, hBD⟩ := sidon_subset_of_image A f hf hinj D hD hsidon
  exact ⟨B, hBA, hB, by simpa only [hBD, hcard] using hsize⟩

/-- In particular, the same universal bound holds in every real coordinate space. -/
theorem real_space_bound_transfer (L : ℕ → ℝ) (N : ℕ)
    (h : ∀ A : Finset ℤ, N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧ L A.card ≤ (B.card : ℝ))
    (d : ℕ) :
    ∀ A : Finset (Fin d → ℝ), N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧ L A.card ≤ (B.card : ℝ) := by
  letI : IsAddTorsionFree (Fin d → ℝ) :=
    IsAddTorsionFree.of_isTorsionFree ℝ (Fin d → ℝ)
  exact integer_bound_transfer L N h

end SidonResearch

#print axioms SidonResearch.exists_freiman2_int
#print axioms SidonResearch.integer_bound_transfer
#print axioms SidonResearch.real_space_bound_transfer
