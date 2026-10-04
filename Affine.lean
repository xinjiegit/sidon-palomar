module

public import Mathlib

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set
open scoped MeasureTheory

namespace SidonResearch

abbrev Circle := UnitAddCircle
abbrev Sample := Circle × Circle

noncomputable def sampleMeasure : Measure Sample :=
  (volume : Measure Circle).prod volume

instance : IsAddHaarMeasure sampleMeasure := by unfold sampleMeasure; infer_instance
instance : IsProbabilityMeasure sampleMeasure := ⟨by simp [sampleMeasure, Measure.prod_apply]⟩

noncomputable def affine (a : ℤ) : Sample →+ Circle where
  toFun ω := a • ω.1 + ω.2
  map_zero' := by simp
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, smul_add]; abel

theorem affine_measurePreserving (a : ℤ) :
    MeasurePreserving (affine a) sampleMeasure volume := by
  apply AddMonoidHom.measurePreserving (f := affine a)
  · change Continuous (fun ω : Sample => a • ω.1 + ω.2)
    fun_prop
  · intro x
    exact ⟨(0,x), by simp [affine]⟩
  · simp [sampleMeasure, Measure.prod_apply]

noncomputable def affinePair (a b : ℤ) : Sample →+ Sample :=
  (affine a).prod (affine b)

/-- The common affine shift cancels in every balanced two-sum relation. -/
theorem affine_preserves {a b c d : ℤ} (h : a+b=c+d) (ω : Sample) :
    affine a ω + affine b ω = affine c ω + affine d ω := by
  change (a • ω.1 + ω.2) + (b • ω.1 + ω.2) =
    (c • ω.1 + ω.2) + (d • ω.1 + ω.2)
  calc
    _ = (a+b) • ω.1 + (ω.2+ω.2) := by rw [add_zsmul]; abel
    _ = (c+d) • ω.1 + (ω.2+ω.2) := by rw [h]
    _ = _ := by rw [add_zsmul]; abel

theorem affinePair_measurePreserving {a b : ℤ} (hab : a ≠ b) :
    MeasurePreserving (affinePair a b) sampleMeasure sampleMeasure := by
  apply AddMonoidHom.measurePreserving (f := affinePair a b)
  · change Continuous (fun ω : Sample => (a • ω.1 + ω.2, b • ω.1 + ω.2))
    fun_prop
  · intro x
    obtain ⟨θ, hθ⟩ := DivisibleBy.surjective_smul Circle ℤ (sub_ne_zero.mpr hab) (x.1 - x.2)
    refine ⟨(θ, x.1 - a • θ), ?_⟩
    change (a • θ + (x.1 - a • θ), b • θ + (x.1 - a • θ)) = x
    apply Prod.ext
    · simp
    · simp only [sub_smul] at hθ
      change b • θ + (x.1 - a • θ) = x.2
      calc
        b • θ + (x.1 - a • θ) = x.1 - (a • θ - b • θ) := by abel
        _ = x.2 := by rw [hθ]; abel
  · rfl

#print axioms affine_measurePreserving
#print axioms affinePair_measurePreserving

end SidonResearch
