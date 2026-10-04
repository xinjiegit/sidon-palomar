/-
SPDX-License-Identifier: GPL-3.0-only
Variable-density circular cells for the general affine compression lemma.
-/
module

public import CellGeometry

@[expose] public section

open MeasureTheory Metric
namespace SidonResearch
variable {m : ℕ} [NeZero m]

/-- A cell of length `δ/m`, centered at the residue divided by `m`. -/
def deltaCell (δ : ℝ) (m : ℕ) [NeZero m] (j : ZMod m) : Set UnitAddCircle :=
  Metric.ball (ZMod.toAddCircle j) (δ / (2 * (m : ℝ)))

theorem measurableSet_deltaCell (δ : ℝ) (j : ZMod m) : MeasurableSet (deltaCell δ m j) :=
  measurableSet_ball

theorem deltaCells_disjoint {δ : ℝ} (hδ : δ ≤ 1/2) {i j : ZMod m} (hij : i ≠ j) :
    Disjoint (deltaCell δ m i) (deltaCell δ m j) := by
  apply Metric.ball_disjoint_ball
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have heq : δ / (2 * (m : ℝ)) + δ / (2 * (m : ℝ)) = δ / (m : ℝ) := by ring
  rw [heq]
  exact le_trans ((div_le_div_iff_of_pos_right hm).mpr (by linarith)) (centers_separated hij)

theorem volume_deltaCell {δ : ℝ} (hδ : δ ≤ 1/2) (j : ZMod m) :
    volume (deltaCell δ m j) = ENNReal.ofReal (δ / (m : ℝ)) := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.pos m)
  have hm0 : (0 : ℝ) < m := by linarith
  have hcap : 2 * (δ / (2 * (m : ℝ))) ≤ 1 := by
    have heq : 2 * (δ / (2 * (m : ℝ))) = δ / (m : ℝ) := by ring
    rw [heq]
    apply (div_le_iff₀ hm0).mpr
    nlinarith
  rw [deltaCell, ← measure_congr (AddCircle.closedBall_ae_eq_ball (x := ZMod.toAddCircle j)),
    AddCircle.volume_closedBall, min_eq_right hcap]
  congr 1
  ring

theorem volume_real_deltaCell {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/2) (j : ZMod m) :
    volume.real (deltaCell δ m j) = δ / (m : ℝ) := by
  rw [MeasureTheory.measureReal_def, volume_deltaCell hδ, ENNReal.toReal_ofReal]
  positivity

/-- Four points in cells obey every existing additive relation at the level of labels.
The statement permits repeated points and repeated labels. -/
theorem deltaCell_labels_freiman {δ : ℝ} (hδ : δ ≤ 1/2) {a b c d : UnitAddCircle} {i j k l : ZMod m}
    (ha : a ∈ deltaCell δ m i) (hb : b ∈ deltaCell δ m j)
    (hc : c ∈ deltaCell δ m k) (hd : d ∈ deltaCell δ m l)
    (hadd : a+b=c+d) : i+j=k+l := by
  have ha' : ‖ZMod.toAddCircle i - a‖ < δ / (2 * (m : ℝ)) := by
    simpa [deltaCell, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using ha
  have hb' : ‖ZMod.toAddCircle j - b‖ < δ / (2 * (m : ℝ)) := by
    simpa [deltaCell, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hb
  have hc' : ‖ZMod.toAddCircle k - c‖ < δ / (2 * (m : ℝ)) := by
    simpa [deltaCell, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hc
  have hd' : ‖ZMod.toAddCircle l - d‖ < δ / (2 * (m : ℝ)) := by
    simpa [deltaCell, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hd
  have heq : ZMod.toAddCircle (i+j-k-l) =
      (ZMod.toAddCircle i-a)+(ZMod.toAddCircle j-b)-
        (ZMod.toAddCircle k-c)-(ZMod.toAddCircle l-d) := by
    simp only [map_sub, map_add]
    apply sub_eq_zero.mp
    have heq : (ZMod.toAddCircle i + ZMod.toAddCircle j - ZMod.toAddCircle k -
      ZMod.toAddCircle l) - ((ZMod.toAddCircle i-a)+(ZMod.toAddCircle j-b)-
        (ZMod.toAddCircle k-c)-(ZMod.toAddCircle l-d)) = (a+b)-(c+d) := by abel
    rw [heq, hadd, sub_self]
  have hnorm : ‖ZMod.toAddCircle (i+j-k-l)‖ < 1 / (m : ℝ) := by
    rw [heq]
    have h1 := norm_sub_le ((ZMod.toAddCircle i-a)+(ZMod.toAddCircle j-b)-
      (ZMod.toAddCircle k-c)) (ZMod.toAddCircle l-d)
    have h2 := norm_sub_le ((ZMod.toAddCircle i-a)+(ZMod.toAddCircle j-b))
      (ZMod.toAddCircle k-c)
    have h3 := norm_add_le (ZMod.toAddCircle i-a) (ZMod.toAddCircle j-b)
    have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
    have heq' : 4 * (δ / (2 * (m : ℝ))) = (2*δ) / (m : ℝ) := by ring
    have hδ' : (2*δ)/(m : ℝ) ≤ 1/(m : ℝ) :=
      (div_le_div_iff_of_pos_right hm).mpr (by linarith)
    linarith
  have hz := center_eq_zero_of_norm_lt (i+j-k-l) hnorm
  rw [sub_sub] at hz
  exact sub_eq_zero.mp hz


end SidonResearch
