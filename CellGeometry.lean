/-
SPDX-License-Identifier: GPL-3.0-only
Half-density cells on the unit additive circle and their Freiman property.
-/
module

public import Mathlib

@[expose] public section

open MeasureTheory Metric

namespace SidonResearch

variable {m : ℕ} [NeZero m]

/-- An open circular interval of length `1/(2m)` about the residue `j/m`. -/
def cell (m : ℕ) [NeZero m] (j : ZMod m) : Set UnitAddCircle :=
  Metric.ball (ZMod.toAddCircle j) (1 / (4 * (m : ℝ)))

theorem measurableSet_cell (j : ZMod m) : MeasurableSet (cell m j) :=
  measurableSet_ball

/-- Distinct grid points have circular distance at least `1/m`. -/
theorem center_eq_zero_of_norm_lt (j : ZMod m)
    (hj : ‖ZMod.toAddCircle j‖ < 1 / (m : ℝ)) : j = 0 := by
  by_contra hne
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have hv : 0 < j.val := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hne ((ZMod.val_eq_zero j).mp h)
  have hmin : 1 ≤ min (j.val % m) (m - j.val % m) := by
    rw [Nat.mod_eq_of_lt (ZMod.val_lt j)]
    have := ZMod.val_lt j
    omega
  have hnorm : ‖ZMod.toAddCircle j‖ =
      (min (j.val % m) (m - j.val % m) : ℕ) / (m : ℝ) := by
    rw [ZMod.toAddCircle_apply]
    simpa only [mul_one, one_mul] using
      (AddCircle.norm_div_natCast (p := (1 : ℝ)) (m := j.val) (n := m))
  rw [hnorm] at hj
  have hcast : (1 : ℝ) ≤ (min (j.val % m) (m - j.val % m) : ℕ) := by
    exact_mod_cast hmin
  exact (not_lt_of_ge ((div_le_div_iff_of_pos_right hm).mpr hcast)) hj

theorem centers_separated {i j : ZMod m} (hij : i ≠ j) :
    1 / (m : ℝ) ≤ dist (ZMod.toAddCircle i) (ZMod.toAddCircle j) := by
  by_contra h
  have hlt : ‖ZMod.toAddCircle (i-j)‖ < 1 / (m : ℝ) := by
    simpa [map_sub, dist_eq_norm] using lt_of_not_ge h
  exact hij (sub_eq_zero.mp (center_eq_zero_of_norm_lt (i-j) hlt))

theorem cells_disjoint {i j : ZMod m} (hij : i ≠ j) : Disjoint (cell m i) (cell m j) := by
  apply Metric.ball_disjoint_ball
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have h := centers_separated hij
  have heq : 1 / (4 * (m : ℝ)) + 1 / (4 * (m : ℝ)) = 1 / (2 * (m : ℝ)) := by ring
  rw [heq]
  exact le_trans ((div_le_div_iff₀ (by positivity) hm).mpr (by nlinarith)) h

theorem volume_cell (j : ZMod m) :
    volume (cell m j) = ENNReal.ofReal (1 / (2 * (m : ℝ))) := by
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.pos m)
  have hm0 : (0 : ℝ) < m := by linarith
  have hcap : 2 * (1 / (4 * (m : ℝ))) ≤ 1 := by
    have heq : 2 * (1 / (4 * (m : ℝ))) = 1 / (2 * (m : ℝ)) := by ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*m)).mpr
    nlinarith
  rw [cell, ← measure_congr (AddCircle.closedBall_ae_eq_ball (x := ZMod.toAddCircle j)),
    AddCircle.volume_closedBall, min_eq_right hcap]
  congr 1
  ring

/-- The real-valued cell measure used in expectation calculations. -/
theorem volume_real_cell (j : ZMod m) :
    volume.real (cell m j) = 1 / (2 * (m : ℝ)) := by
  rw [MeasureTheory.measureReal_def, volume_cell, ENNReal.toReal_ofReal]
  positivity

/-- Four points in cells obey every existing additive relation at the level of labels.
The statement permits repeated points and repeated labels. -/
theorem cell_labels_freiman {a b c d : UnitAddCircle} {i j k l : ZMod m}
    (ha : a ∈ cell m i) (hb : b ∈ cell m j)
    (hc : c ∈ cell m k) (hd : d ∈ cell m l)
    (hadd : a+b=c+d) : i+j=k+l := by
  have ha' : ‖ZMod.toAddCircle i - a‖ < 1 / (4 * (m : ℝ)) := by
    simpa [cell, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using ha
  have hb' : ‖ZMod.toAddCircle j - b‖ < 1 / (4 * (m : ℝ)) := by
    simpa [cell, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hb
  have hc' : ‖ZMod.toAddCircle k - c‖ < 1 / (4 * (m : ℝ)) := by
    simpa [cell, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hc
  have hd' : ‖ZMod.toAddCircle l - d‖ < 1 / (4 * (m : ℝ)) := by
    simpa [cell, Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hd
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
    have heq' : 4 * (1 / (4 * (m : ℝ))) = 1 / (m : ℝ) := by ring
    linarith
  have hz := center_eq_zero_of_norm_lt (i+j-k-l) hnorm
  rw [sub_sub] at hz
  exact sub_eq_zero.mp hz

end SidonResearch
