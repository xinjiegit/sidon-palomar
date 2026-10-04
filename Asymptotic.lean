module

public import Basic
public import PrimeNumberTheoremAnd.Consequences

@[expose] public section

/-!
# Prime selection and the optimized Sidon asymptotic

External number-theoretic input: `chebyshev_asymptotic`, from
`PrimeNumberTheoremAnd.Consequences`, vendored from revision
`c39a751132c88b6e8080b74c74023fd95b3d8be0` of
https://github.com/AlexKontorovich/PrimeNumberTheoremAnd.
The selected proof closure is ported to the toolchain pinned in `lean-toolchain`;
see `vendor/PNT/PROVENANCE.txt` for source selection and licensing.
No extra number-theoretic axiom is declared.

We derive prime density rather than postulating it, select the least prime
above `(sqrt 3 / 2) * sqrt n`, and prove the exact normalized finite expression
converges to `2 / (3 * sqrt 3)`. The final theorem is an epsilon formulation
uniform over every integer set whose cardinality exceeds a common threshold.
-/

open Filter Asymptotics

namespace SidonResearch

noncomputable section

/-- A prime in every sufficiently large fixed multiplicative interval, from the PNT. -/
theorem eventually_exists_prime_between {c : ℝ} (hc : 1 < c) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ c * x := by
  have hθ : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1) := by
    exact (isEquivalent_iff_tendsto_one (eventually_ne_atTop 0)).mp chebyshev_asymptotic
  have hc0 : 0 < c := lt_trans zero_lt_one hc
  have hcθ : Tendsto (fun x : ℝ => Chebyshev.theta (c * x) / x) atTop (nhds c) := by
    have h := (hθ.comp (tendsto_id.const_mul_atTop hc0)).mul_const c
    simp only [one_mul] at h
    apply h.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
    dsimp
    field_simp
  have hd : Tendsto (fun x : ℝ => Chebyshev.theta (c*x) / x -
      Chebyshev.theta x / x) atTop (nhds (c-1)) := hcθ.sub hθ
  filter_upwards [hd.eventually_const_lt (by linarith : 0 < c-1),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hlt : Chebyshev.theta x < Chebyshev.theta (c*x) := by
    have := (div_lt_div_iff_of_pos_right hx0).mp (show Chebyshev.theta x / x <
      Chebyshev.theta (c*x) / x by linarith)
    exact this
  by_contra h
  push Not at h
  have heq : (⌊x⌋₊).primesLE = (⌊c*x⌋₊).primesLE := by
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · rintro ⟨hp, hpP⟩
      refine ⟨?_, hpP⟩
      apply (Nat.le_floor_iff (by positivity : 0 ≤ c*x)).mpr
      exact le_trans ((Nat.le_floor_iff hx0.le).mp hp) (by nlinarith)
    · rintro ⟨hp, hpP⟩
      refine ⟨(Nat.le_floor_iff hx0.le).mpr ?_, hpP⟩
      by_contra hpx
      exact (h p hpP (lt_of_not_ge hpx)).not_ge ((Nat.le_floor_iff (by positivity)).mp hp)
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, ← heq] at hlt
  exact lt_irrefl _ hlt

/-- The least prime not smaller than the real number `x`. -/
noncomputable def nextPrimeReal (x : ℝ) : ℕ :=
  Nat.find (Nat.exists_infinite_primes ⌈x⌉₊)

theorem nextPrimeReal_prime (x : ℝ) : (nextPrimeReal x).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes ⌈x⌉₊)).2

theorem le_nextPrimeReal (x : ℝ) : x ≤ (nextPrimeReal x : ℝ) := by
  exact (Nat.ceil_le).mp (Nat.find_spec (Nat.exists_infinite_primes ⌈x⌉₊)).1

theorem nextPrimeReal_le {x : ℝ} {p : ℕ} (hp : p.Prime) (hx : x ≤ (p : ℝ)) :
    nextPrimeReal x ≤ p :=
  Nat.find_min' _ ⟨Nat.ceil_le.mpr hx, hp⟩

/-- Consecutive prime gaps are `o(x)`, in the precise form needed below. -/
theorem nextPrimeReal_div_tendsto :
    Tendsto (fun x : ℝ => (nextPrimeReal x : ℝ) / x) atTop (nhds 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have h : 1 ≤ (nextPrimeReal x : ℝ) / x :=
      (le_div_iff₀ hx).mpr (by simpa using le_nextPrimeReal x)
    exact lt_of_lt_of_le ha h
  · intro a ha
    obtain ⟨c, hc1, hca⟩ := exists_between ha
    filter_upwards [eventually_exists_prime_between hc1,
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    obtain ⟨p, hp, hxp, hpc⟩ := hx
    have hpmin : (nextPrimeReal x : ℝ) ≤ p := by
      exact_mod_cast nextPrimeReal_le hp hxp.le
    exact lt_of_le_of_lt ((div_le_iff₀ hx0).mpr (hpmin.trans hpc)) hca

/-- The prime parameter optimizes the finite compression bound at `q²/n → 3/4`. -/
noncomputable def optimizingPrime (n : ℕ) : ℕ :=
  nextPrimeReal (Real.sqrt 3 / 2 * Real.sqrt n)

theorem optimizingPrime_prime (n : ℕ) : (optimizingPrime n).Prime :=
  nextPrimeReal_prime _

theorem optimizingPrime_ratio_tendsto :
    Tendsto (fun n : ℕ => (optimizingPrime n : ℝ) / Real.sqrt n)
      atTop (nhds (Real.sqrt 3 / 2)) := by
  have ha : 0 < Real.sqrt 3 / 2 := by positivity
  have hx : Tendsto (fun n : ℕ => Real.sqrt 3 / 2 * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop ha
  have h := (nextPrimeReal_div_tendsto.comp hx).mul_const (Real.sqrt 3 / 2)
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  dsimp [optimizingPrime]
  field_simp

/-- The real-valued lower bound supplied by finite compression and Singer averaging. -/
def finiteSidonBound (n q : ℕ) : ℝ :=
  ((q : ℝ) + 1) / ((q : ℝ)^2 + q + 1) *
    ((n : ℝ)/2 - (n : ℝ)*((n : ℝ)-1)/(8*((q : ℝ)^2+q+1)))

/-- A rational expression in the normalized prime and inverse square-root scale. -/
def normalizedSidonBound (r t : ℝ) : ℝ :=
  (r+t)/(r^2+r*t+t^2) * (1/2 - (1-t^2)/(8*(r^2+r*t+t^2)))

theorem normalizedSidonBound_eq (n q : ℕ) (hn : 0 < n) :
    finiteSidonBound n q / Real.sqrt n =
      normalizedSidonBound ((q : ℝ)/Real.sqrt n) (1/Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := by positivity
  have hsq := Real.sq_sqrt hn0.le
  have hq : (0 : ℝ) ≤ q := by positivity
  unfold finiteSidonBound normalizedSidonBound
  rw [← hsq, Real.sqrt_sq hs.le]
  field_simp

theorem normalizedSidonBound_limit :
    Tendsto (fun n : ℕ => normalizedSidonBound
      ((optimizingPrime n : ℝ)/Real.sqrt n) (1/Real.sqrt n))
      atTop (nhds (2/(3*Real.sqrt 3))) := by
  have ht : Tendsto (fun n : ℕ => (1 : ℝ)/Real.sqrt n) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hr := optimizingPrime_ratio_tendsto
  have hm := ((hr.pow 2).add (hr.mul ht)).add (ht.pow 2)
  have hm0 : (Real.sqrt 3 / 2)^2 + (Real.sqrt 3 / 2)*0 + 0^2 ≠ (0 : ℝ) := by
    positivity
  have h := ((hr.add ht).div hm hm0).mul
    ((tendsto_const_nhds (x := (1/2 : ℝ))).sub
      (((tendsto_const_nhds (x := (1 : ℝ))).sub (ht.pow 2)).div (hm.const_mul 8) (by positivity)))
  have heq : normalizedSidonBound (Real.sqrt 3 / 2) 0 = 2/(3*Real.sqrt 3) := by
    unfold normalizedSidonBound
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hp : Real.sqrt 3 ≠ 0 := by positivity
    field_simp
    nlinarith
  exact heq ▸ h

/-- The finite lower bounds converge to the claimed universal constant. -/
theorem finiteSidonBound_limit :
    Tendsto (fun n : ℕ => finiteSidonBound n (optimizingPrime n) / Real.sqrt n)
      atTop (nhds (2/(3*Real.sqrt 3))) := by
  apply normalizedSidonBound_limit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact (normalizedSidonBound_eq n _ hn).symm

/-- An epsilon-form bound uniform over all sufficiently large cardinalities. -/
theorem finiteSidonBound_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (2/(3*Real.sqrt 3)-ε)*Real.sqrt n ≤ finiteSidonBound n (optimizingPrime n) := by
  have h := finiteSidonBound_limit.eventually_const_lt
    (by linarith : 2/(3*Real.sqrt 3)-ε < 2/(3*Real.sqrt 3))
  filter_upwards [h, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hs : 0 < Real.sqrt (n : ℝ) := by positivity
  exact ((lt_div_iff₀ hs).mp hn).le

/-- Complete asymptotic passage. Its single combinatorial hypothesis is discharged
by the finite compression/Singer theorem in the final composition file.
There is no prime-density hypothesis: it was proved above from a checked PNT. -/
theorem asymptotic_of_finite_bound
    (hfinite : ∀ (A : Finset ℤ) (q : ℕ), q.Prime →
      ∃ B ⊆ A, IsSidon B ∧ finiteSidonBound A.card q ≤ (B.card : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ A : Finset ℤ, N ≤ A.card →
      ∃ B ⊆ A, IsSidon B ∧
        (2/(3*Real.sqrt 3)-ε)*Real.sqrt A.card ≤ (B.card : ℝ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (finiteSidonBound_eventually ε hε)
  refine ⟨N, fun A hA => ?_⟩
  obtain ⟨B, hBA, hB, hcard⟩ :=
    hfinite A (optimizingPrime A.card) (optimizingPrime_prime A.card)
  exact ⟨B, hBA, hB, le_trans (hN A.card hA) hcard⟩

end

end SidonResearch

#print axioms SidonResearch.eventually_exists_prime_between
#print axioms SidonResearch.finiteSidonBound_limit
#print axioms SidonResearch.asymptotic_of_finite_bound
