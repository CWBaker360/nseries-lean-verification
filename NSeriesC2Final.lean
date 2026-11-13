import Mathlib

namespace BakerNSeries

theorem sine_interval_derivatives
    (x : Real) (hx : Ne x 0) (n : Nat) :
    iteratedDerivWithin n Real.sin (Set.uIcc 0 x) 0 =
      iteratedDeriv n Real.sin 0 := by
  apply iteratedDerivWithin_eq_iteratedDeriv
  · exact uniqueDiffOn_uIcc hx.symm
  · exact Real.contDiff_sin.contDiffAt
  · exact Set.left_mem_uIcc

theorem sine_interval_taylor_eq_univ
    (x : Real) (hx : Ne x 0) (n : Nat) :
    taylorWithinEval Real.sin n (Set.uIcc 0 x) 0 x =
      taylorWithinEval Real.sin n Set.univ 0 x := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [taylorWithinEval_succ,
          taylorWithinEval_succ,
          ih,
          sine_interval_derivatives x hx (n + 1),
          iteratedDerivWithin_univ]


-- Lagrange remainder for the eighth-degree sine polynomial.
theorem sine_lagrange_remainder
    (x : Real) (hx : Ne x 0) :
    Exists fun xi : Real =>
      xi ∈ Set.uIoo 0 x ∧
      Real.sin x -
        taylorWithinEval Real.sin 8 (Set.uIcc 0 x) 0 x =
        iteratedDeriv 9 Real.sin xi * x^9 /
          (Nat.factorial 9 : Real) := by
  obtain ⟨xi, hxi, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sin) (x₀ := 0) (x := x) (n := 8)
      hx.symm (Real.contDiff_sin.contDiffOn)
  refine ⟨xi, hxi, ?_⟩
  simpa using hrem

-- Explicit Lagrange remainder using cosine.
theorem sine_lagrange_cos
    (x : Real) (hx : Ne x 0) :
    Exists fun xi : Real =>
      xi ∈ Set.uIoo 0 x ∧
      Real.sin x -
        taylorWithinEval Real.sin 8 (Set.uIcc 0 x) 0 x =
        Real.cos xi * x^9 /
          (Nat.factorial 9 : Real) := by
  obtain ⟨xi, hxi, hrem⟩ :=
    sine_lagrange_remainder x hx
  refine ⟨xi, hxi, ?_⟩
  simpa [iteratedDeriv_succ,
    Real.deriv_sin, Real.deriv_cos] using hrem

-- Explicit ninth-order absolute remainder bound.
theorem sine_lagrange_abs_bound
    (x : Real) (hx : Ne x 0) :
    abs (Real.sin x -
      taylorWithinEval Real.sin 8 (Set.uIcc 0 x) 0 x)
      <= abs x ^ 9 / 362880 := by
  obtain ⟨xi, _, hrem⟩ := sine_lagrange_cos x hx
  have hcos : abs (Real.cos xi) <= (1 : Real) :=
    Real.abs_cos_le_one xi
  have hp : 0 <= abs x ^ 9 :=
    pow_nonneg (abs_nonneg x) 9
  have hmul :
      abs (Real.cos xi) * abs x ^ 9 <= abs x ^ 9 := by
    nlinarith [mul_le_mul_of_nonneg_right hcos hp]
  rw [hrem]
  have hfact : (Nat.factorial 9 : Real) = 362880 := by
    norm_num
  rw [hfact, abs_div, abs_mul, abs_pow]
  have hden : abs (362880 : Real) = 362880 := by
    norm_num
  rw [hden]
  exact (div_le_div_iff_of_pos_right
    (by norm_num : (0 : Real) < 362880)).2 hmul

-- Explicit degree-eight sine Taylor polynomial.
theorem sine_taylor_eight_univ (x : Real) :
    taylorWithinEval Real.sin 8 Set.univ 0 x =
      x - x^3 / 6 + x^5 / 120 - x^7 / 5040 := by
  simp [taylorWithinEval_succ,
        iteratedDerivWithin_univ,
        iteratedDeriv_succ,
        Real.deriv_sin,
        Real.deriv_cos,
        Real.sin_zero,
        Real.cos_zero]
  ; ring

-- Ninth-order sine remainder bound for every real x.
theorem sine_remainder_bound_all (x : Real) :
    abs (Real.sin x -
      (x - x^3 / 6 + x^5 / 120 - x^7 / 5040))
      <= abs x ^ 9 / 362880 := by
  by_cases hx : x = 0
  · subst x
    norm_num [Real.sin_zero]
  · have h := sine_lagrange_abs_bound x hx
    rw [sine_interval_taylor_eq_univ x hx 8,
        sine_taylor_eight_univ x] at h
    exact h

-- Scale the certified sine remainder by N > 0.
theorem sine_scaled_remainder_step
    (N : Real) (hN : 0 < N) :
    abs (N * Real.sin (Real.pi / N) -
      N * (Real.pi / N -
        (Real.pi / N)^3 / 6 +
        (Real.pi / N)^5 / 120 -
        (Real.pi / N)^7 / 5040))
      <= N * (abs (Real.pi / N)^9 / 362880) := by
  have h := sine_remainder_bound_all (Real.pi / N)
  calc
    abs (N * Real.sin (Real.pi / N) -
      N * (Real.pi / N -
        (Real.pi / N)^3 / 6 +
        (Real.pi / N)^5 / 120 -
        (Real.pi / N)^7 / 5040))
      = N * abs (Real.sin (Real.pi / N) -
          (Real.pi / N -
            (Real.pi / N)^3 / 6 +
            (Real.pi / N)^5 / 120 -
            (Real.pi / N)^7 / 5040)) := by
          rw [← mul_sub, abs_mul, abs_of_pos hN]
    _ <= N * (abs (Real.pi / N)^9 / 362880) :=
      mul_le_mul_of_nonneg_left h (le_of_lt hN)


-- Normalize the scaled Taylor polynomial.
theorem scaled_polynomial_normalize
    (N : Real) (hN : Ne N 0) :
    N * (Real.pi / N -
      (Real.pi / N)^3 / 6 +
      (Real.pi / N)^5 / 120 -
      (Real.pi / N)^7 / 5040) =
    Real.pi - Real.pi^3 / (6 * N^2) +
      Real.pi^5 / (120 * N^4) -
      Real.pi^7 / (5040 * N^6) := by
  field_simp [hN]

-- Normalize the scaled remainder.
theorem scaled_remainder_normalize
    (N : Real) (hN : 0 < N) :
    N * (abs (Real.pi / N)^9 / 362880) =
      Real.pi^9 / (362880 * N^8) := by
  rw [abs_div, abs_of_pos Real.pi_pos, abs_of_pos hN]
  field_simp [ne_of_gt hN]


-- Certified eighth-order N-series sine remainder.
theorem nseries_sine_remainder_bound
    (N : Real) (hN : 0 < N) :
    abs (N * Real.sin (Real.pi / N) -
      (Real.pi - Real.pi^3 / (6 * N^2) +
        Real.pi^5 / (120 * N^4) -
        Real.pi^7 / (5040 * N^6)))
      <= Real.pi^9 / (362880 * N^8) := by
  have h := sine_scaled_remainder_step N hN
  rw [scaled_polynomial_normalize N (ne_of_gt hN),
      scaled_remainder_normalize N hN] at h
  exact h
end BakerNSeries