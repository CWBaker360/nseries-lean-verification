import NSeriesC2Final

namespace BakerNSeries

-- Module B3: rigorous Richardson error propagation.
-- First establish an absolute bound for arbitrary residuals.

theorem two_scale_residual_abs
    (k e1 e2 : Real) (hden : 0 < k^2 - 1) :
    abs ((k^2 * e2 - e1) / (k^2 - 1))
      <= (k^2 * abs e2 + abs e1) / (k^2 - 1) := by
  have htriangle :
      abs (k^2 * e2 - e1) <=
        abs (k^2 * e2) + abs e1 := by
    calc
      abs (k^2 * e2 - e1)
          = abs (k^2 * e2 + (-e1)) := by
              rw [sub_eq_add_neg]
      _ <= abs (k^2 * e2) + abs (-e1) :=
          abs_add_le _ _
      _ = abs (k^2 * e2) + abs e1 := by
          rw [abs_neg]
  have hmul :
      abs (k^2 * e2) = k^2 * abs e2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg k)]
  rw [abs_div, abs_of_pos hden]
  apply (div_le_div_iff_of_pos_right hden).2
  rw [hmul] at htriangle
  exact htriangle

-- Error budgets for the two input approximations.
theorem two_scale_error_budget
    (k e1 e2 B1 B2 : Real)
    (hk : 1 < k)
    (h1 : abs e1 <= B1)
    (h2 : abs e2 <= B2) :
    abs ((k^2 * e2 - e1) / (k^2 - 1))
      <= (k^2 * B2 + B1) / (k^2 - 1) := by
  have hden : 0 < k^2 - 1 := by
    nlinarith [sq_nonneg (k - 1)]
  have hbase :=
    two_scale_residual_abs k e1 e2 hden
  apply le_trans hbase
  apply (div_le_div_iff_of_pos_right hden).2
  have hmul :
      k^2 * abs e2 <= k^2 * B2 :=
    mul_le_mul_of_nonneg_left h2 (sq_nonneg k)
  linarith


-- Module B4: certified two-scale sine residual propagation.

noncomputable def nseriesQ (N : Real) : Real :=
  N * Real.sin (Real.pi / N)

noncomputable def nseriesP (N : Real) : Real :=
  Real.pi - Real.pi^3 / (6 * N^2)
    + Real.pi^5 / (120 * N^4)
    - Real.pi^7 / (5040 * N^6)

theorem two_scale_sine_residual_bound
    (N k : Real) (hN : 0 < N) (hk : 1 < k) :
    abs ((k^2 * (nseriesQ (k*N) - nseriesP (k*N))
      - (nseriesQ N - nseriesP N)) / (k^2 - 1))
    <=
      (k^2 * (Real.pi^9 / (362880 * (k*N)^8))
        + Real.pi^9 / (362880 * N^8))
        / (k^2 - 1) := by
  have hkpos : 0 < k := by
    linarith
  have hkN : 0 < k * N := mul_pos hkpos hN
  have h1 :
      abs (nseriesQ N - nseriesP N)
        <= Real.pi^9 / (362880 * N^8) := by
    simpa [nseriesQ, nseriesP] using
      nseries_sine_remainder_bound N hN
  have h2 :
      abs (nseriesQ (k*N) - nseriesP (k*N))
        <= Real.pi^9 / (362880 * (k*N)^8) := by
    simpa [nseriesQ, nseriesP] using
      nseries_sine_remainder_bound (k*N) hkN
  exact two_scale_error_budget k
    (nseriesQ N - nseriesP N)
    (nseriesQ (k*N) - nseriesP (k*N))
    (Real.pi^9 / (362880 * N^8))
    (Real.pi^9 / (362880 * (k*N)^8))
    hk h1 h2



-- Richardson cancellation through sixth order.
-- The coefficient of N^(-2) cancels exactly.
-- The surviving fourth-order coefficient is -pi^5/(120*k^2).

theorem two_scale_fourth_order_model
    (N k : Real) (hN : Ne N 0)
    (hk : Ne k 0) (hk1 : Ne (k^2 - 1) 0) :
    (k^2 * (
       Real.pi
       - Real.pi^3 / (6 * (k*N)^2)
       + Real.pi^5 / (120 * (k*N)^4)
       - Real.pi^7 / (5040 * (k*N)^6))
     - (
       Real.pi
       - Real.pi^3 / (6 * N^2)
       + Real.pi^5 / (120 * N^4)
       - Real.pi^7 / (5040 * N^6)))
       / (k^2 - 1)
    =
      Real.pi
      - Real.pi^5 / (120 * k^2 * N^4)
      + Real.pi^7 * (k^2 + 1) /
          (5040 * k^4 * N^6) := by
  field_simp [hN, hk, hk1]
  ring


-- B5: actual two-scale Richardson error bound.

noncomputable def nseriesR (N k : Real) : Real :=
  (k^2 * nseriesQ (k*N) - nseriesQ N) / (k^2 - 1)

theorem two_scale_actual_error_bound_raw
    (N k : Real) (hN : 0 < N) (hk : 1 < k) :
    abs (nseriesR N k - Real.pi
      + Real.pi^5 / (120 * k^2 * N^4))
    <=
      Real.pi^7 * (k^2 + 1) /
        (5040 * k^4 * N^6)
      +
      (k^2 * (Real.pi^9 / (362880 * (k*N)^8))
        + Real.pi^9 / (362880 * N^8))
        / (k^2 - 1) := by

  have hN0 : Ne N 0 := ne_of_gt hN
  have hk0 : Ne k 0 := ne_of_gt (by linarith : 0 < k)
  have hdenpos : 0 < k^2 - 1 := by
    nlinarith [sq_nonneg (k - 1)]
  have hden0 : Ne (k^2 - 1) 0 := ne_of_gt hdenpos

  let b : Real :=
    Real.pi^7 * (k^2 + 1) /
      (5040 * k^4 * N^6)

  let e : Real :=
    (k^2 * (nseriesQ (k*N) - nseriesP (k*N))
      - (nseriesQ N - nseriesP N)) / (k^2 - 1)

  have hmodel :
      (k^2 * nseriesP (k*N) - nseriesP N) /
          (k^2 - 1)
        = Real.pi
          - Real.pi^5 / (120 * k^2 * N^4)
          + b := by
    simpa [nseriesP, b] using
      two_scale_fourth_order_model N k hN0 hk0 hden0

  have hsplit :
      nseriesR N k =
        (k^2 * nseriesP (k*N) - nseriesP N) /
          (k^2 - 1) + e := by
    dsimp [nseriesR, e]
    ring

  have hbpos : 0 <= b := by
    dsimp [b]
    positivity

  have herr :
      abs e <=
        (k^2 * (Real.pi^9 / (362880 * (k*N)^8))
          + Real.pi^9 / (362880 * N^8))
          / (k^2 - 1) := by
    exact two_scale_sine_residual_bound N k hN hk

  calc
    abs (nseriesR N k - Real.pi
        + Real.pi^5 / (120 * k^2 * N^4))
      = abs (b + e) := by
          rw [hsplit, hmodel]
          congr 1
          ring
    _ <= abs b + abs e := abs_add_le b e
    _ = b + abs e := by rw [abs_of_nonneg hbpos]
    _ <= b +
        (k^2 * (Real.pi^9 / (362880 * (k*N)^8))
          + Real.pi^9 / (362880 * N^8))
          / (k^2 - 1) := by
          exact add_le_add_right herr b
    _ = Real.pi^7 * (k^2 + 1) /
          (5040 * k^4 * N^6)
        +
        (k^2 * (Real.pi^9 / (362880 * (k*N)^8))
          + Real.pi^9 / (362880 * N^8))
          / (k^2 - 1) := by
          rfl

end BakerNSeries