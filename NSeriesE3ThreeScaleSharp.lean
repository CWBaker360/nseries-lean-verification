/-
  E3 — Sharp three-scale expansion:
    R₃(N) = π − π⁷/(5040·k⁶·N⁶) + O(N⁻⁸),
  and the dyadic case π − π⁷/(322560·N⁶) for scales N, 2N, 4N (Corollary 6.2).
  NOT YET COMPILED (written without a local Mathlib build).
-/
import NSeriesE2ThreeScale

namespace BakerNSeries

/-- |A + B + C| ≤ |A| + |B| + |C|. -/
theorem abs_three_add_le (A B C : Real) :
    abs (A + B + C) ≤ abs A + abs B + abs C := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self A, neg_abs_le A, le_abs_self B, neg_abs_le B,
      le_abs_self C, neg_abs_le C]

/-- Sine remainder at any scale M ≥ N > 0, bounded at the base scale, order N⁻⁸. -/
theorem nseries_remainder_le_base8 (N M : Real) (hN : 0 < N) (hM : N ≤ M) :
    abs (nseriesQ M - nseriesP M) ≤ Real.pi^9 / 362880 / N^8 := by
  have hMpos : 0 < M := lt_of_lt_of_le hN hM
  have h : abs (nseriesQ M - nseriesP M) ≤ Real.pi^9 / (362880 * M^8) := by
    unfold nseriesQ nseriesP
    exact nseries_sine_remainder_bound M hMpos
  have hpow : N^8 ≤ M^8 := pow_le_pow_left₀ (le_of_lt hN) hM 8
  have hpi : 0 ≤ Real.pi^9 := pow_nonneg (le_of_lt Real.pi_pos) 9
  have hstep : Real.pi^9 / (362880 * M^8) ≤ Real.pi^9 / 362880 / N^8 := by
    rw [div_div]
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) (pow_pos hMpos 8))
      (mul_pos (by norm_num) (pow_pos hN 8))).2
    nlinarith [mul_le_mul_of_nonneg_left hpow hpi]
  exact le_trans h hstep

/-- Sharp three-scale bound for any weights satisfying the moment conditions,
    with sixth moment `m` and absolute weight sum at most `S`. -/
theorem three_scale_sharp_weights
    (a b c m S N k : Real) (hN : 0 < N) (hk : 1 < k)
    (h0 : a + b + c = 1)
    (h2 : a + b / k^2 + c / k^4 = 0)
    (h4 : a + b / k^4 + c / k^8 = 0)
    (h6 : a + b / k^6 + c / k^12 = m)
    (hS : abs a + abs b + abs c ≤ S) :
    abs (a * nseriesQ N + b * nseriesQ (k * N) + c * nseriesQ (k^2 * N)
        - Real.pi + Real.pi^7 / (5040 * N^6) * m)
      ≤ S * (Real.pi^9 / 362880 / N^8) := by
  have hkpos : 0 < k := by linarith
  have hN0 : N ≠ 0 := ne_of_gt hN
  have hk0 : k ≠ 0 := ne_of_gt hkpos
  have hk2 : 1 ≤ k^2 := by nlinarith
  have hkN : N ≤ k * N := by
    nlinarith [mul_nonneg (sub_nonneg.2 (le_of_lt hk)) (le_of_lt hN)]
  have hk2N : N ≤ k^2 * N := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk2) (le_of_lt hN)]
  have e1 := nseries_remainder_le_base8 N N hN (le_refl N)
  have e2 := nseries_remainder_le_base8 N (k * N) hN hkN
  have e3 := nseries_remainder_le_base8 N (k^2 * N) hN hk2N
  have hE : 0 ≤ Real.pi^9 / 362880 / N^8 :=
    le_of_lt (div_pos (div_pos (pow_pos Real.pi_pos 9) (by norm_num)) (pow_pos hN 8))
  have hpoly := three_scale_poly_identity a b c k N hk0 hN0
  have hsplit :
      a * nseriesQ N + b * nseriesQ (k * N) + c * nseriesQ (k^2 * N)
          - Real.pi + Real.pi^7 / (5040 * N^6) * m
        = a * (nseriesQ N - nseriesP N)
          + b * (nseriesQ (k * N) - nseriesP (k * N))
          + c * (nseriesQ (k^2 * N) - nseriesP (k^2 * N)) := by
    linear_combination hpoly + Real.pi * h0
      - Real.pi^3 / (6 * N^2) * h2 + Real.pi^5 / (120 * N^4) * h4
      - Real.pi^7 / (5040 * N^6) * h6
  have t1 : abs (a * (nseriesQ N - nseriesP N))
      ≤ abs a * (Real.pi^9 / 362880 / N^8) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left e1 (abs_nonneg a)
  have t2 : abs (b * (nseriesQ (k * N) - nseriesP (k * N)))
      ≤ abs b * (Real.pi^9 / 362880 / N^8) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left e2 (abs_nonneg b)
  have t3 : abs (c * (nseriesQ (k^2 * N) - nseriesP (k^2 * N)))
      ≤ abs c * (Real.pi^9 / 362880 / N^8) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left e3 (abs_nonneg c)
  have htri := abs_three_add_le
    (a * (nseriesQ N - nseriesP N))
    (b * (nseriesQ (k * N) - nseriesP (k * N)))
    (c * (nseriesQ (k^2 * N) - nseriesP (k^2 * N)))
  have hSE := mul_le_mul_of_nonneg_right hS hE
  rw [hsplit]
  linarith [htri, t1, t2, t3, hSE]

/-- The sixth moment of the Theorem 6.1 weights is exactly 1/k⁶. -/
theorem w_moment6 (k : Real) (hk : 1 < k) :
    wa k + wb k / k ^ 6 + wc k / k ^ 12 = 1 / k ^ 6 := by
  have hk0 : k ≠ 0 := (by linarith : (0 : ℝ) < k).ne'
  have h1 : k ^ 2 - 1 ≠ 0 := (by nlinarith : (0 : ℝ) < k ^ 2 - 1).ne'
  have h2 : k ^ 2 + 1 ≠ 0 := (by positivity : (0 : ℝ) < k ^ 2 + 1).ne'
  unfold wa wb wc
  field_simp
  ring

/-- Sharp three-scale expansion: R₃(N) = π − π⁷/(5040·k⁶·N⁶) + O(N⁻⁸),
    with explicit constant. -/
theorem three_scale_sharp (N k : Real) (hN : 0 < N) (hk : 1 < k) :
    abs (nseriesR3 N k - Real.pi + Real.pi^7 / (5040 * k^6 * N^6))
      ≤ (abs (wa k) + abs (wb k) + abs (wc k)) * (Real.pi^9 / 362880 / N^8) := by
  have h := three_scale_sharp_weights (wa k) (wb k) (wc k) (1 / k^6)
    (abs (wa k) + abs (wb k) + abs (wc k)) N k hN hk
    (w_sum k hk) (w_moment2 k hk) (w_moment4 k hk) (w_moment6 k hk) (le_refl _)
  have harg :
      nseriesR3 N k - Real.pi + Real.pi^7 / (5040 * k^6 * N^6)
        = wa k * nseriesQ N + wb k * nseriesQ (k * N) + wc k * nseriesQ (k^2 * N)
          - Real.pi + Real.pi^7 / (5040 * N^6) * (1 / k^6) := by
    unfold nseriesR3
    ring
  rw [harg]
  exact h

/-- Corollary 6.2 on the polygonal sequence, sharp form:
    (1/45)·Q_N − (4/9)·Q_{2N} + (64/45)·Q_{4N} = π − π⁷/(322560·N⁶) + O(N⁻⁸). -/
theorem dyadic_three_scale_sharp (N : Real) (hN : 0 < N) :
    abs (1 / 45 * nseriesQ N - 4 / 9 * nseriesQ (2 * N) + 64 / 45 * nseriesQ (4 * N)
        - Real.pi + Real.pi^7 / (322560 * N^6))
      ≤ 17 / 9 * (Real.pi^9 / 362880 / N^8) := by
  have hS : abs (1 / 45 : ℝ) + abs (-(4 / 9) : ℝ) + abs (64 / 45 : ℝ) ≤ 17 / 9 := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 45),
      abs_of_neg (by norm_num : (-(4 / 9) : ℝ) < 0),
      abs_of_pos (by norm_num : (0 : ℝ) < 64 / 45)]
    norm_num
  have h := three_scale_sharp_weights (1 / 45) (-(4 / 9)) (64 / 45) (1 / 64) (17 / 9)
    N 2 hN (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hS
  have e4 : (2 : ℝ)^2 * N = 4 * N := by ring
  rw [e4] at h
  have harg :
      1 / 45 * nseriesQ N - 4 / 9 * nseriesQ (2 * N) + 64 / 45 * nseriesQ (4 * N)
          - Real.pi + Real.pi^7 / (322560 * N^6)
        = 1 / 45 * nseriesQ N + -(4 / 9) * nseriesQ (2 * N) + 64 / 45 * nseriesQ (4 * N)
          - Real.pi + Real.pi^7 / (5040 * N^6) * (1 / 64) := by
    ring
  rw [harg]
  exact h

end BakerNSeries

#print axioms BakerNSeries.three_scale_sharp
#print axioms BakerNSeries.dyadic_three_scale_sharp
