/-
  Gap 3 — Theorem 6.1 of the paper for the actual polygonal sequence:
  the three-scale operator has error O(N⁻⁶), with an explicit constant.
  NOT YET COMPILED (written without a local Mathlib build).
-/
import NSeriesAlgebra
import NSeriesB5ActualBound

namespace BakerNSeries

/-- |A + B + C − D| ≤ |A| + |B| + |C| + |D|. -/
theorem abs_three_add_sub_le (A B C D : Real) :
    abs (A + B + C - D) ≤ abs A + abs B + abs C + abs D := by
  rw [abs_le]
  constructor <;>
    linarith [le_abs_self A, neg_abs_le A, le_abs_self B, neg_abs_le B,
      le_abs_self C, neg_abs_le C, le_abs_self D, neg_abs_le D]

/-- Weighted three-scale combination of the degree-6 model polynomial,
    grouped by the moment sums of the weights. -/
theorem three_scale_poly_identity (a b c k N : Real) (hk : k ≠ 0) (hN : N ≠ 0) :
    a * nseriesP N + b * nseriesP (k * N) + c * nseriesP (k^2 * N)
      = Real.pi * (a + b + c)
        - Real.pi^3 / (6 * N^2) * (a + b / k^2 + c / k^4)
        + Real.pi^5 / (120 * N^4) * (a + b / k^4 + c / k^8)
        - Real.pi^7 / (5040 * N^6) * (a + b / k^6 + c / k^12) := by
  unfold nseriesP
  field_simp
  ring

/-- Sine remainder at any scale M ≥ N ≥ 1, bounded at the base scale. -/
theorem nseries_remainder_le_base (N M : Real) (hN : 1 ≤ N) (hM : N ≤ M) :
    abs (nseriesQ M - nseriesP M) ≤ Real.pi^9 / 362880 / N^6 := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hMpos : 0 < M := lt_of_lt_of_le hNpos hM
  have h : abs (nseriesQ M - nseriesP M) ≤ Real.pi^9 / (362880 * M^8) := by
    unfold nseriesQ nseriesP
    exact nseries_sine_remainder_bound M hMpos
  have hN68 : N^6 ≤ N^8 := by
    have hN6 : 0 ≤ N^6 := pow_nonneg (le_of_lt hNpos) 6
    have hN2 : 1 ≤ N^2 := by nlinarith
    calc
      N^6 = N^6 * 1 := by ring
      _ ≤ N^6 * N^2 := mul_le_mul_of_nonneg_left hN2 hN6
      _ = N^8 := by ring
  have hNM : N^8 ≤ M^8 := pow_le_pow_left₀ (le_of_lt hNpos) hM 8
  have hpow : N^6 ≤ M^8 := le_trans hN68 hNM
  have hpi : 0 ≤ Real.pi^9 := pow_nonneg (le_of_lt Real.pi_pos) 9
  have hstep : Real.pi^9 / (362880 * M^8) ≤ Real.pi^9 / 362880 / N^6 := by
    rw [div_div]
    apply (div_le_div_iff₀
      (mul_pos (by norm_num) (pow_pos hMpos 8))
      (mul_pos (by norm_num) (pow_pos hNpos 6))).2
    nlinarith [mul_le_mul_of_nonneg_left hpow hpi]
  exact le_trans h hstep

/-- Three-scale error bound for any weights satisfying the moment conditions. -/
theorem three_scale_error_bound_weights
    (a b c N k : Real) (hN : 1 ≤ N) (hk : 1 < k)
    (h0 : a + b + c = 1)
    (h2 : a + b / k^2 + c / k^4 = 0)
    (h4 : a + b / k^4 + c / k^8 = 0) :
    abs (a * nseriesQ N + b * nseriesQ (k * N) + c * nseriesQ (k^2 * N) - Real.pi)
      ≤ Real.pi^7 / (5040 * N^6) * abs (a + b / k^6 + c / k^12)
        + (abs a + abs b + abs c) * (Real.pi^9 / 362880 / N^6) := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hkpos : 0 < k := by linarith
  have hN0 : N ≠ 0 := ne_of_gt hNpos
  have hk0 : k ≠ 0 := ne_of_gt hkpos
  have hk2 : 1 ≤ k^2 := by nlinarith
  have hkN : N ≤ k * N := by
    nlinarith [mul_nonneg (sub_nonneg.2 (le_of_lt hk)) (le_of_lt hNpos)]
  have hk2N : N ≤ k^2 * N := by
    nlinarith [mul_nonneg (sub_nonneg.2 hk2) (le_of_lt hNpos)]
  have e1 := nseries_remainder_le_base N N hN (le_refl N)
  have e2 := nseries_remainder_le_base N (k * N) hN hkN
  have e3 := nseries_remainder_le_base N (k^2 * N) hN hk2N
  have hpoly := three_scale_poly_identity a b c k N hk0 hN0
  have hsplit :
      a * nseriesQ N + b * nseriesQ (k * N) + c * nseriesQ (k^2 * N) - Real.pi
        = a * (nseriesQ N - nseriesP N)
          + b * (nseriesQ (k * N) - nseriesP (k * N))
          + c * (nseriesQ (k^2 * N) - nseriesP (k^2 * N))
          - Real.pi^7 / (5040 * N^6) * (a + b / k^6 + c / k^12) := by
    linear_combination hpoly + Real.pi * h0
      - Real.pi^3 / (6 * N^2) * h2 + Real.pi^5 / (120 * N^4) * h4
  have t1 : abs (a * (nseriesQ N - nseriesP N))
      ≤ abs a * (Real.pi^9 / 362880 / N^6) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left e1 (abs_nonneg a)
  have t2 : abs (b * (nseriesQ (k * N) - nseriesP (k * N)))
      ≤ abs b * (Real.pi^9 / 362880 / N^6) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left e2 (abs_nonneg b)
  have t3 : abs (c * (nseriesQ (k^2 * N) - nseriesP (k^2 * N)))
      ≤ abs c * (Real.pi^9 / 362880 / N^6) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left e3 (abs_nonneg c)
  have hcoef : 0 ≤ Real.pi^7 / (5040 * N^6) :=
    le_of_lt (div_pos (pow_pos Real.pi_pos 7)
      (mul_pos (by norm_num) (pow_pos hNpos 6)))
  have t4 : abs (Real.pi^7 / (5040 * N^6) * (a + b / k^6 + c / k^12))
      = Real.pi^7 / (5040 * N^6) * abs (a + b / k^6 + c / k^12) := by
    rw [abs_mul, abs_of_nonneg hcoef]
  have htri := abs_three_add_sub_le
    (a * (nseriesQ N - nseriesP N))
    (b * (nseriesQ (k * N) - nseriesP (k * N)))
    (c * (nseriesQ (k^2 * N) - nseriesP (k^2 * N)))
    (Real.pi^7 / (5040 * N^6) * (a + b / k^6 + c / k^12))
  rw [hsplit]
  rw [t4] at htri
  linarith [htri, t1, t2, t3]

/-- The three-scale operator of Theorem 6.1 on the polygonal sequence. -/
noncomputable def nseriesR3 (N k : Real) : Real :=
  wa k * nseriesQ N + wb k * nseriesQ (k * N) + wc k * nseriesQ (k^2 * N)

/-- The explicit constant in the three-scale O(N⁻⁶) bound. -/
noncomputable def threeScaleC (k : Real) : Real :=
  Real.pi^7 / 5040 * abs (wa k + wb k / k^6 + wc k / k^12)
    + (abs (wa k) + abs (wb k) + abs (wc k)) * (Real.pi^9 / 362880)

/-- Theorem 6.1 for the polygonal sequence, with explicit constant. -/
theorem three_scale_error_bound (N k : Real) (hN : 1 ≤ N) (hk : 1 < k) :
    abs (nseriesR3 N k - Real.pi) ≤ threeScaleC k / N^6 := by
  have h := three_scale_error_bound_weights (wa k) (wb k) (wc k) N k hN hk
    (w_sum k hk) (w_moment2 k hk) (w_moment4 k hk)
  have hrhs :
      Real.pi^7 / (5040 * N^6) * abs (wa k + wb k / k^6 + wc k / k^12)
        + (abs (wa k) + abs (wb k) + abs (wc k)) * (Real.pi^9 / 362880 / N^6)
      = threeScaleC k / N^6 := by
    unfold threeScaleC
    ring
  unfold nseriesR3
  rw [← hrhs]
  exact h

open Asymptotics

/-- Theorem 6.1 in big-O form. -/
theorem three_scale_error_isBigO (k : Real) (hk : 1 < k) :
    (fun N : Real => nseriesR3 N k - Real.pi)
      =O[Filter.atTop] (fun N : Real => 1 / N^6) := by
  rw [isBigO_iff]
  refine ⟨threeScaleC k, Filter.eventually_atTop.2 ⟨1, ?_⟩⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpos : (0 : Real) < 1 / N^6 := one_div_pos.2 (pow_pos hNpos 6)
  have h := three_scale_error_bound N k hN hk
  simp only [Real.norm_eq_abs]
  rw [abs_of_pos hpos]
  calc
    abs (nseriesR3 N k - Real.pi) ≤ threeScaleC k / N^6 := h
    _ = threeScaleC k * (1 / N^6) := by ring

end BakerNSeries

#print axioms BakerNSeries.three_scale_error_bound
#print axioms BakerNSeries.three_scale_error_isBigO
