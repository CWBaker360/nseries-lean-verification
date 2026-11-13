/-
  E10 — Acceleration bounds restated on the intrinsic (π-free) polygonal
  half-perimeter sequence, via D3's identification with N·sin(π/N) for n ≥ 3.
  Candidate: not compiled.
-/
import NSeriesD3Limit
import NSeriesB6
import NSeriesE3ThreeScaleSharp

namespace BakerNSeries

/-- Corollary 3.2 on the intrinsic sequence: two-scale operator with integer
    scale factor k ≥ 2 applied to regular n-gons, n ≥ 3. -/
theorem intrinsic_two_scale_bound (n k : ℕ) (hn : 3 ≤ n) (hk : 2 ≤ k) :
    abs (((k : ℝ)^2 * intrinsicPolygonHalfPerimeter (k * n)
          - intrinsicPolygonHalfPerimeter n) / ((k : ℝ)^2 - 1)
        - Real.pi + Real.pi^5 / (120 * (k : ℝ)^2 * (n : ℝ)^4))
      ≤ richardsonC (k : ℝ) / (n : ℝ)^6 := by
  have hN1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  have hkn : 3 ≤ k * n := by nlinarith
  have h := richardson_error_bound (n : ℝ) (k : ℝ) hN1 hk1
  unfold nseriesR at h
  rw [intrinsicPolygonHalfPerimeter_eq_nseriesQ n hn,
    intrinsicPolygonHalfPerimeter_eq_nseriesQ (k * n) hkn, Nat.cast_mul]
  exact h

/-- Corollary 6.2 on the intrinsic sequence: the dyadic three-scale operator
    on regular n-, 2n- and 4n-gons, n ≥ 3, with sharp sixth-order term. -/
theorem intrinsic_dyadic_three_scale_sharp (n : ℕ) (hn : 3 ≤ n) :
    abs (1 / 45 * intrinsicPolygonHalfPerimeter n
        - 4 / 9 * intrinsicPolygonHalfPerimeter (2 * n)
        + 64 / 45 * intrinsicPolygonHalfPerimeter (4 * n)
        - Real.pi + Real.pi^7 / (322560 * (n : ℝ)^6))
      ≤ 17 / 9 * (Real.pi^9 / 362880 / (n : ℝ)^8) := by
  have hpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have h := dyadic_three_scale_sharp (n : ℝ) hpos
  have e2 : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by norm_num
  have e4 : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by norm_num
  rw [intrinsicPolygonHalfPerimeter_eq_nseriesQ n hn,
    intrinsicPolygonHalfPerimeter_eq_nseriesQ (2 * n) (by omega),
    intrinsicPolygonHalfPerimeter_eq_nseriesQ (4 * n) (by omega), e2, e4]
  exact h

end BakerNSeries

#print axioms BakerNSeries.intrinsic_two_scale_bound
#print axioms BakerNSeries.intrinsic_dyadic_three_scale_sharp
