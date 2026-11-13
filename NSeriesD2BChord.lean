import NSeriesD2Geometry
import NSeriesD2BPrimitive
import NSeriesD2BClosing
import NSeriesB5ActualBound

namespace BakerNSeries

theorem canonicalPolygonStep_chord_length (n : ℕ) (hn : 3 ≤ n) :
    dist (1 : ℂ) (canonicalPolygonStep n) =
      2 * Real.sin (Real.pi / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hargpos : 0 < Real.pi / (n : ℝ) :=
    div_pos Real.pi_pos hn0
  have harglt : Real.pi / (n : ℝ) < Real.pi := by
    apply (div_lt_iff₀ hn0).2
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi / (n : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hargpos harglt
  rw [dist_eq_norm_sub]
  have hexp : canonicalPolygonStep n =
      Complex.exp (Complex.I * ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ)) := by
    rw [canonicalPolygonStep]
    congr 1
    push_cast
    ring
  rw [hexp]
  calc
    ‖1 - Complex.exp (Complex.I * ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ))‖
        = ‖Complex.exp (Complex.I * ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ)) - 1‖ := by
          rw [← norm_neg]
          congr 1
          ring
    _ = ‖2 * Real.sin ((2 * Real.pi / (n : ℝ)) / 2)‖ :=
      Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi / (n : ℝ))
    _ = 2 * Real.sin (Real.pi / (n : ℝ)) := by
      rw [show (2 * Real.pi / (n : ℝ)) / 2 = Real.pi / (n : ℝ) by ring]
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hsin)]

theorem canonicalPolygon_halfPerimeter_eq_nseriesQ (n : ℕ) (hn : 3 ≤ n) :
    polygonHalfPerimeter n (canonicalPolygonStep n) = nseriesQ (n : ℝ) := by
  rw [regularPolygon_halfPerimeter_eq n (canonicalPolygonStep n)
    (canonicalPolygonStep_norm_one n)]
  rw [canonicalPolygonStep_chord_length n hn]
  simp [nseriesQ]
  ring

end BakerNSeries

#print axioms BakerNSeries.canonicalPolygonStep_chord_length
#print axioms BakerNSeries.canonicalPolygon_halfPerimeter_eq_nseriesQ
