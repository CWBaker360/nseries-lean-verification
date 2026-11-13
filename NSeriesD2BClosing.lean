import NSeriesD2Geometry
import NSeriesD2BPrimitive

namespace BakerNSeries

theorem canonicalPolygonStep_norm_one (n : ℕ) :
    ‖canonicalPolygonStep n‖ = 1 := by
  rw [canonicalPolygonStep]
  convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi / n) using 1 <;>
    push_cast <;> ring

theorem canonicalPolygonStep_closing_edge (n : ℕ) (hn : n ≠ 0) :
    dist (canonicalPolygonStep n ^ (n - 1)) 1 =
      dist 1 (canonicalPolygonStep n) := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  have hedge := regularPolygon_edge_length (canonicalPolygonStep n) (n - 1)
    (canonicalPolygonStep_norm_one n)
  rw [regularVertex, regularVertex] at hedge
  have hlast : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  have hclose : canonicalPolygonStep n ^ n = 1 :=
    (canonicalPolygonStep_pow_eq_one_iff n n hn).2 (dvd_refl n)
  simpa [hlast, hclose] using hedge

end BakerNSeries

#print axioms BakerNSeries.canonicalPolygonStep_norm_one
#print axioms BakerNSeries.canonicalPolygonStep_closing_edge
