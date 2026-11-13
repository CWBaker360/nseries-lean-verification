import NSeriesD3ChordPowers
import NSeriesD3SineComparison

namespace BakerNSeries

theorem canonicalPolygonStep_chord_le_pow_chord
    (n k : ℕ) (hn : 3 ≤ n) (hk1 : 1 ≤ k) (hkn : k < n) :
    dist (1 : ℂ) (canonicalPolygonStep n) ≤
      dist (1 : ℂ) (canonicalPolygonStep n ^ k) := by
  have hleft := canonicalPolygonStep_pow_chord_length n 1 hn (by omega)
  have hright := canonicalPolygonStep_pow_chord_length n k hn (by omega)
  have hleft' : dist (1 : ℂ) (canonicalPolygonStep n) =
      2 * Real.sin (Real.pi / n) := by simpa using hleft
  calc
    dist (1 : ℂ) (canonicalPolygonStep n) = 2 * Real.sin (Real.pi / n) := hleft'
    _ ≤ 2 * Real.sin (Real.pi * k / n) :=
      mul_le_mul_of_nonneg_left
        (sine_adjacent_le_sine_multiple n k hn hk1 hkn) (by norm_num)
    _ = dist (1 : ℂ) (canonicalPolygonStep n ^ k) := hright.symm

end BakerNSeries

#print axioms BakerNSeries.canonicalPolygonStep_chord_le_pow_chord
