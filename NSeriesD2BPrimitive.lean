import Mathlib

namespace BakerNSeries

noncomputable def canonicalPolygonStep (n : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / n)

theorem canonicalPolygonStep_isPrimitiveRoot (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot (canonicalPolygonStep n) n := by
  simpa [canonicalPolygonStep] using Complex.isPrimitiveRoot_exp n hn

theorem canonicalPolygonStep_orderOf (n : ℕ) (hn : n ≠ 0) :
    orderOf (canonicalPolygonStep n) = n := by
  let z := canonicalPolygonStep n
  have hprimitive : IsPrimitiveRoot z n :=
    canonicalPolygonStep_isPrimitiveRoot n hn
  have hdata := (IsPrimitiveRoot.iff_def z n).mp hprimitive
  apply Nat.dvd_antisymm
  · exact orderOf_dvd_of_pow_eq_one hdata.1
  · exact hdata.2 (orderOf z) (pow_orderOf_eq_one z)

theorem canonicalPolygonStep_pow_eq_one_iff
    (n k : ℕ) (hn : n ≠ 0) :
    canonicalPolygonStep n ^ k = 1 ↔ n ∣ k := by
  exact (canonicalPolygonStep_isPrimitiveRoot n hn).pow_eq_one_iff_dvd k

end BakerNSeries

#print axioms BakerNSeries.canonicalPolygonStep_isPrimitiveRoot
#print axioms BakerNSeries.canonicalPolygonStep_orderOf
#print axioms BakerNSeries.canonicalPolygonStep_pow_eq_one_iff
