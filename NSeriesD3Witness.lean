import NSeriesD3Foundation
import NSeriesD2BPrimitive

namespace BakerNSeries

noncomputable def canonicalRootWitness (n : ℕ) [NeZero n] : rootsOfUnity n ℂ :=
  rootsOfUnity.mkOfPowEq
    (canonicalPolygonStep n)
    ((canonicalPolygonStep_pow_eq_one_iff n n NeZero.out).2 (dvd_refl n))

theorem canonicalRootWitness_coe (n : ℕ) [NeZero n] :
    ((canonicalRootWitness n).1 : ℂˣ) =
      Units.mk0 (canonicalPolygonStep n) (by
        dsimp [canonicalPolygonStep]
        exact Complex.exp_ne_zero _) := by
  apply Units.ext
  rfl

theorem canonicalRootWitness_coe_complex (n : ℕ) [NeZero n] :
    (((canonicalRootWitness n).1 : ℂˣ) : ℂ) = canonicalPolygonStep n := by
  rfl

end BakerNSeries

#print axioms BakerNSeries.canonicalRootWitness_coe
#print axioms BakerNSeries.canonicalRootWitness_coe_complex
