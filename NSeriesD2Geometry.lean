import Mathlib

namespace BakerNSeries

/-- A regular polygon is generated geometrically from a unit complex step. -/
def regularVertex (z : ℂ) (j : ℕ) : ℂ := z ^ j

/-- The polygonal perimeter, expressed as a finite sum of Euclidean distances. -/
noncomputable def regularPolygonPerimeter (n : ℕ) (z : ℂ) : ℝ :=
  ∑ j ∈ Finset.range n, dist (regularVertex z j) (regularVertex z (j + 1))

/-- The half-perimeter is the prospective geometric approximation to π. -/
noncomputable def polygonHalfPerimeter (n : ℕ) (z : ℂ) : ℝ :=
  regularPolygonPerimeter n z / 2

theorem regularVertex_norm_one (z : ℂ) (j : ℕ) (hz : ‖z‖ = 1) :
    ‖regularVertex z j‖ = 1 := by
  simp [regularVertex, norm_pow, hz]

theorem regularPolygon_closes (n : ℕ) (z : ℂ) (hz : z ^ n = 1) :
    regularVertex z n = regularVertex z 0 := by
  simp [regularVertex, hz]

theorem regularPolygon_edge_length (z : ℂ) (j : ℕ) (hz : ‖z‖ = 1) :
    dist (regularVertex z j) (regularVertex z (j + 1)) = dist 1 z := by
  rw [dist_eq_norm_sub, dist_eq_norm_sub]
  dsimp [regularVertex]
  rw [pow_succ]
  have hfactor : z ^ j - z ^ j * z = z ^ j * (1 - z) := by ring
  rw [hfactor, norm_mul, norm_pow, hz]
  simp

theorem regularPolygon_perimeter_eq (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    regularPolygonPerimeter n z = n * dist 1 z := by
  rw [regularPolygonPerimeter]
  calc
    _ = ∑ _j ∈ Finset.range n, dist 1 z := by
      apply Finset.sum_congr rfl
      intro j hj
      exact regularPolygon_edge_length z j hz
    _ = n * dist 1 z := by simp [Finset.sum_const, Finset.card_range]

theorem regularPolygon_halfPerimeter_eq (n : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    polygonHalfPerimeter n z = (n : ℝ) * dist 1 z / 2 := by
  rw [polygonHalfPerimeter, regularPolygon_perimeter_eq n z hz]

end BakerNSeries

#print axioms BakerNSeries.regularPolygon_edge_length
#print axioms BakerNSeries.regularPolygon_perimeter_eq
#print axioms BakerNSeries.regularPolygon_halfPerimeter_eq
