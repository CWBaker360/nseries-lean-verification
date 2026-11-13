import NSeriesD1
import NSeriesD2BChord
import NSeriesD3Minimum

namespace BakerNSeries

/-- The π-free intrinsic half-perimeter of the regular `n`-gon, with a harmless
zero value for the finitely many indices below three. -/
noncomputable def intrinsicPolygonHalfPerimeter (n : ℕ) : ℝ :=
  if hn : 3 ≤ n then
    letI : NeZero n := ⟨by omega⟩
    (n : ℝ) / 2 * minimumRootChord n (rootChordLengths_nonempty n hn)
  else 0

/-- Beyond the initial indices, intrinsic polygonal half-perimeter is exactly the
analytic N-Series expression. -/
theorem intrinsicPolygonHalfPerimeter_eq_nseriesQ
    (n : ℕ) (hn : 3 ≤ n) :
    intrinsicPolygonHalfPerimeter n = nseriesQ (n : ℝ) := by
  letI : NeZero n := ⟨by omega⟩
  rw [intrinsicPolygonHalfPerimeter, dite_eq_left hn]
  change (n : ℝ) / 2 * minimumRootChord n (rootChordLengths_nonempty n hn) =
    nseriesQ (n : ℝ)
  rw [minimumRootChord_eq_canonicalPolygonStep_chord n hn]
  rw [canonicalPolygonStep_chord_length n hn]
  simp [nseriesQ]
  ring

theorem nseriesQ_nat_tendsto_pi :
    Filter.Tendsto (fun n : ℕ => nseriesQ (n : ℝ)) Filter.atTop (nhds Real.pi) := by
  exact nseriesQ_tendsto_pi.comp tendsto_natCast_atTop_atTop

/-- The π-free intrinsic polygonal half-perimeters converge to classical π. -/
theorem intrinsicPolygonHalfPerimeter_tendsto_pi :
    Filter.Tendsto intrinsicPolygonHalfPerimeter Filter.atTop (nhds Real.pi) := by
  have heq : (fun n : ℕ => nseriesQ (n : ℝ)) =ᶠ[Filter.atTop]
      intrinsicPolygonHalfPerimeter := by
    filter_upwards [Filter.eventually_atTop.2
      ⟨3, fun n hn => intrinsicPolygonHalfPerimeter_eq_nseriesQ n hn⟩] with n hn
    exact hn.symm
  exact Filter.Tendsto.congr' heq nseriesQ_nat_tendsto_pi

/-- The geometric constant defined as the polygonal-limit value. -/
noncomputable def polygonalPi : ℝ :=
  Filter.limUnder Filter.atTop intrinsicPolygonHalfPerimeter

/-- The independently defined polygonal limit equals classical π. -/
theorem polygonalPi_eq_pi : polygonalPi = Real.pi := by
  unfold polygonalPi
  exact (Filter.limUnder_eq_iff ⟨Real.pi, intrinsicPolygonHalfPerimeter_tendsto_pi⟩).2
    intrinsicPolygonHalfPerimeter_tendsto_pi

end BakerNSeries

#print axioms BakerNSeries.intrinsicPolygonHalfPerimeter_eq_nseriesQ
#print axioms BakerNSeries.nseriesQ_nat_tendsto_pi
#print axioms BakerNSeries.intrinsicPolygonHalfPerimeter_tendsto_pi
#print axioms BakerNSeries.polygonalPi_eq_pi
