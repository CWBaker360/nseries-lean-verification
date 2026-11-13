import NSeriesB5ActualBound

namespace BakerNSeries

theorem nseriesP_tendsto_pi :
    Filter.Tendsto nseriesP Filter.atTop (nhds Real.pi) := by
  have hinv : Filter.Tendsto (fun N : Real => N⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have h2' : Filter.Tendsto (fun N : Real => Real.pi^3 / (6 * N^2))
      Filter.atTop (nhds 0) := by
    convert (hinv.pow 2).const_mul (Real.pi^3 / 6) using 1 <;>
      simp [div_eq_mul_inv] <;> ring
  have h4' : Filter.Tendsto (fun N : Real => Real.pi^5 / (120 * N^4))
      Filter.atTop (nhds 0) := by
    convert (hinv.pow 4).const_mul (Real.pi^5 / 120) using 1 <;>
      simp [div_eq_mul_inv] <;> ring
  have h6' : Filter.Tendsto (fun N : Real => Real.pi^7 / (5040 * N^6))
      Filter.atTop (nhds 0) := by
    convert (hinv.pow 6).const_mul (Real.pi^7 / 5040) using 1 <;>
      simp [div_eq_mul_inv] <;> ring
  change Filter.Tendsto
    (fun N : Real => Real.pi - Real.pi^3 / (6 * N^2) +
      Real.pi^5 / (120 * N^4) - Real.pi^7 / (5040 * N^6))
    Filter.atTop (nhds Real.pi)
  simpa using
    (((tendsto_const_nhds : Filter.Tendsto (fun _ : Real => Real.pi)
      Filter.atTop (nhds Real.pi)).sub h2').add h4').sub h6'

theorem nseriesQ_sub_nseriesP_tendsto_zero :
    Filter.Tendsto (fun N : Real => nseriesQ N - nseriesP N)
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hinv : Filter.Tendsto (fun N : Real => N⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hmajor : Filter.Tendsto
      (fun N : Real => Real.pi^9 / (362880 * N^8))
      Filter.atTop (nhds 0) := by
    convert (hinv.pow 8).const_mul (Real.pi^9 / 362880) using 1 <;>
      simp [div_eq_mul_inv] <;> ring
  apply squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _)
  · filter_upwards [Filter.eventually_atTop.2 ⟨(1 : Real), fun N hN => hN⟩] with N hN
    simpa [Real.norm_eq_abs, nseriesQ, nseriesP] using
      nseries_sine_remainder_bound N (lt_of_lt_of_le zero_lt_one hN)
  · exact hmajor

theorem nseriesQ_tendsto_pi :
    Filter.Tendsto (fun N : Real => nseriesQ N) Filter.atTop (nhds Real.pi) := by
  have hsum := nseriesQ_sub_nseriesP_tendsto_zero.add nseriesP_tendsto_pi
  simpa [sub_add_cancel] using hsum

end BakerNSeries

#print axioms BakerNSeries.nseriesP_tendsto_pi
#print axioms BakerNSeries.nseriesQ_sub_nseriesP_tendsto_zero
#print axioms BakerNSeries.nseriesQ_tendsto_pi
