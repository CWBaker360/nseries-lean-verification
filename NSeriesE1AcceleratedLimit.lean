/-
  Gap 1 — Theorem 4.2 of the paper: the accelerated limit π_g^(k) equals π.
  NOT YET COMPILED (written without a local Mathlib build).
-/
import NSeriesD1

namespace BakerNSeries

/-- The two-scale accelerated sequence converges to π (real scale variable). -/
theorem nseriesR_tendsto_pi (k : Real) (hk : 1 < k) :
    Filter.Tendsto (fun N : Real => nseriesR N k) Filter.atTop (nhds Real.pi) := by
  have hkpos : 0 < k := by linarith
  have hdenpos : 0 < k^2 - 1 := by
    nlinarith [sq_nonneg (k - 1)]
  have hden0 : k^2 - 1 ≠ 0 := ne_of_gt hdenpos
  have hscale : Filter.Tendsto (fun N : Real => k * N) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hkpos Filter.tendsto_id
  have hQk : Filter.Tendsto (fun N : Real => nseriesQ (k * N))
      Filter.atTop (nhds Real.pi) :=
    nseriesQ_tendsto_pi.comp hscale
  have hnum := (hQk.const_mul (k^2)).sub nseriesQ_tendsto_pi
  have hdiv := hnum.div_const (k^2 - 1)
  have hlim : (k^2 * Real.pi - Real.pi) / (k^2 - 1) = Real.pi := by
    rw [div_eq_iff hden0]
    ring
  rw [hlim] at hdiv
  unfold nseriesR
  exact hdiv

/-- Integer-indexed form, matching the paper's N ∈ ℕ. -/
theorem nseriesR_nat_tendsto_pi (k : Real) (hk : 1 < k) :
    Filter.Tendsto (fun n : ℕ => nseriesR (n : ℝ) k) Filter.atTop (nhds Real.pi) :=
  (nseriesR_tendsto_pi k hk).comp tendsto_natCast_atTop_atTop

/-- The accelerated geometric limit π_g^(k) (Definition 4.1). -/
noncomputable def acceleratedPi (k : Real) : ℝ :=
  Filter.limUnder Filter.atTop (fun n : ℕ => nseriesR (n : ℝ) k)

/-- Theorem 4.2: π_g^(k) = π for every k > 1. -/
theorem acceleratedPi_eq_pi (k : Real) (hk : 1 < k) : acceleratedPi k = Real.pi := by
  unfold acceleratedPi
  exact (Filter.limUnder_eq_iff ⟨Real.pi, nseriesR_nat_tendsto_pi k hk⟩).2
    (nseriesR_nat_tendsto_pi k hk)

end BakerNSeries

#print axioms BakerNSeries.nseriesR_tendsto_pi
#print axioms BakerNSeries.acceleratedPi_eq_pi
