/-
  E4 — Section 10 chord-trisection recurrence:
  seeds c₃ = √3/2 and c₆ = 1/2, the cubic 4u³ − 3u + c_N = 0 at u = c_{3N},
  and uniqueness of that root in [0, 1/2].
  NOT YET COMPILED (written without a local Mathlib build).
-/
import NSeriesAlgebra

namespace BakerNSeries

/-- The chord half-length c_N = sin(π/N). -/
noncomputable def chordHalf (N : Real) : Real := Real.sin (Real.pi / N)

/-- Triangle seed: c₃ = √3/2. -/
theorem chordHalf_three : chordHalf 3 = Real.sqrt 3 / 2 := by
  unfold chordHalf
  exact Real.sin_pi_div_three

/-- Hexagon seed: c₆ = 1/2. -/
theorem chordHalf_six : chordHalf 6 = 1 / 2 := by
  unfold chordHalf
  exact Real.sin_pi_div_six

/-- c_{3N} satisfies the chord-trisection cubic 4u³ − 3u + c_N = 0. -/
theorem chordHalf_trisection (N : Real) :
    4 * chordHalf (3 * N) ^ 3 - 3 * chordHalf (3 * N) + chordHalf N = 0 := by
  have h := trisection_cubic (Real.pi / N)
  have harg : Real.pi / N / 3 = Real.pi / (3 * N) := by ring
  rw [harg] at h
  unfold chordHalf
  exact h

/-- For N ≥ 2 the trisected chord lies in [0, 1/2]. -/
theorem chordHalf_trisection_range (N : Real) (hN : 2 ≤ N) :
    0 ≤ chordHalf (3 * N) ∧ chordHalf (3 * N) ≤ 1 / 2 := by
  have hNpos : 0 < N := by linarith
  have h3N : 0 < 3 * N := by linarith
  have hx0 : 0 ≤ Real.pi / (3 * N) := le_of_lt (div_pos Real.pi_pos h3N)
  have hx6 : Real.pi / (3 * N) ≤ Real.pi / 6 := by
    apply (div_le_div_iff₀ h3N (by norm_num : (0 : ℝ) < 6)).2
    nlinarith [mul_le_mul_of_nonneg_left hN (le_of_lt Real.pi_pos)]
  have hxpi : Real.pi / (3 * N) ≤ Real.pi := by
    linarith [Real.pi_pos]
  unfold chordHalf
  constructor
  · exact Real.sin_nonneg_of_nonneg_of_le_pi hx0 hxpi
  · have hmono : Real.sin (Real.pi / (3 * N)) ≤ Real.sin (Real.pi / 6) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hx6
    rw [Real.sin_pi_div_six] at hmono
    exact hmono

/-- The cubic 4u³ − 3u + c = 0 has at most one root in [0, 1/2]. -/
theorem trisection_root_unique (c u v : Real)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (hv0 : 0 ≤ v) (hv1 : v ≤ 1 / 2)
    (hu : 4 * u ^ 3 - 3 * u + c = 0) (hv : 4 * v ^ 3 - 3 * v + c = 0) :
    u = v := by
  have hfac : (u - v) * (4 * (u ^ 2 + u * v + v ^ 2) - 3) = 0 := by
    linear_combination hu - hv
  rcases mul_eq_zero.1 hfac with h1 | h2
  · linarith
  · have huu : u * u ≤ 1 / 2 * u := mul_le_mul_of_nonneg_right hu1 hu0
    have hvv : v * v ≤ 1 / 2 * v := mul_le_mul_of_nonneg_right hv1 hv0
    have huv : u * v ≤ 1 / 2 * v := mul_le_mul_of_nonneg_right hu1 hv0
    have hu' : u = 1 / 2 := by nlinarith
    have hv' : v = 1 / 2 := by nlinarith
    rw [hu', hv']

/-- For N ≥ 2, c_{3N} is the unique root in [0, 1/2] of 4u³ − 3u + c_N = 0. -/
theorem chordHalf_trisection_unique (N u : Real) (hN : 2 ≤ N)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (hu : 4 * u ^ 3 - 3 * u + chordHalf N = 0) :
    u = chordHalf (3 * N) :=
  trisection_root_unique (chordHalf N) u (chordHalf (3 * N)) hu0 hu1
    (chordHalf_trisection_range N hN).1 (chordHalf_trisection_range N hN).2
    hu (chordHalf_trisection N)

end BakerNSeries

#print axioms BakerNSeries.chordHalf_trisection
#print axioms BakerNSeries.chordHalf_trisection_unique
