import Mathlib

namespace BakerNSeries

theorem sine_adjacent_le_sine_multiple
    (n k : ℕ) (hn : 3 ≤ n) (hk1 : 1 ≤ k) (hkn : k < n) :
    Real.sin (Real.pi / n) ≤ Real.sin (Real.pi * k / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hfirst : ∀ m : ℕ, 1 ≤ m → m < n → 2 * m ≤ n →
      Real.sin (Real.pi / n) ≤ Real.sin (Real.pi * m / n) := by
    intro m hm1 hmn htwo
    have hm0 : (0 : ℝ) ≤ m := by positivity
    have hlow : -(Real.pi / 2) ≤ Real.pi / n := by
      exact (neg_nonpos.mpr (by positivity)).trans (le_of_lt (div_pos Real.pi_pos hn0))
    have hmid : Real.pi / n ≤ Real.pi * m / n := by
      apply (div_le_div_iff₀ hn0 hn0).2
      have hmul : Real.pi ≤ Real.pi * (m : ℝ) := by
        exact le_mul_of_one_le_right Real.pi_pos.le (by exact_mod_cast hm1)
      have := mul_le_mul_of_nonneg_right hmul hn0.le
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have hupp : Real.pi * m / n ≤ Real.pi / 2 := by
      apply (div_le_iff₀ hn0).2
      nlinarith [Real.pi_pos, (show (2 : ℝ) * m ≤ n by exact_mod_cast htwo)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two hlow hupp hmid
  by_cases htwo : 2 * k ≤ n
  · exact hfirst k hk1 hkn htwo
  · let j := n - k
    have hk_le : k ≤ n := by omega
    have hj1 : 1 ≤ j := by dsimp [j]; omega
    have hjn : j < n := by dsimp [j]; omega
    have hjtwo : 2 * j ≤ n := by dsimp [j]; omega
    have hbase := hfirst j hj1 hjn hjtwo
    have hangle : Real.pi - Real.pi * k / n = Real.pi * j / n := by
      dsimp [j]
      rw [Nat.cast_sub hk_le]
      field_simp
    have hreflect : Real.sin (Real.pi * j / n) =
        Real.sin (Real.pi * k / n) := by
      rw [← hangle, Real.sin_pi_sub]
    rw [hreflect] at hbase
    exact hbase

end BakerNSeries

#print axioms BakerNSeries.sine_adjacent_le_sine_multiple
