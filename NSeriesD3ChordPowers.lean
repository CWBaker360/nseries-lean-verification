import NSeriesD2BPrimitive

namespace BakerNSeries

theorem canonicalPolygonStep_pow_chord_length
    (n k : ℕ) (hn : 3 ≤ n) (hk : k ≤ n) :
    dist (1 : ℂ) (canonicalPolygonStep n ^ k) =
      2 * Real.sin (Real.pi * k / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hangle0 : 0 ≤ Real.pi * (k : ℝ) / n := by positivity
  have hanglepi : Real.pi * (k : ℝ) / n ≤ Real.pi := by
    apply (div_le_iff₀ hn0).2
    nlinarith [Real.pi_pos, (show (k : ℝ) ≤ n by exact_mod_cast hk)]
  have hsin : 0 ≤ Real.sin (Real.pi * (k : ℝ) / n) :=
    Real.sin_nonneg_of_mem_Icc ⟨hangle0, hanglepi⟩
  rw [dist_eq_norm_sub]
  have hpow : canonicalPolygonStep n ^ k =
      Complex.exp (Complex.I * ((2 * Real.pi * (k : ℝ) / n : ℝ) : ℂ)) := by
    rw [canonicalPolygonStep, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hpow]
  calc
    ‖1 - Complex.exp (Complex.I * ((2 * Real.pi * (k : ℝ) / n : ℝ) : ℂ))‖
        = ‖Complex.exp (Complex.I * ((2 * Real.pi * (k : ℝ) / n : ℝ) : ℂ)) - 1‖ := by
          rw [← norm_neg]
          congr 1
          ring
    _ = ‖2 * Real.sin ((2 * Real.pi * (k : ℝ) / n) / 2)‖ :=
      Complex.norm_exp_I_mul_ofReal_sub_one _
    _ = 2 * Real.sin (Real.pi * (k : ℝ) / n) := by
      rw [show (2 * Real.pi * (k : ℝ) / n) / 2 = Real.pi * (k : ℝ) / n by ring]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hsin)]

end BakerNSeries

#print axioms BakerNSeries.canonicalPolygonStep_pow_chord_length
