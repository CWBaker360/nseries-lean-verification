import NSeriesB5ActualBound

namespace BakerNSeries

noncomputable def richardsonC (k : Real) : Real :=
  Real.pi^7 * (k^2 + 1) / (5040 * k^4) +
    (2 * Real.pi^9) / (362880 * (k^2 - 1))

theorem richardson_error_bound
    (N k : Real) (hN : 1 <= N) (hk : 1 < k) :
    abs (nseriesR N k - Real.pi + Real.pi^5 / (120 * k^2 * N^4)) <=
      richardsonC k / N^6 := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hkpos : 0 < k := by linarith
  have hN0 : N ≠ 0 := ne_of_gt hNpos
  have hk0 : k ≠ 0 := ne_of_gt hkpos
  have hdenpos : 0 < k^2 - 1 := by
    nlinarith [sq_nonneg (k - 1)]
  have hden0 : k^2 - 1 ≠ 0 := ne_of_gt hdenpos
  have hNpow : N^6 <= N^8 := by
    have hN6 : 0 <= N^6 := pow_nonneg (le_of_lt hNpos) 6
    have hN2 : 1 <= N^2 := by nlinarith
    calc
      N^6 = N^6 * 1 := by ring
      _ <= N^6 * N^2 := mul_le_mul_of_nonneg_left hN2 hN6
      _ = N^8 := by ring
  have hrecipN : 1 / N^8 <= 1 / N^6 := by
    apply (div_le_div_iff₀ (pow_pos hNpos 8) (pow_pos hNpos 6)).2
    simpa using hNpow
  have hk6 : 1 <= k^6 := by
    have hk1 : 1 <= k := le_of_lt hk
    exact one_le_pow₀ hk1
  have hrecipk : 1 / (k^6 * N^8) <= 1 / N^8 := by
    apply (div_le_div_iff₀
      (mul_pos (pow_pos hkpos 6) (pow_pos hNpos 8)) (pow_pos hNpos 8)).2
    simpa [one_mul] using mul_le_mul_of_nonneg_right hk6
      (pow_nonneg (le_of_lt hNpos) 8)
  have hsum : 1 / (k^6 * N^8) + 1 / N^8 <= 2 / N^6 := by
    calc
      1 / (k^6 * N^8) + 1 / N^8 <= 1 / N^8 + 1 / N^8 :=
        add_le_add_left hrecipk _
      _ <= 1 / N^6 + 1 / N^6 := add_le_add hrecipN hrecipN
      _ = 2 / N^6 := by ring
  have hfactor : 0 <= Real.pi^9 / (362880 * (k^2 - 1)) := by positivity
  have hresidual :
      (k^2 * (Real.pi^9 / (362880 * (k*N)^8))
        + Real.pi^9 / (362880 * N^8)) / (k^2 - 1)
        <= (2 * Real.pi^9) / (362880 * (k^2 - 1) * N^6) := by
    have hrewrite :
        (k^2 * (Real.pi^9 / (362880 * (k*N)^8))
          + Real.pi^9 / (362880 * N^8)) / (k^2 - 1)
        = (Real.pi^9 / (362880 * (k^2 - 1))) *
            (1 / (k^6 * N^8) + 1 / N^8) := by
          field_simp [hN0, hk0, hden0]
    rw [hrewrite]
    calc
      _ <= (Real.pi^9 / (362880 * (k^2 - 1))) * (2 / N^6) :=
        mul_le_mul_of_nonneg_left hsum hfactor
      _ = (2 * Real.pi^9) / (362880 * (k^2 - 1) * N^6) := by
        field_simp [hN0, hk0, hden0]
  have hraw := two_scale_actual_error_bound_raw N k hNpos hk
  calc
    abs (nseriesR N k - Real.pi + Real.pi^5 / (120 * k^2 * N^4))
        <= Real.pi^7 * (k^2 + 1) / (5040 * k^4 * N^6) +
          (k^2 * (Real.pi^9 / (362880 * (k*N)^8))
            + Real.pi^9 / (362880 * N^8)) / (k^2 - 1) := hraw
    _ <= Real.pi^7 * (k^2 + 1) / (5040 * k^4 * N^6) +
          (2 * Real.pi^9) / (362880 * (k^2 - 1) * N^6) :=
      add_le_add_right hresidual _
    _ = richardsonC k / N^6 := by
      dsimp [richardsonC]
      field_simp [hN0, hk0, hden0]

open Asymptotics

theorem richardson_error_isBigO (k : Real) (hk : 1 < k) :
    (fun N : Real => nseriesR N k - Real.pi + Real.pi^5 / (120 * k^2 * N^4))
      =O[Filter.atTop] (fun N : Real => 1 / N^6) := by
  rw [isBigO_iff]
  refine ⟨richardsonC k, Filter.eventually_atTop.2 ⟨1, ?_⟩⟩
  intro N hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNabs : |N| ^ 6 = N^6 := by rw [abs_of_pos hNpos]
  simpa [Real.norm_eq_abs, hNabs, div_eq_mul_inv] using
    richardson_error_bound N k hN hk

end BakerNSeries

#print axioms BakerNSeries.richardson_error_bound
#print axioms BakerNSeries.richardson_error_isBigO
