/-
  Module G -- the canonical constructible tableau certificate.

  Composes the verified per-level residual bounds of the canonical schedule with
  the verified canonical-weight tableau result, giving

      | T~_10 - T_10 |  <=  13 / 10^86  =  1.3 x 10^(-85)

  UNCONDITIONALLY: no assumed residual budget, no abstract residuals, no
  abstract weights.  Every input is the actual 4:3 geometric construction and
  every weight is the actual Richardson vector.

  WHY THE CONSTANT IS 13/10^86.  `canonical_constructible_tableau` takes
  `tau = (10/13) * Bcon`, because the budget closes as
  `tau * sum|w_j| <= (10/13) * Bcon * (13/10) = Bcon`.  The schedule certifies
  `tau = 10^(-85)`, so

      (10/13) * Bcon = 10^(-85)   <=>   Bcon = (13/10) * 10^(-85) = 13/10^86.

  The `13/10` factor is the majorant for `sum_j |w_j| = 1.2852105863...`, proved
  in `canonicalWeight_abs_sum_le`.

  WHAT IS STILL MISSING.  This bounds the distance from the CONSTRUCTED tableau
  value to the EXACT tableau value `T_10`.  Reaching `pi` needs
  `|T_10 - pi| <= B_an`, which is Theorem 6.1 of the manuscript -- proved there
  by exact rational interval propagation and a closed sine remainder, but not
  yet formalized.  `canonical_tableau_vs_pi` below takes that bound as an
  explicit hypothesis, so the remaining obligation is stated precisely rather
  than hidden.

  NOT COMPILED.
-/
import NSeriesCanonicalLadder

namespace BakerNSeries

open BakerSeed

/-- The constructed tableau value: the Richardson combination of the chord
estimates produced by the canonical scheduled ladder. -/
noncomputable def canonicalTableauConstructed : ℝ :=
  ∑ j ∈ Finset.range 11,
    ((canonicalWeight j : ℚ) : ℝ)
      * (ladderM j * Real.sin (schedLadder canonicalSchedule j))

/-- The exact tableau value: the same combination of the ideal chord values. -/
noncomputable def canonicalTableauExact : ℝ :=
  ∑ j ∈ Finset.range 11,
    ((canonicalWeight j : ℚ) : ℝ) * (ladderM j * Real.sin (target j))

/-- **The canonical constructible tableau certificate.**

`|T~_10 - T_10| <= 1.3 x 10^(-85)`, unconditionally. -/
theorem canonical_tableau_certified :
    |canonicalTableauConstructed - canonicalTableauExact| ≤ 13 / 10 ^ 86 := by
  unfold canonicalTableauConstructed canonicalTableauExact
  refine canonical_constructible_tableau
    (schedLadder canonicalSchedule) (schedResidual canonicalSchedule)
    (schedLadder_isLadder canonicalSchedule)
    (err_schedLadder_zero canonicalSchedule)
    (13 / 10 ^ 86) (by norm_num) ?_
  intro j hj1 hj10
  have h := canonical_residual_bounds j hj1 hj10
  have heq : ((10 : ℝ) / 13) * (13 / 10 ^ 86) = 1 / 10 ^ 85 := by
    norm_num
  rw [heq]
  exact h

/-- The combined estimate, with Theorem 6.1's analytic bound as an explicit
hypothesis.

This is the precise remaining obligation: supply `B_an` with
`|T_10 - pi| <= B_an` and the constructible lane is certified against `pi` end
to end.  The manuscript proves `B_an = 3.40628574228490542 x 10^(-81)`; only its
formalization is outstanding. -/
theorem canonical_tableau_vs_pi (Ban : ℝ)
    (hBan : |canonicalTableauExact - Real.pi| ≤ Ban) :
    |canonicalTableauConstructed - Real.pi| ≤ 13 / 10 ^ 86 + Ban := by
  have hsplit : canonicalTableauConstructed - Real.pi
      = (canonicalTableauConstructed - canonicalTableauExact)
        + (canonicalTableauExact - Real.pi) := by ring
  calc |canonicalTableauConstructed - Real.pi|
      = |(canonicalTableauConstructed - canonicalTableauExact)
          + (canonicalTableauExact - Real.pi)| := by rw [hsplit]
    _ ≤ |canonicalTableauConstructed - canonicalTableauExact|
          + |canonicalTableauExact - Real.pi| := abs_add_le _ _
    _ ≤ 13 / 10 ^ 86 + Ban := by
        exact add_le_add canonical_tableau_certified hBan

/-- Instantiated at the manuscript's `B_an`, for the record.  Still conditional
on Theorem 6.1: the hypothesis is exactly what that theorem supplies. -/
theorem canonical_tableau_vs_pi_manuscript
    (hBan : |canonicalTableauExact - Real.pi|
      ≤ 341 / 10 ^ 83) :
    |canonicalTableauConstructed - Real.pi| ≤ 342 / 10 ^ 83 := by
  have h := canonical_tableau_vs_pi (341 / 10 ^ 83) hBan
  have hnum : (13 : ℝ) / 10 ^ 86 + 341 / 10 ^ 83 ≤ 342 / 10 ^ 83 := by
    norm_num
  exact le_trans h hnum

end BakerNSeries

/-! ## Axiom audit -/
#print axioms BakerNSeries.canonical_tableau_certified
#print axioms BakerNSeries.canonical_tableau_vs_pi
#print axioms BakerNSeries.canonical_tableau_vs_pi_manuscript
