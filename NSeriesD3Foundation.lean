import Mathlib

namespace BakerNSeries

/-- The finite set of nonidentity complex `n`-th roots of unity. -/
noncomputable def nontrivialRoots (n : ℕ) [NeZero n] : Finset (rootsOfUnity n ℂ) :=
  letI : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _
  Finset.univ.filter (fun z => ((z.1 : ℂˣ) : ℂ) ≠ 1)

/-- The π-free finite set of Euclidean chord lengths from `1` to nonidentity roots. -/
noncomputable def rootChordLengths (n : ℕ) [NeZero n] : Finset ℝ :=
  (nontrivialRoots n).image (fun z => dist (1 : ℂ) ((z.1 : ℂˣ) : ℂ))

/-- The intrinsic shortest nonzero root-of-unity chord, given its finite nonemptiness proof. -/
noncomputable def minimumRootChord (n : ℕ) [NeZero n]
    (h : (rootChordLengths n).Nonempty) : ℝ :=
  (rootChordLengths n).min' h

end BakerNSeries
