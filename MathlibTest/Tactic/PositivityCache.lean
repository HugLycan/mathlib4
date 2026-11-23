module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Tactic.Positivity

/-! # Tests for the `positivity` cache

`trace.Tactic.positivity.cache` prints one line for every lookup that is answered from the cache.
-/

namespace Cache

/-! ### Repeated subterms are analysed only once -/

/--
trace: [Tactic.positivity.cache] cached: x => nonnegative
[Tactic.positivity.cache] cached: x + x => nonnegative
-/
#guard_msgs in
set_option trace.Tactic.positivity.cache true in
example {x : ℤ} (hx : 0 ≤ x) : 0 ≤ (x + x) + (x + x) := by positivity

example {x : ℤ} (hx : 0 ≤ x) :
    0 ≤ ((((x + x) + (x + x)) + ((x + x) + (x + x))) + ((((x + x) + (x + x)) + ((x + x) + (x + x))))
        + (((x + x) + (x + x)) + ((x + x) + (x + x))) + ((((x + x) + (x + x)) + ((x + x) + (x + x)))))
  := by positivity

example {x : ℤ} (hx : 0 ≤ x) :
    0 ≤ x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x
        + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x + x
  := by positivity

/-! ### Failures are cached too, and a cached failure is still a failure -/

/-- trace: [Tactic.positivity.cache] cached: y => none -/
#guard_msgs in
set_option trace.Tactic.positivity.cache true in
example {y : ℤ} : 0 ≤ |y| + |y + 2| := by positivity

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x y : ℤ} (hx : 0 ≤ x) : 0 ≤ (y + x) * (y + x) := by positivity

/-! ### The cache survives a failing extension

The extension for `x + y` fails, since nothing is known about `y`, but the result for `x` that
was found on the way is still available afterwards. -/

/-- trace: [Tactic.positivity.cache] cached: x => positive -/
#guard_msgs in
set_option trace.Tactic.positivity.cache true in
example {x y : ℤ} (hx : 0 < x) : 0 < |x + y| + x := by positivity

/-! ### Results found without a `PartialOrder` are kept apart from those found with one

`ℂ` has no `PartialOrder` instance here, so for `(t : ℂ)` the `Nat.cast` extension asks whether
`t ≠ 0` *without* an order, and the answer is `nonzero`. For `(t : ℤ)` it asks about the same `t`
*with* the order on `ℕ`, and needs the answer `positive`. So the first answer must not be reused
for the second question. -/

example (t : ℕ) (c : ℤ) (ht : t ≠ 0) (hc : c ≠ 0) :
    (t : ℂ) * (((t : ℤ) * c : ℤ) : ℂ) * (((t : ℤ) * (c * c) : ℤ) : ℂ) ≠ 0 := by positivity

example (t : ℕ) (c : ℤ) (ht : t ≠ 0) (hc : c ≠ 0) :
    (t : ℂ) * (((t : ℤ) * c : ℤ) : ℂ) ≠ 0 := by positivity

example (t : ℕ) (c : ℤ) (ht : t ≠ 0) (hc : c ≠ 0) :
    (((t : ℤ) * c : ℤ) : ℂ) * (t : ℂ) ≠ 0 := by positivity

/-! ### The cache is shared with subterms under a binder -/

/--
trace: [Tactic.positivity.cache] cached: x => nonnegative
[Tactic.positivity.cache] cached: x + x => nonnegative
-/
#guard_msgs in
set_option trace.Tactic.positivity.cache true in
example {x : ℤ} (hx : 0 ≤ x) (s : Finset ℕ) : 0 ≤ ∑ i ∈ s, ((x + x) + (i : ℤ)) + (x + x) := by
  positivity

/-! ### The cache survives a `positivity_lemma` that does not apply

In `ℝ≥0∞` the lemma `mul_pos` does not apply, as there is no `PosMulStrictMono ℝ≥0∞` instance.
For a product, `positivity` proves the premises of `mul_pos`, fails to apply it, and goes on with
`mul_nonneg` and `mul_ne_zero`, which are about the same two factors. If the failure discarded the
cache entries of the premises, every further factor would double the work, and the following
example would time out. -/

open scoped ENNReal in
example {x : ℝ≥0∞} (hx : 0 < x) :
    0 < x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x * x := by
  positivity

end Cache
