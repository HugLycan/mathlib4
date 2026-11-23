import Mathlib.Tactic.Positivity.Core

/-! # Tests for the `positivity_lemma` attribute

The attribute is global, so a lemma tagged in one section stays active in the later ones. Each
section therefore uses its own functions: otherwise a test could pass thanks to a lemma of an
earlier section.

`trace.Tactic.positivity.lemma` prints the lemmas that `positivity` applies, in order.
-/

axiom α : Type
axiom β : Type

section

variable [Zero α] [PartialOrder α] [Zero β] [PartialOrder β]

namespace Basic

axiom c : α
axiom f : α → α
axiom g : α → β
axiom m : α → α → α

@[positivity_lemma]
axiom c_pos : 0 < c

@[positivity_lemma]
axiom f_pos {x : α} : 0 < x → 0 < f x

@[positivity_lemma]
axiom f_nonneg {x : α} : 0 ≤ x → 0 ≤ f x

@[positivity_lemma]
axiom f_ne_zero {x : α} : x ≠ 0 → f x ≠ 0

@[positivity_lemma]
axiom zero_ne_g {x : α} : 0 ≠ x → g x ≠ 0

@[positivity_lemma]
axiom g_pos {n : α} : 0 < n → 0 < g n

@[positivity_lemma]
axiom m_pos {x y : α} : 0 < x → 0 < y → 0 < m x y

@[positivity_lemma]
axiom m_nonneg {x y : α} : 0 ≤ x → 0 ≤ y → 0 ≤ m x y

example : 0 < c := by positivity
example {x : α} (hx : 0 < x) : 0 < f x := by positivity
example {x : α} (hx : 0 ≤ x) : 0 ≤ f x := by positivity
example {x : α} (hx : x ≠ 0) : f x ≠ 0 := by positivity
example {x : α} (hx : x ≠ 0) : 0 ≠ f x := by positivity
example {x : α} (hx : 0 ≠ x) : f x ≠ 0 := by positivity
example {x : α} (hx : 0 ≠ x) : 0 ≠ f x := by positivity
example {n : α} (hn : 0 < n) : 0 < g n := by positivity

example {x : α} (hx : x ≠ 0) : g x ≠ 0 := by positivity
example {x : α} (hx : x ≠ 0) : 0 ≠ g x := by positivity
example {x : α} (hx : 0 ≠ x) : g x ≠ 0 := by positivity
example {x : α} (hx : 0 ≠ x) : 0 ≠ g x := by positivity

example {x y : α} (hx : 0 < x) (hy : 0 < y) : 0 < m x y := by positivity
example {x y : α} (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ m x y := by positivity
example {x : α} (hx : 0 ≤ x) : 0 ≤ m x x := by positivity
example {x y : α} (hx : 0 < x) (hy : 0 ≤ y) : 0 ≤ m (f x) (m y (f c)) := by positivity

/-- trace: [Tactic.positivity.lemma] f x: applied f_pos -/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < f x := by positivity

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x : α} : 0 ≤ f x := by positivity

/--
error: failed to prove strict positivity, but it would be possible to prove nonnegativity if desired
-/
#guard_msgs in
example {x : α} (hx : 0 ≤ x) : 0 < f x := by positivity

end Basic

namespace GtGe

/-! The conclusion and the premises may be stated with `>` and `≥`. -/

axiom f : α → α

@[positivity_lemma]
axiom f_pos {x : α} : x > 0 → f x > 0

@[positivity_lemma]
axiom f_nonneg {x : α} : x ≥ 0 → f x ≥ 0

example {x : α} (hx : 0 < x) : 0 < f x := by positivity
example {x : α} (hx : x > 0) : f x > 0 := by positivity
example {x : α} (hx : 0 ≤ x) : 0 ≤ f x := by positivity

end GtGe

namespace Combine

/-! The results of several lemmas are combined: `0 ≤ f x` and `f x ≠ 0` give `0 < f x`. A proof of
`0 < x` is accepted for the premises `0 ≤ x` and `x ≠ 0`. -/

axiom f : α → α

@[positivity_lemma]
axiom f_ne_zero {x : α} : x ≠ 0 → f x ≠ 0

@[positivity_lemma]
axiom f_nonneg {x : α} : 0 ≤ x → 0 ≤ f x

/--
trace: [Tactic.positivity.lemma] f x: applied f_nonneg
[Tactic.positivity.lemma] f x: applied f_ne_zero
-/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < f x := by positivity

end Combine

namespace Order

/-! ### The order in which lemmas are tried -/

/-! A higher priority comes first. -/

axiom f : α → α

@[positivity_lemma low]
axiom f_pos_low {x : α} : 0 < x → 0 < f x

@[positivity_lemma high]
axiom f_pos_high {x : α} : 0 < x → 0 < f x

@[positivity_lemma]
axiom f_pos_default {x : α} : 0 < x → 0 < f x

/-- trace: [Tactic.positivity.lemma] f x: applied f_pos_high -/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < f x := by positivity

/-! For equal priorities, `<` comes before `≤`, which comes before `≠`, whatever the order in
which the lemmas were tagged. -/

axiom g : α → α

@[positivity_lemma]
axiom g_ne_zero {x : α} : x ≠ 0 → g x ≠ 0

@[positivity_lemma]
axiom g_nonneg {x : α} : 0 ≤ x → 0 ≤ g x

@[positivity_lemma]
axiom g_pos {x : α} : 0 < x → 0 < g x

/-- trace: [Tactic.positivity.lemma] g x: applied g_pos -/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < g x := by positivity

/-! Otherwise, the lemma that was tagged first comes first. -/

axiom h : α → α

@[positivity_lemma]
axiom h_pos₁ {x : α} : 0 < x → 0 < h x

@[positivity_lemma]
axiom h_pos₂ {x : α} : 0 < x → 0 < h x

/-- trace: [Tactic.positivity.lemma] h x: applied h_pos₁ -/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < h x := by positivity

/-! The priority takes precedence over the kind of the conclusion. -/

axiom k : α → α

@[positivity_lemma]
axiom k_pos {x : α} : 0 < x → 0 < k x

@[positivity_lemma high]
axiom k_nonneg {x : α} : 0 ≤ x → 0 ≤ k x

/--
trace: [Tactic.positivity.lemma] k x: applied k_nonneg
[Tactic.positivity.lemma] k x: applied k_pos
-/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < k x := by positivity

/-! Tagging a lemma again replaces its entry. -/

attribute [positivity_lemma low] k_nonneg

/-- trace: [Tactic.positivity.lemma] k x: applied k_pos -/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < k x := by positivity

end Order

namespace Instances

/-! Instance arguments are found by instance synthesis. A lemma with a missing instance is skipped,
and the other lemmas are still tried. -/

class Good (α : Type*) : Prop where
  adorable : True

class Bad (α : Type*) : Prop where
  horrible : False

instance : Good α := ⟨⟨⟩⟩

axiom f : α → α
axiom g : α → α

@[positivity_lemma]
axiom f_pos [Good α] {x : α} : 0 < x → 0 < f x

example {x : α} (hx : 0 < x) : 0 < f x := by positivity

@[positivity_lemma high]
axiom g_pos_bad [Bad α] {x : α} : 0 < x → 0 < g x

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x : α} (hx : 0 < x) : 0 < g x := by positivity

@[positivity_lemma]
axiom g_pos [Good α] {x : α} : 0 < x → 0 < g x

/-- trace: [Tactic.positivity.lemma] g x: applied g_pos -/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example {x : α} (hx : 0 < x) : 0 < g x := by positivity

end Instances

namespace PremiseWithoutZero

/-! If the argument of a premise has a type without `Zero`, that lemma is skipped,
but the other lemmas for the same head are still tried. -/

axiom γ : Type
axiom k {δ : Type} : δ → α

@[positivity_lemma high]
axiom k_pos {δ : Type} [Zero δ] [PartialOrder δ] {x : δ} : 0 < x → 0 < k x

@[positivity_lemma low]
axiom k_pos' {δ : Type} {x : δ} : 0 < k x

/-- trace: [Tactic.positivity.lemma] k x: applied k_pos' -/
#guard_msgs in
set_option trace.Tactic.positivity.lemma true in
example (x : γ) : 0 < k x := by positivity

end PremiseWithoutZero

namespace NoOrder

/-! Without an order, only the lemmas about `≠` are used. -/

axiom γ : Type
axiom zγ : Zero γ
attribute [instance] zγ
axiom f : γ → γ
axiom g : α → γ

@[positivity_lemma]
axiom f_ne_zero {x : γ} : x ≠ 0 → f x ≠ 0

@[positivity_lemma]
axiom g_ne_zero {x : α} : 0 ≤ x → g x ≠ 0

example {x : γ} (hx : x ≠ 0) : f x ≠ 0 := by positivity
example {x : γ} (hx : x ≠ 0) : 0 ≠ f (f x) := by positivity
example {x : α} (hx : 0 < x) : f (g x) ≠ 0 := by positivity

end NoOrder

namespace Unfold

/-! The head of the expression is unfolded with reducible transparency. -/

axiom f : α → α

noncomputable abbrev f' (x : α) : α := f x

noncomputable def f'' (x : α) : α := f x

@[positivity_lemma]
axiom f_pos {x : α} : 0 < x → 0 < f x

example {x : α} (hx : 0 < x) : 0 < f' x := by positivity

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x : α} (hx : 0 < x) : 0 < f'' x := by positivity

end Unfold

namespace AutoParam

axiom f : α → α

@[positivity_lemma]
axiom f_pos {x : α} (hx : 0 < x := by assumption) : 0 < f x

example {x : α} (hx : 0 < x) : 0 < f (f x) := by positivity

end AutoParam

namespace Scoped

axiom f : α → α
axiom g : α → α

namespace Inner

@[scoped positivity_lemma]
axiom f_pos {x : α} : 0 < x → 0 < f x

example {x : α} (hx : 0 < x) : 0 < f x := by positivity

end Inner

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x : α} (hx : 0 < x) : 0 < f x := by positivity

section

@[local positivity_lemma]
axiom g_pos {x : α} : 0 < x → 0 < g x

example {x : α} (hx : 0 < x) : 0 < g x := by positivity

end

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x : α} (hx : 0 < x) : 0 < g x := by positivity

end Scoped

namespace OtherInstance

/-! A premise about another order than the one found by instance synthesis is not satisfied by
what `positivity` proves. The lemma is then skipped. -/

axiom f : α → α
axiom otherOrder : PartialOrder α

@[positivity_lemma]
axiom f_pos {x : α} (h : @LT.lt α otherOrder.toLT 0 x) : 0 < f x

/-- error: failed to prove positivity/nonnegativity/nonzeroness -/
#guard_msgs in
example {x : α} (hx : 0 < x) : 0 < f x := by positivity

end OtherInstance

namespace Rejected

/-! ### Lemmas that the attribute rejects -/

axiom f : α → α
axiom f₂ : (x : α) → 0 < x → α
axiom P : α → Prop

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The premise P x is not a positivity proposition
-/
#guard_msgs in
@[positivity_lemma]
axiom f_pos {x : α} : P x → 0 < x → 0 < f x

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The conclusion 0 < g x does not have a constant head
-/
#guard_msgs in
@[positivity_lemma]
axiom variable_head {g : α → α} {x : α} : 0 < x → 0 < g x

/-! An argument that the conclusion does not determine would be left over as a goal. -/

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The argument y is not determined by the conclusion 0 ≤ f x
-/
#guard_msgs in
@[positivity_lemma]
axiom undetermined_implicit {x y : α} : 0 ≤ x → 0 ≤ f x

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The argument n is not determined by the conclusion 0 < f x
-/
#guard_msgs in
@[positivity_lemma]
axiom undetermined_explicit (n : ℕ) {x : α} : 0 < x → 0 < f x

/-! The proof of a premise is not known when the lemma is unified with the goal. -/

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The conclusion 0 < f₂ x hx or the type of another argument depends on the proof of the premise 0 < x
-/
#guard_msgs in
@[positivity_lemma]
axiom dependent_premise {x : α} (hx : 0 < x) : 0 < f₂ x hx

end Rejected

end

namespace Rejected

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The conclusion a < 0 is not a positivity proposition
-/
#guard_msgs in
@[positivity_lemma]
theorem neg_pos' {a : ℤ} : 0 < -a → a < 0 := Int.neg_pos.mp

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The premise a < 0 is not a positivity proposition
-/
#guard_msgs in
@[positivity_lemma]
theorem neg_pos'' {a : ℤ} : a < 0 → 0 < -a := by exact fun a_1 => Int.neg_pos_of_neg a_1

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The conclusion a < 0 ↔ 0 < -a is not a positivity proposition
-/
#guard_msgs in
@[positivity_lemma]
theorem neg_pos''' {a : ℤ} : a < 0 ↔ 0 < -a := by exact Iff.symm Int.neg_pos

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The premise 0 < a + b does not refer to a direct argument of the conclusion 0 < a - b
-/
#guard_msgs in
@[positivity_lemma]
axiom not_direct_arg {a b : ℤ} : 0 < a + b → 0 < a - b

/--
error: @[positivity_lemma] attribute only applies to lemmas proving
0 [</≤/≠] f x₁ ... xₙ or f x₁ ... xₙ [>/≥/≠] 0.
The argument c is not determined by the conclusion 0 < a - b
-/
#guard_msgs in
@[positivity_lemma]
axiom not_an_arg {a b c : ℤ} : 0 < c → 0 < a - b

end Rejected
