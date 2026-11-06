import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.FieldTheory.Finite.Basic

open Real (exp sin continuous_sin exp_le_exp)
noncomputable section
variable (a b c : ℝ)

/-
# Practical remarks
* *eCampus is down* due to PHP vulnerability. Deadline for assignment 1
  will be extended. Stay tuned for updates.
* As last time: the lecture is posted in advance of class,
  so you can open the file yourself during class.
* To get the latest version of this repository,
  follow the instructions in the README file.
-/


/- # Last time -/
/- Last time we saw how to deal with logic: if and only if, disjunction, exists and negation

Need to be precise about logical connectives, phrases like "to prove `A ∧ B` we have to prove
`A` and `B`." are awkward but necessary.

Overview of the most important connectives:

→   \to     if ... then ...           implication
∀   \all    for all                   universal quantification
∃   \ex     there exists              existential quantification
¬   \not    not                       negation
∧   \and    and                       conjunction
∨   \or     or                        disjunction
↔   \iff    ... if and only iff ...   biimplication
False       contradiction!            falsity
True        this is trivial           truth

... and how to use them:

            appearing as hypothesis `h`                appearing as goal
`A → B`     `have h' := h ha`, `apply h`               `intro ha`
`∀ x, P x`  `have h' := h x`, `apply h`, `specialize`  `intro x`

`A ∧ B`     `obtain ⟨ha, hb⟩ := h`, `h.1`, `h.2`       `constructor`
`∃ x. P x`  `obtain ⟨x, hx⟩ := h`                      `constructor` or `use x`

`False`     `contradiction`                            --
`True`      --                                         `trivial`

`A ↔ B`     `obtain ⟨h₁, h₂⟩ := h`                     `constructor`
-/

/- # Disjunction
Lean denotes by `∨` the logical OR operator.

In order to directly prove a goal `P ∨ Q`,
we use either the `left` tactic and prove `P` or the `right`
tactic and prove `Q`.

In order to make use of an assumption
  `h : P ∨ Q`
we use the obtain tactic:
  `r`
which creates two proof branches: one branch assuming `hP : P`,
and one branch assuming `hQ : Q`.
-/

#check (mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0)

example : a = a * b → a = 0 ∨ b = 1 := by
  intro h
  have H : a*(b-1) = 0 := by linarith
  rw [mul_eq_zero] at H
  obtain ha | hb := H
  · left
    assumption
  · right
    linarith -- tactic that can close goals about linear (in)equalities



def Injective (f : ℝ → ℝ) : Prop := ∀ x y : ℝ, f x = f y → x = y

#check (lt_trichotomy a b : a < b ∨ a = b ∨ b < a)

example (f : ℝ → ℝ) (hf : StrictMono f) : Injective f := by
  intro x y h
  obtain h_lt | h_eq | h_gt := lt_trichotomy x y
  · specialize hf h_lt
    linarith
  · assumption
  · specialize hf h_gt
    linarith

/- Sometimes you have multiple goals with very similar proofs.
The syntax `<;>` means "apply the following tactic to all goals"
-/
example : 1 = 1 ∧ 2 = 2 := by
  constructor <;>
  rfl

/- ## Negation
The negation `¬ A` just means `A → False`,
where `False` is a statement without a proof.
We can use the same tactics as for implication:
`intro` to prove a negation, and `apply` to use one. -/

example {p : Prop} (h : p) : ¬ ¬ p := by
  intro hnp
  apply hnp
  assumption

example {α : Type*} {p : α → Prop} : ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by
  constructor
  · intro h x hnp
    apply h
    exact ⟨x, hnp⟩
  · intro h hn
    obtain ⟨x, hx⟩ := hn
    specialize h x
    apply h
    assumption


/- We can use `exfalso` to use the fact that
everything follows from `False`: ex falso quod libet -/
example {p : Prop} (h : ¬ p) : p → 0 = 1 := by
  intro hp
  exfalso
  apply h
  exact hp



/- `contradiction` proves any goal
when two hypotheses are contradictory. -/
example {p : Prop} (h : ¬ p) : p → 0 = 1 := by
  intro hp
  contradiction





/- ## Logic (concluded): classical reasoning
We can use classical reasoning (with the law of the excluded middle)
using the following tactics.

* `by_contra h` start a proof by contradiction.
* `by_cases h : p` to start a proof by cases on statement `p`.
* `push Not` to push negations inside quantifiers and connectives.
-/

example (p : Prop) (h : ¬¬p) : p := by
  by_contra hnp
  apply h
  assumption

example (p q : Prop) (h : ¬q → ¬p) : p → q := by
  intro hp
  by_contra hnq
  specialize h hnq
  apply h
  assumption

example (p r : Prop) (h1 : p → r) (h2 : ¬ p → r) : r := by
  by_cases h : p
  --case 1: h : p
  · apply h1
    exact h
  --case 2: h : ¬p
  · apply h2
    exact h

example {α : Type*} {p : α → α → Prop} :
    ¬ (∃ x y, p x y) ↔ ∀ x y, ¬ p x y := by
  push Not
  rfl

/-
Note the difference between adding and removing a negation.
For the former (going from `hp : P` to `¬P`), we use `intro` in Lean.
For the latter (going from `hp : ¬P` to `P`),
we need to use `by_contra` to begin a proof by contradiction.
(In constructive mathematics, these are different.)
-/

/- The `contrapose` tactic starts a proof by contraposition -/
example (p q : Prop) (h : ¬q → ¬p) : p → q := by
  contrapose
  assumption

example : 2 ≠ 4 → 1 ≠ 2 := by
  contrapose
  intro h
  contradiction


/-- The sequence `u` of real numbers converges to `l`.
`∀ ε > 0, ...` means `∀ ε, ε > 0 → ...` -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (u : ℕ → ℝ) (l : ℝ) : ¬ SequentialLimit u l ↔
    ∃ ε > 0, ∀ N, ∃ n ≥ N, |u n - l| ≥ ε := by
  unfold SequentialLimit
  push Not
  rfl

lemma sequentialLimit_unique (u : ℕ → ℝ) (l l' : ℝ) :
    SequentialLimit u l → SequentialLimit u l' → l = l' := by
  intro hl hl'
  by_contra h : l ≠ l'
  have H : |l - l'| > 0 := by exact abs_sub_pos.mpr h -- found with exact?
  specialize hl (|l - l'|/2) (by linarith)
  specialize hl' (|l - l'|/2) (by exact?)
  obtain ⟨N, hN⟩ := hl
  obtain ⟨N', hN'⟩ := hl'
  let N₀ := max N N'
  specialize hN N₀ (by exact Nat.le_max_left N N')
  specialize hN' N₀ (by exact?)
  have key := calc
    |l - l'| = |(u N₀ - l') - (u N₀ - l)| := by ring_nf
           _ ≤ |u N₀ - l'| + |u N₀ - l| := by exact abs_sub (u N₀ - l') (u N₀ - l)
           _ < |l - l'| := by linarith
  linarith



/- ## Refine tactic
The tactic `refine` behaves like `exact`, except you can leave
`?_` placeholders, which create new goals of the appropriate type.
This is very useful for writing more compact code.
-/

example (p q r : Prop) (h : p → q) (h' : q → r) : p → p ∧ q ∧ r := by
  -- intro hp
  -- refine ⟨?_, ?_, ?_⟩
  -- · exact hp
  -- · exact h hp
  -- · refine h' ?_
  --   exact h hp
  intro hp
  refine ⟨hp, h hp, h' (h hp)⟩

-- END OF LECTURE

/- ## Proving two functions are equal
To prove that two functions `f g : α → β` are equal, you can prove that they are equal at every
point, using the `ext` tactic. `ext x` can prove that `f = g` if `f x = g x` for a new variable `x`.
-/

example {α β : Type*} {f g : α → β} (h : ∀ x, f x = g x) : f = g := by
  sorry

-- `rfl` can prove an equality `f = f`,
example : (fun n ↦ n + 2 : ℤ → ℤ) = (fun n ↦ n + 2 : ℤ → ℤ) := rfl

-- but once two functions are not "obviously" equal, you need `ext` to prove it.
example : (fun n ↦ n + 2 : ℤ → ℤ) = (fun n ↦ n + 2 + 0 : ℤ → ℤ) := by
  sorry

example : (fun n ↦ 2 * n : ℤ → ℤ) = (fun n ↦ n + n) := by
  sorry

example : (fun (n : ℤ) ↦ 2 * n + 5) = (fun (n : ℤ) ↦ (n + 2) + (n + 6) - 3) := by
  sorry

/- # Finding Lemmas
* Use tactics with a question mark to find a lemma.
  - `exact?` tries to apply a *single* lemma from the library to prove the current goal.
  - `simp?` simplifies the goal using `simp` and prints all used lemmas.

* The command `#click_suggestions` lets you shift-click on subexpressions in
  the infoview, and gives a list of possible rewrites.

* Use `#leansearch "<query>."` to query theorems in natural language.
  Or use its website https://leansearch.net/

* Guess the name of the lemma
  - You can search lemmas in the API documentation:
    https://leanprover-community.github.io/mathlib4_docs/
  - When typing a name, a list of suggested completions automatically shows up
  - You can also press `ctrl-space` (or `cmd-space` on a Mac) to see the list of suggestions.
  - Pressing `ctrl-space` toggles the display of the documentation of the selected completion.
  - You can also press `ctrl-T` (or `cmd-T`) to search for a lemma name
    (choosing an option shows you where it is proven)

  Some naming conventions:
  - a theorem named `A_of_B_of_C` establishes something of the form `A`
    from hypotheses of the form `B` and `C`.
  - `A`, `B`, and `C` approximate the way we might read the statement out loud.
  - Example: a theorem showing `x + y ≤ ...` will probably start with `add_le`.
    After typing `add_le` the autocomplete will give you some helpful choices.

* You can browse Mathlib
If you ctrl-click on a definition or theorem in VS Code you will jump
to the file where the theorem is proven.
You can often find similar theorems nearby the theorem you searched for.
-/

#click_suggestions



example (a b x y : ℝ) (h : a < b) (h2 : x ≤ y) : a + exp x < b + exp y := by
  sorry


/- In the following lemma, notice that `a`, `b`, `c`
are inside curly braces `{...}`.
This means that these arguments are *implicit*:
they don't have to be stated, but will be figured out by Lean automatically. -/


lemma cancel_addition {a b c : ℝ} (h : a + b = a + c) : b = c := by
  sorry

lemma cancel_addition' (a b c : ℝ) (h : a + b = a + c) : b = c := by
  sorry

example {b c : ℝ} (h : 2 + b = 2 + c) : b = c := by
  sorry

/- {G : Type*} and [Group G] are both implicit arguments.
The difference will be discussed later. -/

example {G : Type*} [Group G] (a : G) : a * a⁻¹ = 1 := by
  sorry

-- Let's see how `#click_suggestions` works on a more complicated example.
-- Note that I cannot select two terms on the left: multiplication is left-associative, so
-- a * b * c means (a * b) * c.
example {G : Type*} [Group G] (a : G) : a⁻¹ * a * a * a⁻¹ = 1 := by
  sorry

-- You can also click on terms in hypotheses.
example {G : Type*} [Group G] {a b : G} (h : a⁻¹ * a * a * a⁻¹ = b) : b = 1 := by
  sorry

example (x : ℝ) : (3 * (x - x))^2 = 0 := by
  sorry

/- # Orders -/

section Real
variable {a b c d e x y z : ℝ}

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_antisymm : a ≤ b → b ≤ a → a = b)


/- We can apply these lemmas manually, or use the `rfl`/`trans`/`calc` tactics. -/

example (x : ℝ) : x ≤ x := by exact le_refl x
example (x : ℝ) : x ≤ x := by apply le_refl
example (x : ℝ) : x ≤ x := by rfl

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry

/- `linarith` can prove inequalities (and equalities)
  that follow from linear combinations of assumptions. -/

example (h₀ : a = b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry

example (x y z : ℝ) (hx : x ≤ 3 * y) (h2 : ¬ y > 2 * z)
    (h3 : x ≥ 6 * z) : x = 3 * y := by
  sorry


/- Mathlib has lemmas that all common operations are monotone. Here are a few examples. -/

#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (mul_le_mul : a ≤ b → c ≤ d → 0 ≤ c → 0 ≤ b → a * c ≤ b * d)
#check (mul_le_mul_of_nonneg_right : b ≤ c → 0 ≤ a → b * a ≤ c * a)

example (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 ≤ c) : a * (b + 2) ≤ (a + c) * (b + 2) := by
  sorry

/- `gcongr` is very convenient for monotonicity of functions. -/

example (h : a ≤ b) (h2 : b ≤ c) : exp a ≤ exp c := by
  sorry

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry

example (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 0 ≤ c) : a * (b + 2) ≤ (a + c) * (b + 2) := by
  sorry

/- Remark: for equalities, you should use `congr` instead of `gcongr` -/

example (h : a = b) : c - exp b = c - exp a := by
  sorry

/- `grw` can be used to rewrite with more general relations than `=` and `↔`: for example,
inequalities or congruence relations -/

example {a b c d : ℤ} (h₁ : a < b) (h₂ : b ≤ c) : a + d ≤ c + d := by
  sorry

#check 10 ≡ 2 [ZMOD 5]

example {a b n : ℤ} (h : a ≡ b [ZMOD n]) : a ^ 2 ≡ b ^ 2 [ZMOD n] := by
  sorry

example {a b c d n : ℤ} (h : a ≡ b [ZMOD n]) (h' : c ≡ d [ZMOD n]) :
    a ^ 2 * c ≡ b ^ 2 * d [ZMOD n] := by
  sorry

example {a b c : ℤ} (h₁ : a ∣ b) (h₂ : b ∣ a ^ 2 * c) : a ∣ b ^ 2 * c := by
  sorry

example (h₁ : a + e ≤ b + e) (h₂ : b < c) (h₃ : c ≤ d) : a + e < d + e := by
  sorry

example (f g : ℝ → ℝ) (h : ∀ x : ℝ, f x ≤ g x) (h₂ : g a + g b ≤ 5) : f a + f b ≤ 5 := by
  sorry
