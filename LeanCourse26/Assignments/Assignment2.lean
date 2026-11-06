-- Name: Henning Micheel
import Mathlib.Analysis.Complex.Exponential
import Mathlib.FieldTheory.Finite.Basic

open Real Function Set Nat

#click_suggestions

/-
* Hand in the solutions to the exercises below. Deadline: 28.10.2025 at 16:00.
* Solutions from the section `Exercises to hand-in` will receive feedback
  from the tutors.
* None of your solutions should be LLM-generated: doing so will only rob you
  of the practice and waste the tutors' time.
* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

example (p q r s : Prop) (h : p ∧ q → r) (hp : p) (h' : q → s) : q → r ∧ s := by
  intro hq
  have hpq : p ∧ q := by
    constructor
    · exact hp
    · exact hq
  have hr : r := by
    apply h hpq
  have hs : s := by
    apply h' hq
  constructor
  · exact hr
  · exact hs


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by
    intro h'
    obtain ⟨x, hx⟩ := h'
    use x
    apply h
    exact hx

-- Exercise: prove this by contraposition.
example : 2 ≠ 4 → 1 ≠ 2 := by
  contrapose
  intro h
  linarith

/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by
  constructor
  · intro h
    intro x
    intro h'
    apply h
    use x

  · intro h
    intro h'
    obtain ⟨x, hx⟩ := h'
    specialize h x hx
    exact h




/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    constructor
    · use x
      exact hx.1
    exact hx.2
  · intro h
    obtain ⟨hx, hr⟩ := h
    obtain⟨x, hp⟩ := hx
    use x




/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h
    by_contra h'
    specialize h' x
    contradiction
  · intro h
    by_contra h'
    apply h
    intro x
    intro hpx
    apply h'
    exact ⟨x, hpx⟩


def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun _ : ℕ ↦ a) a := by
  unfold SequentialLimit
  intro eps
  intro heps
  use 0
  intro n
  intro hn
  ring_nf
  ring_nf
  exact heps






/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by
  calc
    (n)! ∣ (m)!     := Nat.factorial_dvd_factorial h
    _    ∣ (m + 1)! := by rw [Nat.factorial_succ]; exact dvd_mul_left (m !) (m + 1)

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
  a + exp x ≤ c + exp (y + 2) := by
  have hxy : x ≤ y + 2 := by linarith
  calc
    a + exp x ≤ b + exp x := by linarith
    _ ≤ c + exp x := by linarith
    _ ≤ c + exp (y + 2) := by
      have := Real.exp_le_exp.2 hxy
      linarith

-- Use `rw?` or `#click_suggestions` to help you in the following calculation.
-- Alternatively, write out a calc block by hand.
example {G : Type*} [Group G] {a b c : G}
    (h : a⁻¹ * b * c * c⁻¹ * a * b⁻¹ * a * a⁻¹ = b) (h' : b * a = a * b) : b = 1 := by
  sorry


/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by
  constructor
  · intro h
    have h' : a ≤ c - b := by linarith
    exact h'
  · intro h
    have h' : a + b <= c := by linarith
    exact h'


/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by
  calc
  n - m^2 <= n - 0 := by gcongr; exact sq_nonneg m
  _ <= n + 3 := by linarith

example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  have h2 := h 2
  norm_num at h2
  linarith


/-! # Exercises to hand-in. -/

section Logic
-- Prove the following statements with basic tactics,
-- in particular without using `tauto`, `grind` or lemmas from Mathlib.

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def Continuous' (f : ℝ → ℝ) := ∀ x, ContinuousAtPoint f x

-- Exercise for you. Remember that you can use `unfold` to expand a definition.
example (f g : ℝ → ℝ) (hfg : ∀ x, ContinuousAtPoint f x ↔ ContinuousAtPoint g x) :
    Continuous' f ↔ Continuous' g := by
  unfold Continuous'
  constructor
  · intro hf
    intro x
    apply (hfg x ).1 (hf x)
  · intro hg
    intro x
    apply (hfg x ).2 (hg x)


def All (p : ℝ → Prop) := ∀ x, p x

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    All p ↔ All q := by
  unfold All
  constructor
  · intro px
    intro x
    apply (h x ).1 (px x)
  · intro qx
    intro x
    apply (h x).2 (qx x)





example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    (∃ x, p x) ↔ (∃ x, q x) := by
  constructor
  · intro h'
    obtain ⟨x, px⟩ := h'
    use x
    apply (h x).1
    exact px
  · intro h'
    obtain ⟨x, qx⟩ := h'
    use x
    apply (h x).2
    exact qx



-- Is the following true? If yes, prove it in Lean.
-- If not, give a counterexample and prove it. (What do you have to do to do so?)
example (p q : ℕ → Prop) (h: (∃ x, p x) ↔ (∃ x, q x)) : ∀ x, p x ↔ q x := by
  sorry




/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro h
    obtain ⟨x, pqx⟩ := h
    obtain hp | hq := pqx
    · left
      use x
    . right
      use x
  · intro h
    obtain hp | hq := h
    · obtain ⟨x, px⟩:= hp
      use x
      left
      exact px
    · obtain ⟨x, qx⟩:= hq
      use x
      right
      assumption


end Logic

section Functions

-- Let us investigate the function example from the lecture further.

-- This is how to say "a natural number p is prime" in Mathlib.
#check Nat.Prime

-- The following theorem is the key ingredient to it.
-- (You have not seen the syntax `[hp: Fact (Nat.Prime p)]` yet:
-- this is related to implicit arguments.
-- You can assume it says `(hp: Nat.Prime p)`. We will discuss the precise difference later.)
--
-- Use `exact?`, `apply?` or `#click_suggestions` to find this theorem in Mathlib.
-- Describe what you are doing.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (x : ZMod p) : x ^ p = x := by
  exact ZMod.pow_card x

-- The above theorem has a name. What is it?
-- Use this name to find the same result using leansearch.net.
-- Describe every step you're performing.

-- We go to the definition of `ZMod.pow_card`: hover over the theorem,
-- right-click and select "Go to definition".
-- This opens the Mathlib file where this theorem is proven. The theorem's doc-string says
-- "/-- A variation on Fermat's little theorem. See `ZMod.pow_card_sub_one_eq_one` -/".
-- This is the name of the theorem: Fermat's little theorem.

-- We open leansearch.net, type "Fermat's little theorem" as a query and press search.
-- The fourth result we get is `ZMod.pow_card x`, with the description
-- "Fermat's Little Theorem in Z/pZ: x^p=x"


-- Use `exact?` to find the following theorem in Mathlib.
example (p : ℕ) [hp: Fact (Nat.Prime p)] (k : ZMod p) (hk : k ≠ 0) : k ^ (p - 1) = 1 := by
  exact ZMod.pow_card_sub_one_eq_one hk

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] :
    (fun x ↦ x ^ p + 2 * x ^ (2 * (p - 1) + 1) : ZMod p → ZMod p) = (fun x ↦ 3 * x) := by
  sorry

-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (3 * (p - 1) + 1) = k := by
  sorry

example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (5 * (p - 1) + 1) = k := by
  sorry

end Functions


/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by
  unfold SequentialLimit
  intro ε
  intro hε
  unfold SequentialLimit at hs ht
  have hε2 : ε / 2 > 0 := by positivity
  obtain ⟨N1, hN1⟩ := hs (ε / 2) hε2
  obtain ⟨N2, hN2⟩ := ht (ε / 2) hε2
  let N := max N1 N2
  use N
  intro n hn
  have hn1 : n ≥ N1 := le_trans (le_max_left N1 N2) hn
  have hn2 : n ≥ N2 := le_trans (le_max_right N1 N2) hn
  have hs_n := hN1 n hn1
  have ht_n := hN2 n hn2
  ring_nf
  have h : s n + t n - a - b = (s n - a) + (t n - b) := by ring
  rw [h]
  calc
    |(s n - a) + (t n - b)| ≤ |s n - a| + |t n - b| := by exact abs_add_le (s n - a) (t n - b)
    _ < ε / 2 + ε / 2 := add_lt_add hs_n ht_n
    _ = ε := by ring

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  by_cases h :c = 0
  · unfold SequentialLimit
    intro ε hε
    use 0
    intro n hn
    rw [h]
    ring_nf
    rw [abs_zero]
    linarith
  · unfold SequentialLimit
    unfold SequentialLimit at hs
    have hc_abs : 0 < |c| := abs_pos.2 h
    intro ε hε
    have hε_c : 0 < ε / |c| := div_pos hε hc_abs
    obtain ⟨N, hN⟩ := hs (ε / |c|) hε_c
    use N
    intro n hn
    ring_nf
    rw [← mul_sub]
    rw [abs_mul]
    exact (lt_div_iff₀' hc_abs).mp (hN n hn)















/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by
  sorry





section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  unfold EventuallyGrowsFaster
  simp
  intro k
  use k
  intro n hnk
  exact Nat.mul_le_mul_right (s n) hnk

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  unfold EventuallyGrowsFaster at *
  intro k
  simp
  obtain ⟨N1, hN1⟩ := h₁ k
  obtain ⟨N2, hN2⟩ := h₂ k
  use max N1 N2
  intro n hn
  have hn1 : n ≥ N1 := le_trans (le_max_left N1 N2) hn
  have hn2 : n ≥ N2 := le_trans (le_max_right N1 N2) hn
  ring_nf
  exact Nat.add_le_add (hN1 n hn1) (hN2 n hn2)

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  sorry




end Growth
