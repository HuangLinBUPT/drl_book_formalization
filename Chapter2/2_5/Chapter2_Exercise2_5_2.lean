/-
# Chapter 2, Exercise 2.5, Part 2: Kurtosis Scaling

## Informal Statement (from Deep Representation Learning book)

Let X be a random variable.

**Part 2:** For any α ∈ ℝ, show that kurt(αX) = α⁴·kurt(X).

## Definition of Kurtosis (from book, equation kurtosis)

For a zero-mean random variable X:
  kurt(X) = E[X⁴] - 3·(E[X²])²

## Reference
Deep Representation Learning book, Chapter 2, Exercise 2.5 (kurtosis-linearity-properties), Part 2
Book source: deep-representation-learning-book/chapters/chapter2/classic-models.tex:2308

## Formalization Notes

The proof expands (αX)⁴ = α⁴·X⁴ and (αX)² = α²·X² pointwise,
then uses linearity of the integral: ∫ α^n·f ∂μ = α^n · ∫ f ∂μ  (integral_const_mul).
Final algebra is handled by ring.

No integrability hypotheses are needed: integral_const_mul holds unconditionally
(both sides are 0 when f is not integrable).
-/

import Chapter2.«2_5».Chapter2_Exercise2_5_1

open ProbabilityTheory MeasureTheory

/-!
## Main Theorem: Kurtosis Scaling
-/

/--
**Exercise 2.5, Part 2 (Main Result):**

For any random variable X and scalar α ∈ ℝ,
  kurt(αX) = α⁴ · kurt(X).

**Proof sketch:**
1. (αX)⁴ = α⁴·X⁴ and (αX)² = α²·X² pointwise (by ring).
2. By linearity of expectation: E[(αX)⁴] = α⁴·E[X⁴] and E[(αX)²] = α²·E[X²].
3. kurt(αX) = α⁴·E[X⁴] - 3·(α²·E[X²])²
            = α⁴·E[X⁴] - 3·α⁴·(E[X²])²
            = α⁴·(E[X⁴] - 3·(E[X²])²)
            = α⁴·kurt(X).

See book Chapter 2, Exercise 2.5, Part 2.
-/
theorem exercise_2_5_part_2
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (X : Ω → ℝ) (α : ℝ) :
    kurtosis (fun ω => α * X ω) μ = α ^ 4 * kurtosis X μ := by
  simp only [kurtosis]
  -- Step 1: E[(αX)⁴] = α⁴·E[X⁴]
  have h4 : ∫ ω, (α * X ω) ^ 4 ∂μ = α ^ 4 * ∫ ω, X ω ^ 4 ∂μ := by
    have : (fun ω => (α * X ω) ^ 4) = (fun ω => α ^ 4 * X ω ^ 4) := by ext ω; ring
    rw [this, integral_const_mul]
  -- Step 2: E[(αX)²] = α²·E[X²]
  have h2 : ∫ ω, (α * X ω) ^ 2 ∂μ = α ^ 2 * ∫ ω, X ω ^ 2 ∂μ := by
    have : (fun ω => (α * X ω) ^ 2) = (fun ω => α ^ 2 * X ω ^ 2) := by ext ω; ring
    rw [this, integral_const_mul]
  -- Step 3: Substitute and conclude by algebra
  rw [h4, h2]
  ring
