/-
# Chapter 2, Exercise 2.5, Part 1: Kurtosis Additivity

## Informal Statement (from Deep Representation Learning book)

Let X and Y be zero-mean independent random variables.

**Part 1:** Show that kurt(X + Y) = kurt(X) + kurt(Y).

## Definition of Kurtosis (from book, equation kurtosis)

For a zero-mean random variable X:
  kurt(X) = E[X⁴] - 3·(E[X²])²

## Reference
Deep Representation Learning book, Chapter 2, Exercise 2.5 (kurtosis-linearity-properties), Part 1
Book source: deep-representation-learning-book/chapters/chapter2/classic-models.tex:2308

## Formalization Notes

The proof expands (X+Y)⁴ and (X+Y)² and uses:
- Independence: E[f(X)·g(Y)] = E[f(X)]·E[g(Y)]
- Zero-mean: E[X] = 0, E[Y] = 0

Key moment cancellations:
- E[X³Y] = E[X³]·E[Y] = 0          (independence + E[Y]=0)
- E[XY³] = E[X]·E[Y³] = 0          (independence + E[X]=0)
- E[X²Y²] = E[X²]·E[Y²]             (independence)
- E[XY] = E[X]·E[Y] = 0             (independence + zero mean)

After these substitutions, the algebra reduces by ring.
-/

import Mathlib

open ProbabilityTheory MeasureTheory

/-!
## Kurtosis Definition

The kurtosis of a (zero-mean) random variable X is defined as the fourth
central moment minus three times the square of the second moment.
-/

/-- 峰度（kurtosis）定义：对于零均值随机变量 X，kurt(X) = E[X⁴] - 3·(E[X²])²。
    这是衡量分布"尖峭程度"的四阶统计量。-/
noncomputable def kurtosis {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  ∫ ω, X ω ^ 4 ∂μ - 3 * (∫ ω, X ω ^ 2 ∂μ) ^ 2

/-!
## Key Moment Lemmas

We first establish the four moment identities needed for the main theorem.
Each uses independence of X and Y, plus the zero-mean assumptions.
-/

/-- 对独立零均值随机变量，E[X·Y] = 0。
    Proof: E[XY] = E[X]·E[Y] = 0·0 = 0 by independence. -/
lemma integral_mul_of_indepFun_zero_mean
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hI : IndepFun X Y μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0) :
    ∫ ω, X ω * Y ω ∂μ = 0 := by
  have h := IndepFun.integral_mul_eq_mul_integral hI
    hXm.aestronglyMeasurable hYm.aestronglyMeasurable
  simp only [Pi.mul_apply] at h
  rw [h, hX0, hY0, zero_mul]

/-- 对独立随机变量，E[X³·Y] = 0（若 E[Y] = 0）。
    Proof: E[X³Y] = E[X³]·E[Y] = E[X³]·0 = 0 by independence. -/
lemma integral_cube_mul_of_indepFun_zero_mean_right
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hI : IndepFun X Y μ)
    (hY0 : ∫ ω, Y ω ∂μ = 0) :
    ∫ ω, X ω ^ 3 * Y ω ∂μ = 0 := by
  -- X^3 ⟂ᵢ Y since X ⟂ᵢ Y and x ↦ x^3 is measurable
  have hI' : IndepFun (fun ω => X ω ^ 3) Y μ := by
    simpa using hI.comp (measurable_id.pow_const 3) measurable_id
  have h := IndepFun.integral_mul_eq_mul_integral hI'
    (hXm.pow_const 3).aestronglyMeasurable hYm.aestronglyMeasurable
  simp only [Pi.mul_apply] at h
  rw [h, hY0, mul_zero]

/-- 对独立随机变量，E[X·Y³] = 0（若 E[X] = 0）。
    Proof: E[XY³] = E[X]·E[Y³] = 0·E[Y³] = 0 by independence. -/
lemma integral_mul_cube_of_indepFun_zero_mean_left
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hI : IndepFun X Y μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) :
    ∫ ω, X ω * Y ω ^ 3 ∂μ = 0 := by
  -- X ⟂ᵢ Y^3 since X ⟂ᵢ Y and y ↦ y^3 is measurable
  have hI' : IndepFun X (fun ω => Y ω ^ 3) μ := by
    simpa using hI.comp measurable_id (measurable_id.pow_const 3)
  have h := IndepFun.integral_mul_eq_mul_integral hI'
    hXm.aestronglyMeasurable (hYm.pow_const 3).aestronglyMeasurable
  simp only [Pi.mul_apply] at h
  rw [h, hX0, zero_mul]

/-- 对独立随机变量，E[X²·Y²] = E[X²]·E[Y²]。
    Proof: X² ⟂ᵢ Y² by measurability of squaring, then factorize integral. -/
lemma integral_sq_mul_sq_of_indepFun
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    (hI : IndepFun X Y μ) :
    ∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ = (∫ ω, X ω ^ 2 ∂μ) * ∫ ω, Y ω ^ 2 ∂μ := by
  -- x ↦ x^2 is measurable, so X^2 ⟂ᵢ Y^2
  have hI2 : IndepFun (fun ω => X ω ^ 2) (fun ω => Y ω ^ 2) μ := by
    simpa using hI.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have h := IndepFun.integral_mul_eq_mul_integral hI2
    (hXm.pow_const 2).aestronglyMeasurable (hYm.pow_const 2).aestronglyMeasurable
  simp only [Pi.mul_apply] at h
  exact h

/-!
## Integral Linearity Helper

Expand ∫ (X+Y)^4 ∂μ into individual moment integrals.
-/

/-- 展开 ∫ (X+Y)⁴ 为各分量矩的线性组合。-/
private lemma integral_fourth_moment_expand
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (X Y : Ω → ℝ)
    (hX4 : Integrable (fun ω => X ω ^ 4) μ)
    (hX3Y : Integrable (fun ω => X ω ^ 3 * Y ω) μ)
    (hX2Y2 : Integrable (fun ω => X ω ^ 2 * Y ω ^ 2) μ)
    (hXY3 : Integrable (fun ω => X ω * Y ω ^ 3) μ)
    (hY4 : Integrable (fun ω => Y ω ^ 4) μ) :
    ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)
          + 4 * (X ω * Y ω ^ 3) + Y ω ^ 4) ∂μ =
    ∫ ω, X ω ^ 4 ∂μ + 4 * ∫ ω, X ω ^ 3 * Y ω ∂μ
    + 6 * ∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ + 4 * ∫ ω, X ω * Y ω ^ 3 ∂μ
    + ∫ ω, Y ω ^ 4 ∂μ := by
  -- Split off Y^4 last
  have s4 : ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) ∂μ =
      ∫ ω, X ω ^ 4 ∂μ + 4 * ∫ ω, X ω ^ 3 * Y ω ∂μ := by
    have h := integral_add hX4 (hX3Y.const_mul 4)
    simp only [integral_const_mul] at h ⊢
    convert h using 1
  have s3 : ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)) ∂μ =
      ∫ ω, X ω ^ 4 ∂μ + 4 * ∫ ω, X ω ^ 3 * Y ω ∂μ
      + 6 * ∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ := by
    have h := integral_add (hX4.add (hX3Y.const_mul 4)) (hX2Y2.const_mul 6)
    simp only [integral_const_mul] at h ⊢
    linarith [s4, (by convert h using 1 :
      ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)) ∂μ
      = ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω)) ∂μ + 6 * ∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ)]
  have s2 : ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)
               + 4 * (X ω * Y ω ^ 3)) ∂μ =
      ∫ ω, X ω ^ 4 ∂μ + 4 * ∫ ω, X ω ^ 3 * Y ω ∂μ
      + 6 * ∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ + 4 * ∫ ω, X ω * Y ω ^ 3 ∂μ := by
    have h := integral_add ((hX4.add (hX3Y.const_mul 4)).add (hX2Y2.const_mul 6))
                           (hXY3.const_mul 4)
    simp only [integral_const_mul] at h ⊢
    linarith [s3, (by convert h using 1 :
      ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)
               + 4 * (X ω * Y ω ^ 3)) ∂μ
      = ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)) ∂μ
        + 4 * ∫ ω, X ω * Y ω ^ 3 ∂μ)]
  have s1 := integral_add
      (((hX4.add (hX3Y.const_mul 4)).add (hX2Y2.const_mul 6)).add (hXY3.const_mul 4)) hY4
  linarith [s2, (by convert s1 using 1 :
    ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)
              + 4 * (X ω * Y ω ^ 3) + Y ω ^ 4) ∂μ
    = ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)
              + 4 * (X ω * Y ω ^ 3)) ∂μ + ∫ ω, Y ω ^ 4 ∂μ)]

/-!
## Main Theorem: Kurtosis Additivity
-/

/--
**Exercise 2.5, Part 1 (Main Result):**

For independent zero-mean random variables X and Y,
  kurt(X + Y) = kurt(X) + kurt(Y).

**Proof sketch:**
1. Expand (X+Y)⁴ = X⁴ + 4X³Y + 6X²Y² + 4XY³ + Y⁴.
2. Taking expectation and using independence + zero-mean:
   E[(X+Y)⁴] = E[X⁴] + 0 + 6·E[X²]·E[Y²] + 0 + E[Y⁴].
3. Similarly, E[(X+Y)²] = E[X²] + E[Y²] (since E[XY] = 0).
4. The kurtosis additivity follows by algebra.

See book Chapter 2, Exercise 2.5, Part 1.
-/
theorem exercise_2_5_part_1
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (X Y : Ω → ℝ)
    (hXm : Measurable X) (hYm : Measurable Y)
    -- Independence
    (hI : IndepFun X Y μ)
    -- Zero-mean conditions
    (hX0 : ∫ ω, X ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0)
    -- Integrability of all needed moments
    (hX4 : Integrable (fun ω => X ω ^ 4) μ)
    (hY4 : Integrable (fun ω => Y ω ^ 4) μ)
    (hX3Y : Integrable (fun ω => X ω ^ 3 * Y ω) μ)
    (hXY3 : Integrable (fun ω => X ω * Y ω ^ 3) μ)
    (hX2Y2 : Integrable (fun ω => X ω ^ 2 * Y ω ^ 2) μ)
    (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hY2 : Integrable (fun ω => Y ω ^ 2) μ)
    (hXY : Integrable (fun ω => X ω * Y ω) μ) :
    kurtosis (fun ω => X ω + Y ω) μ = kurtosis X μ + kurtosis Y μ := by
  -- Step 1: E[XY] = 0 (independence + zero mean)
  have hEXY0 : ∫ ω, X ω * Y ω ∂μ = 0 :=
    integral_mul_of_indepFun_zero_mean X Y hXm hYm hI hX0 hY0
  -- Step 2: E[X³Y] = 0 (independence + E[Y]=0)
  have hEX3Y0 : ∫ ω, X ω ^ 3 * Y ω ∂μ = 0 :=
    integral_cube_mul_of_indepFun_zero_mean_right X Y hXm hYm hI hY0
  -- Step 3: E[XY³] = 0 (independence + E[X]=0)
  have hEXY30 : ∫ ω, X ω * Y ω ^ 3 ∂μ = 0 :=
    integral_mul_cube_of_indepFun_zero_mean_left X Y hXm hYm hI hX0
  -- Step 4: E[X²Y²] = E[X²]·E[Y²] (independence)
  have hEX2Y2 : ∫ ω, X ω ^ 2 * Y ω ^ 2 ∂μ = (∫ ω, X ω ^ 2 ∂μ) * ∫ ω, Y ω ^ 2 ∂μ :=
    integral_sq_mul_sq_of_indepFun X Y hXm hYm hI
  -- Step 5: Compute E[(X+Y)⁴] = E[X⁴] + 6·E[X²]·E[Y²] + E[Y⁴]
  have hE4 : ∫ ω, (X ω + Y ω) ^ 4 ∂μ =
      ∫ ω, X ω ^ 4 ∂μ + 6 * ((∫ ω, X ω ^ 2 ∂μ) * ∫ ω, Y ω ^ 2 ∂μ) + ∫ ω, Y ω ^ 4 ∂μ := by
    have expand : ∫ ω, (X ω + Y ω) ^ 4 ∂μ =
        ∫ ω, (X ω ^ 4 + 4 * (X ω ^ 3 * Y ω) + 6 * (X ω ^ 2 * Y ω ^ 2)
              + 4 * (X ω * Y ω ^ 3) + Y ω ^ 4) ∂μ :=
      integral_congr_ae (ae_of_all μ (fun ω => by ring))
    linarith [expand, integral_fourth_moment_expand X Y hX4 hX3Y hX2Y2 hXY3 hY4,
              hEX3Y0, hEXY30, hEX2Y2]
  -- Step 6: Compute E[(X+Y)²] = E[X²] + E[Y²]
  have hE2 : ∫ ω, (X ω + Y ω) ^ 2 ∂μ = ∫ ω, X ω ^ 2 ∂μ + ∫ ω, Y ω ^ 2 ∂μ := by
    have expand : ∫ ω, (X ω + Y ω) ^ 2 ∂μ =
        ∫ ω, (X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2) ∂μ :=
      integral_congr_ae (ae_of_all μ (fun ω => by ring))
    have h2 := integral_add (hX2.add (hXY.const_mul 2)) hY2
    have h3 : ∫ ω, (X ω ^ 2 + 2 * (X ω * Y ω)) ∂μ =
        ∫ ω, X ω ^ 2 ∂μ + 2 * ∫ ω, X ω * Y ω ∂μ := by
      rw [integral_add hX2 (hXY.const_mul 2), integral_const_mul]
    linarith [hEXY0, expand,
              (by convert h2 using 1 : ∫ ω, (X ω ^ 2 + 2 * (X ω * Y ω) + Y ω ^ 2) ∂μ
               = ∫ ω, (X ω ^ 2 + 2 * (X ω * Y ω)) ∂μ + ∫ ω, Y ω ^ 2 ∂μ)]
  -- Final assembly: plug in computed moments and use algebra
  -- kurt(X+Y) = E[(X+Y)⁴] - 3·(E[(X+Y)²])²
  --           = (E[X⁴] + 6·E[X²]·E[Y²] + E[Y⁴]) - 3·(E[X²]+E[Y²])²
  --           = (E[X⁴] - 3·(E[X²])²) + (E[Y⁴] - 3·(E[Y²])²)
  --           = kurt(X) + kurt(Y)
  simp only [kurtosis, hE4, hE2]
  ring
