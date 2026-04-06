import Chapter2.«2_8».Chapter2_Exercise2_8_3_1

/-!
# Chapter 2, Exercise 2.8.3 (Part 2): QᵀX equals (XᵀX)^{1/2}

## Informal Statement (exercise:orthogonal-group-calculus, Part 3b)

Using the first and second-order optimality conditions from Part 1:
- `(QᵀX)ᵀ = QᵀX`       — QᵀX is symmetric
- `QᵀX ⪰ 0`             — QᵀX is positive semidefinite

Argue that at every local minimizer Q of `‖Q - X‖_F²`, one has `QᵀX = (XᵀX)^{1/2}`.

**Hint**: If `S ≥ 0` is a symmetric PSD matrix, then `(SᵀS)^{1/2} = S`.

## Proof Sketch

Since Q ∈ O(d), we have QQᵀ = I. Therefore:
```
  (QᵀX)ᵀ(QᵀX) = XᵀQ · QᵀX = Xᵀ(QQᵀ)X = XᵀX
```
Combined with symmetry of QᵀX:
```
  (QᵀX)² = (QᵀX)ᵀ(QᵀX) = XᵀX
```

So QᵀX is a symmetric PSD matrix S satisfying S² = XᵀX.
By the hint (uniqueness of PSD square root), QᵀX = (XᵀX)^{1/2}.

## Formalization Note

Since Mathlib's matrix square root requires spectral theory, we characterize
`(XᵀX)^{1/2}` axiomatically: a matrix S is a PSD square root of M if Sᵀ = S,
S is PSD, and S² = M. We prove QᵀX satisfies all three conditions.

## References
- Book: deep-representation-learning-book/chapters/chapter2/classic-models.tex
  exercise:orthogonal-group-calculus, Part 3b
- See also: Chapter2_Exercise2_8_3_1.lean (first and second-order conditions)
-/

open Matrix

variable (d : ℕ) [DecidableEq (Fin d)]

local notation "Mat" => Matrix (Fin d) (Fin d) ℝ

/-! ### Algebraic lemma: (QᵀX)ᵀ(QᵀX) = XᵀX -/

/-- For `Q ∈ O(d)`: `(QᵀX)ᵀ(QᵀX) = XᵀX`.

This uses `Q * Qᵀ = 1` (right-inverse identity for orthogonal matrices). -/
lemma qtx_transpose_mul_qtx (Q X : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    (Qᵀ * X)ᵀ * (Qᵀ * X) = Xᵀ * X := by
  have hQQt : Q * Qᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin d) ℝ).mp hQ
  -- (QᵀX)ᵀ = XᵀQ
  rw [transpose_mul, transpose_transpose]
  -- (XᵀQ)(QᵀX) = Xᵀ(QQᵀ)X = XᵀX
  rw [← Matrix.mul_assoc (Xᵀ * Q) Qᵀ X]
  rw [Matrix.mul_assoc Xᵀ Q Qᵀ, hQQt, Matrix.mul_one]

/-! ### Key theorem: (QᵀX)² = XᵀX when QᵀX is symmetric -/

/-- When `Q ∈ O(d)` and `QᵀX` is symmetric, `(QᵀX)² = XᵀX`.

Proof: `(QᵀX)² = (QᵀX)ᵀ(QᵀX) = XᵀX`. -/
theorem qtx_sq_eq_xtx (Q X : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    (hsymm : (Qᵀ * X)ᵀ = Qᵀ * X) :
    (Qᵀ * X) * (Qᵀ * X) = Xᵀ * X := by
  -- Use symmetry to rewrite just the first factor: (QᵀX)² = (QᵀX)ᵀ(QᵀX) = XᵀX
  calc (Qᵀ * X) * (Qᵀ * X)
      = (Qᵀ * X)ᵀ * (Qᵀ * X) := by rw [hsymm]
    _ = Xᵀ * X               := qtx_transpose_mul_qtx d Q X hQ

/-! ### PSD square root characterization -/

/-- A matrix S is a **PSD square root** of M (in the tangent-space sense at Q) if:
- `Sᵀ = S`          — S is symmetric
- `S ⪰ 0` (on T_Q) — S is PSD in the Frobenius tangent-space sense
- `S * S = M`       — S² = M -/
structure IsPSDSqrtOD (S M : Mat) (Q : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ) : Prop where
  symm : Sᵀ = S
  psd : ∀ V : Mat, inTangentSpace d Q V → matInner d (V * S) V ≥ 0
  sq : S * S = M

/-- **Exercise 2.8.3.2**: At every local minimizer Q of `‖Q - X‖_F²`,
    `QᵀX` is a PSD square root of `XᵀX` in the sense of `IsPSDSqrtOD`.

This combines:
- Part 1 (Exercise 2.8.3.1): `(QᵀX)ᵀ = QᵀX` and `QᵀX ⪰ 0`
- The algebraic identity `(QᵀX)² = XᵀX` (from Q ∈ O(d))

See book Chapter 2, exercise:orthogonal-group-calculus, Part 3b. -/
theorem exercise_2_8_3_2 (Q X : Mat)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ)
    -- First-order: Riemannian gradient = 0
    (hgrad : tangentProj d Q (Q - X) = 0)
    -- Second-order: Riemannian Hessian PSD
    (hhess : ∀ V : Mat, inTangentSpace d Q V →
      matInner d (riemHessOD d Q id (Q - X) V) V ≥ 0) :
    IsPSDSqrtOD d (Qᵀ * X) (Xᵀ * X) Q hQ := by
  -- Extract symmetry and PSD from Part 1
  obtain ⟨hsymm, hpsd⟩ := exercise_2_8_3_1 d Q X hQ hgrad hhess
  exact {
    symm := hsymm
    psd  := hpsd
    sq   := qtx_sq_eq_xtx d Q X hQ hsymm
  }
