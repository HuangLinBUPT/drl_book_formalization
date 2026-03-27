/-
  深度表征学习 第2章 练习2.3.1

  GL(d)对称性：证明对于模型 X = UZ，若 A 是任意同阶可逆方阵，
  则 (UA, A⁻¹Z) 也满足模型，即 (UA)(A⁻¹Z) = X。
-/

import Mathlib

/-!
# Exercise 2.3.1: GL(d) Symmetry of the Linear Model

Given the model X = UZ for matrices of compatible sizes,
we show that if A is any square invertible matrix,
then the pair (UA, A⁻¹Z) also produces X.

This demonstrates a fundamental symmetry (non-identifiability)
of the linear representation model.
-/

open Matrix

noncomputable section

namespace Chapter2Exercise23_1

variable {D d N : Type*} [Fintype D] [Fintype d] [Fintype N]
variable [DecidableEq D] [DecidableEq d] [DecidableEq N]

set_option linter.unusedSectionVars false

/--
GL(d) Symmetry Theorem:
If X = UZ under the linear model, then for any invertible square matrix A,
the pair (UA, A⁻¹Z) also satisfies (UA)(A⁻¹Z) = X.
-/
theorem gl_d_symmetry
    (U : Matrix D d ℝ)
    (Z : Matrix d N ℝ)
    (A : Matrix d d ℝ)
    (hA : IsUnit A.det) :
    (U * A) * (A⁻¹ * Z) = U * Z := by
  rw [Matrix.mul_assoc U A (A⁻¹ * Z)]
  rw [← Matrix.mul_assoc A A⁻¹ Z]
  have h := Matrix.mul_nonsing_inv A hA
  rw [h, Matrix.one_mul]

/--
Alternative statement: The model is invariant under GL(d) transformations.
Given X = UZ, for any invertible A, we have X = (UA)(A⁻¹Z).
-/
theorem model_invariance_under_GLd
    (X : Matrix D N ℝ)
    (U : Matrix D d ℝ)
    (Z : Matrix d N ℝ)
    (hModel : X = U * Z)
    (A : Matrix d d ℝ)
    (hA : IsUnit A.det) :
    X = (U * A) * (A⁻¹ * Z) := by
  rw [hModel]
  exact (gl_d_symmetry U Z A hA).symm

/--
The set of pairs (U', Z') satisfying X = U'Z' forms an orbit
under the action of GL(d). This shows non-uniqueness of the factorization.
-/
theorem factorization_non_uniqueness
    (X : Matrix D N ℝ)
    (U : Matrix D d ℝ)
    (Z : Matrix d N ℝ)
    (hModel : X = U * Z)
    (A : Matrix d d ℝ)
    (hA : IsUnit A.det) :
    ∃ U' Z', X = U' * Z' ∧ U' = U * A ∧ Z' = A⁻¹ * Z := by
  use U * A, A⁻¹ * Z
  constructor
  · exact model_invariance_under_GLd X U Z hModel A hA
  constructor
  · rfl
  · rfl

end Chapter2Exercise23_1
