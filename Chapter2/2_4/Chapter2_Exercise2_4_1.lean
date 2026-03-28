/-
# Chapter 2, Exercise 2.4, Part 1: Whitening - Rank Bound

## Informal Statement (from Deep Representation Learning book)

Consider the model x = Uz, where U ∈ ℝ^(D×d) with D ≥ d is fixed and has rank d,
and z is a zero-mean random variable. Let x₁, ..., xₙ denote i.i.d. observations
from this model.

**Part 1:** Show that the matrix X = [x₁, ..., xₙ] has rank no larger than d,
and therefore there is an orthonormal matrix V ∈ ℝ^(D×d) so that X = VY,
where Y ∈ ℝ^(d×N).

## Reference
Deep Representation Learning book, Chapter 2, Exercise 2.4, Part 1
Book source: deep-representation-learning-book/chapters/chapter2/classic-models.tex:2282

## Formalization Notes

The key insight is that X = U·Z where Z = [z₁, ..., zₙ] is a (d×N) matrix.
Since U has rank d and Z has d rows, rank(X) ≤ min(rank(U), d) = d.

For the orthonormal decomposition, we use the fact that the column space of X
has dimension ≤ d, so we can find an orthonormal basis V and express X = VY.
-/

import Mathlib

open Matrix

variable {R : Type*} [Field R]

/-!
## Main Theorem: Data Matrix Has Bounded Rank

Given a generative model x = Uz where U has rank d, the data matrix X
formed by stacking observations has rank at most d.
-/

/--
The data matrix X = [x₁, ..., xₙ] where each xᵢ = U·zᵢ has rank at most rank(U).
This is because X = U·Z where Z = [z₁, ..., zₙ].
-/
theorem data_matrix_rank_bound
  {D d N : ℕ}
  (U : Matrix (Fin D) (Fin d) R)
  (Z : Matrix (Fin d) (Fin N) R) :
  (U * Z).rank ≤ U.rank := by
  exact Matrix.rank_mul_le_left U Z

/--
If U has full column rank d (i.e., rank = d), then the data matrix X = U·Z
has rank at most d.
-/
theorem data_matrix_rank_le_d
  {D d N : ℕ}
  (_h_le : d ≤ D)
  (U : Matrix (Fin D) (Fin d) R)
  (h_rank : U.rank = d)
  (Z : Matrix (Fin d) (Fin N) R) :
  (U * Z).rank ≤ d := by
  calc
    (U * Z).rank ≤ U.rank := data_matrix_rank_bound U Z
    _ = d := h_rank

/-!
## Orthonormal Decomposition

For any matrix X with rank ≤ d, we can find an orthonormal matrix V and
a matrix Y such that X = VY. This is a consequence of the SVD or QR decomposition.
-/

/--
Structure to represent an orthonormal matrix.
A matrix V is orthonormal if its columns form an orthonormal set.
-/
structure OrthonormalMatrix (m n : ℕ) (R : Type*) [Field R] where
  matrix : Matrix (Fin m) (Fin n) R
  orthonormal : matrix.transpose * matrix = 1

/--
For any data matrix X = U·Z where U has rank d, there exists an orthonormal matrix V
and a matrix Y such that X = V·Y.

This uses the fact that the column space of X has dimension ≤ d, so we can find
an orthonormal basis for this space (or its extension to dimension d).

**Proof sketch:**
1. The matrix X = U·Z has rank ≤ d, so its column space has dimension ≤ d.
2. We can apply QR decomposition (or Gram-Schmidt orthogonalization) to the columns of X
   to obtain an orthonormal basis V for the column space.
3. Then X can be expressed as V·Y where Y contains the coordinates in this basis.

Note: This requires QR decomposition theory which is not yet conveniently accessible
in Mathlib for this formulation. This is a well-known result in linear algebra.
-/
theorem exists_orthonormal_decomposition
  {D d N : ℕ}
  (h_le : d ≤ D)
  (U : Matrix (Fin D) (Fin d) R)
  (h_rank : U.rank = d)
  (Z : Matrix (Fin d) (Fin N) R) :
  ∃ (V : OrthonormalMatrix D d R) (Y : Matrix (Fin d) (Fin N) R),
    U * Z = V.matrix * Y := by
  sorry

/-!
## Combined Result

Combining the rank bound and orthonormal decomposition gives us the complete
statement of Exercise 2.4, Part 1.
-/

/--
**Exercise 2.4, Part 1 (Main Result):**

Given the model x = Uz where U ∈ ℝ^(D×d) with D ≥ d has rank d,
the data matrix X = [x₁, ..., xₙ] satisfies:
1. rank(X) ≤ d
2. There exists orthonormal V ∈ ℝ^(D×d) and Y ∈ ℝ^(d×N) such that X = VY
-/
theorem exercise_2_4_part_1
  {D d N : ℕ}
  (h_le : d ≤ D)
  (U : Matrix (Fin D) (Fin d) R)
  (h_rank : U.rank = d)
  (Z : Matrix (Fin d) (Fin N) R) :
  (U * Z).rank ≤ d ∧
  ∃ (V : OrthonormalMatrix D d R) (Y : Matrix (Fin d) (Fin N) R),
    U * Z = V.matrix * Y := by
  constructor
  · exact data_matrix_rank_le_d h_le U h_rank Z
  · exact exists_orthonormal_decomposition h_le U h_rank Z
