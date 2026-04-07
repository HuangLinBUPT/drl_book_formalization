/-
  Deep Representation Learning, Exercise 2.2

  Prove: For a Gaussian random variable z ~ N(0, sigma^2 I),
  any orthogonal matrix Q (satisfying Q^T Q = I) preserves the distribution,
  i.e., Qz has the same distribution as z.

  This is the rotational invariance of the isotropic Gaussian distribution.

  Proof approach: we show the density function is invariant under Q,
  by proving the squared Euclidean norm is preserved: (Qx) . (Qx) = x . x.
  See: Deep Representation Learning, Exercise 2.2
-/

import Mathlib

open Real Matrix

noncomputable section

namespace Chapter2Exercise22

variable {d : ℕ}

/-! ## Definitions -/

/-- An orthogonal matrix satisfies Q^T Q = I. -/
def IsOrthogonal (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Qᵀ * Q = 1

/-- The squared Euclidean norm: ||x||^2 = sum_i x_i^2.

We define this via dot product (x . x) rather than using the default norm on
`Fin d -> R`, which is the sup norm, not the Euclidean norm. -/
def euclidNormSq (x : Fin d → ℝ) : ℝ := x ⬝ᵥ x

/-- The density of the isotropic Gaussian N(0, sigma^2 I) in R^d:
    f(x) = (2 pi sigma^2)^(-d/2) * exp(-||x||^2 / (2 sigma^2)). -/
def gaussianDensity (σ : ℝ) (x : Fin d → ℝ) : ℝ :=
  (2 * π * σ ^ 2) ^ (-(d : ℝ) / 2) * exp (-euclidNormSq x / (2 * σ ^ 2))

/-! ## Key Lemmas -/

/-- Orthogonal matrices preserve the squared Euclidean norm: ||Qx||^2 = ||x||^2.

Proof: (Qx)^T (Qx) = x^T Q^T Q x = x^T I x = x^T x. -/
theorem orthogonal_preserves_euclidNormSq {Q : Matrix (Fin d) (Fin d) ℝ}
    (hQ : IsOrthogonal Q) (x : Fin d → ℝ) :
    euclidNormSq (Q.mulVec x) = euclidNormSq x := by
  unfold euclidNormSq
  -- Goal: Q.mulVec x ⬝ᵥ Q.mulVec x = x ⬝ᵥ x
  -- Step 1: Pull Q out of the right factor using dotProduct_mulVec
  rw [Matrix.dotProduct_mulVec]
  -- Goal: vecMul (Q.mulVec x) Q ⬝ᵥ x = x ⬝ᵥ x
  -- Step 2: It suffices to show vecMul (Q.mulVec x) Q = x
  congr 1
  -- Step 3: Rewrite Q = (Q^T)^T so we can apply vecMul_transpose
  rw [show Q = Qᵀᵀ from (Matrix.transpose_transpose Q).symm]
  rw [Matrix.vecMul_transpose]
  -- Goal: Q^T.mulVec ((Q^T)^T.mulVec x) = x
  -- Step 4: Combine the two mulVec into (Q^T * (Q^T)^T).mulVec x
  rw [Matrix.mulVec_mulVec]
  -- Step 5: Simplify (Q^T)^T = Q, apply hQ, and use one_mulVec
  rw [Matrix.transpose_transpose, hQ, Matrix.one_mulVec]

/-- The determinant of an orthogonal matrix has absolute value 1.

From Q^T Q = I: det(Q^T) det(Q) = 1, hence det(Q)^2 = 1, so |det(Q)| = 1. -/
theorem orthogonal_det_abs_one {Q : Matrix (Fin d) (Fin d) ℝ}
    (hQ : IsOrthogonal Q) : |Q.det| = 1 := by
  -- Step 1: Show det(Q)^2 = 1
  have h : Q.det ^ 2 = 1 := by
    have := calc Qᵀ.det * Q.det
        = (Qᵀ * Q).det := (Matrix.det_mul Qᵀ Q).symm
      _ = (1 : Matrix (Fin d) (Fin d) ℝ).det := by rw [hQ]
      _ = 1 := Matrix.det_one
    rwa [Matrix.det_transpose, ← sq] at this
  -- Step 2: From |det(Q)|^2 = det(Q)^2 = 1 and |det(Q)| >= 0, deduce |det(Q)| = 1
  have h_abs_sq : |Q.det| ^ 2 = 1 := by rwa [sq_abs]
  have h_nonneg : 0 ≤ |Q.det| := abs_nonneg _
  nlinarith [sq_nonneg (|Q.det| - 1)]

/-! ## Main Theorem -/

/-- **Exercise 2.2**: The isotropic Gaussian density is invariant under
orthogonal transformations.

If Q is orthogonal (Q^T Q = I), then for all x in R^d:
  gaussianDensity sigma (Qx) = gaussianDensity sigma (x).

This follows immediately from ||Qx||^2 = ||x||^2. -/
theorem gaussian_rotational_invariance (σ : ℝ)
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsOrthogonal Q)
    (x : Fin d → ℝ) :
    gaussianDensity σ (Q.mulVec x) = gaussianDensity σ x := by
  simp only [gaussianDensity, orthogonal_preserves_euclidNormSq hQ]

end Chapter2Exercise22
