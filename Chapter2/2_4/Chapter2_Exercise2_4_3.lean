import Mathlib

/-!
# Chapter 2, Exercise 2.4.3: SVD gives orthonormal whitening

## Informal statement

Given the model `x = U z` with SVD `U = P Σ Qᵀ` (where P has orthonormal columns,
Σ is invertible and symmetric, Q is orthogonal), and assuming the empirical covariance
satisfies `Z Zᵀ = I`, we can choose `V = P` so that the whitened matrix satisfies
`(Y Yᵀ)^{-1/2} Y = W Z` where `W = Qᵀ` is an orthonormal matrix.

## Key steps:
1. Choose `V = P` (left singular vectors of U). Then `X = V Y` with `Y = Σ Qᵀ Z`.
2. `Vᵀ V = I` (P has orthonormal columns).
3. Under `Z Zᵀ = I`: `Y Yᵀ = Σ Qᵀ Z Zᵀ Q Σ = Σ (Qᵀ Q) Σ = Σ²`.
4. Take `M_invSqrt = Σ⁻¹`. Then:
   - `Σ⁻¹ * (Y Yᵀ) * (Σ⁻¹)ᵀ = Σ⁻¹ Σ² Σ⁻¹ = I` (whitening condition)
   - `Σ⁻¹ * Y = Σ⁻¹ Σ Qᵀ Z = Qᵀ Z = W Z`
5. `W = Qᵀ` satisfies `W Wᵀ = Qᵀ Q = I`.

See book Chapter 2, Exercise 2.4 (exercise:whitening), part 3.
-/

open Matrix
open scoped BigOperators

noncomputable section

namespace Chapter2Exercise24_3

/--
Exercise 2.4.3: Using the SVD `U = P Σ Qᵀ`, we can choose `V = P` so that the
whitened matrix satisfies `(Y Yᵀ)^{-1/2} Y = W Z` for the orthonormal matrix `W = Qᵀ`.

Here we assume `Z Zᵀ = I` (empirical identity covariance for the latent factors),
which gives `Y Yᵀ = Σ²` and allows `Σ⁻¹` to serve as the whitening operator.
-/
theorem exercise_2_4_3
    (D d N : ℕ)
    (P : Matrix (Fin D) (Fin d) ℝ)    -- left singular vectors
    (Sigma : Matrix (Fin d) (Fin d) ℝ) -- singular values (diagonal)
    (Q : Matrix (Fin d) (Fin d) ℝ)    -- right singular vectors
    (Z : Matrix (Fin d) (Fin N) ℝ)    -- latent factor matrix
    (hP : Pᵀ * P = 1)                 -- P has orthonormal columns
    (hQ_left : Qᵀ * Q = 1)            -- Q is orthogonal (left)
    (hQ_right : Q * Qᵀ = 1)           -- Q is orthogonal (right)
    (hSigma_unit : IsUnit Sigma)       -- Sigma is invertible
    (hSigma_sym : Sigmaᵀ = Sigma)     -- Sigma is symmetric (diagonal)
    (hZZt : Z * Zᵀ = 1) :             -- empirical identity covariance
    let U : Matrix (Fin D) (Fin d) ℝ := P * Sigma * Qᵀ
    let X : Matrix (Fin D) (Fin N) ℝ := U * Z
    let V : Matrix (Fin D) (Fin d) ℝ := P
    let Y : Matrix (Fin d) (Fin N) ℝ := Sigma * Qᵀ * Z
    let W : Matrix (Fin d) (Fin d) ℝ := Qᵀ  -- orthonormal matrix (right singular vectors)
    X = V * Y ∧
    Vᵀ * V = 1 ∧
    W * Wᵀ = 1 ∧
    ∃ (M_invSqrt : Matrix (Fin d) (Fin d) ℝ),
      M_invSqrt * (Y * Yᵀ) * M_invSqrtᵀ = 1 ∧
      M_invSqrt * Y = W * Z := by
  simp only []
  have hSigma_det : IsUnit (det Sigma) := hSigma_unit.map Matrix.detMonoidHom
  have hSigma_inv_l : Sigma⁻¹ * Sigma = 1 :=
    Matrix.nonsing_inv_mul Sigma hSigma_det
  have hSigma_inv_r : Sigma * Sigma⁻¹ = 1 :=
    Matrix.mul_nonsing_inv Sigma hSigma_det
  -- Part 1: X = V * Y, i.e., P * Sigma * Qᵀ * Z = P * (Sigma * Qᵀ * Z)
  have hXVY : P * Sigma * Qᵀ * Z = P * (Sigma * Qᵀ * Z) := by
    rw [Matrix.mul_assoc P, Matrix.mul_assoc P]
  -- Part 2: Vᵀ * V = I is exactly hP
  -- Part 3: W * Wᵀ = Qᵀ * (Qᵀ)ᵀ = Qᵀ * Q = I
  have hWWt : Qᵀ * (Qᵀ)ᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact hQ_left
  -- Key helper: Y * Yᵀ = Sigma * Sigma
  have hYYt : Sigma * Qᵀ * Z * (Sigma * Qᵀ * Z)ᵀ = Sigma * Sigma := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hSigma_sym]
    -- Goal: Sigma * Qᵀ * Z * (Zᵀ * (Q * Sigma)) = Sigma * Sigma
    have : Sigma * Qᵀ * Z * (Zᵀ * (Q * Sigma)) =
           Sigma * (Qᵀ * (Z * Zᵀ) * Q) * Sigma := by
      simp [Matrix.mul_assoc]
    rw [this, hZZt, Matrix.mul_one, hQ_left, Matrix.mul_one]
  -- Part 4a: Whitening condition for M_invSqrt = Sigma⁻¹
  have hwhiten : Sigma⁻¹ * (Sigma * Qᵀ * Z * (Sigma * Qᵀ * Z)ᵀ) * (Sigma⁻¹)ᵀ = 1 := by
    rw [hYYt, Matrix.transpose_nonsing_inv, hSigma_sym]
    -- Goal: Sigma⁻¹ * (Sigma * Sigma) * Sigma⁻¹ = 1
    have : Sigma⁻¹ * (Sigma * Sigma) * Sigma⁻¹ =
           (Sigma⁻¹ * Sigma) * (Sigma * Sigma⁻¹) := by
      simp [Matrix.mul_assoc]
    rw [this, hSigma_inv_l, hSigma_inv_r, Matrix.mul_one]
  -- Part 4b: M_invSqrt * Y = W * Z
  have hMY_WZ : Sigma⁻¹ * (Sigma * Qᵀ * Z) = Qᵀ * Z := by
    have : Sigma⁻¹ * (Sigma * Qᵀ * Z) = (Sigma⁻¹ * Sigma) * Qᵀ * Z := by
      simp [Matrix.mul_assoc]
    rw [this, hSigma_inv_l, Matrix.one_mul]
  exact ⟨hXVY, hP, hWWt, Sigma⁻¹, hwhiten, hMY_WZ⟩

end Chapter2Exercise24_3
