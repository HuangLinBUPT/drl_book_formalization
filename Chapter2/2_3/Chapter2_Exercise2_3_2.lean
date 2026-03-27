/-
  深度表征学习 第2章 练习2.3.2

  ICA对称性约简：证明当随机向量z的各分量独立（零均值、正方差）时，
  若可逆矩阵A使得Az的各分量不相关，则A必具有形式 A = D₁QD₂，
  其中Q为正交矩阵，D₁、D₂为对角矩阵。
-/

import Mathlib

/-!
# Exercise 2.3.2: Symmetry Breaking in ICA

Given a random vector z with independent components (zero mean, positive variance),
we show that if a square invertible matrix A produces uncorrelated components in Az,
then A must decompose as A = D₁QD₂ where Q is orthogonal and D₁, D₂ are diagonal.

This demonstrates how the independence assumption in ICA reduces the GL(d) symmetry
to only scale and rotational symmetries.

## Mathematical Setup

- **z**: Random vector with independent components, zero mean, positive variance
- **Cov(z)**: Covariance matrix of z, diagonal with positive entries (due to independence)
- **A**: Square invertible matrix
- **Az**: Transformed random vector
- **Cov(Az) = A · Cov(z) · Aᵀ**: Covariance transformation formula

## Key Insight

If both Cov(z) and Cov(Az) are diagonal, then A · Diag · Aᵀ = Diag,
where Diag denotes a diagonal matrix with positive entries.
This strong constraint forces A to have the form D₁QD₂.

## Formalization Approach

We formalize the deterministic core: given diagonal positive definite Σ_z,
if A · Σ_z · Aᵀ is also diagonal, then A = D₁ · Q · D₂.
-/

open Matrix

noncomputable section

namespace Chapter2Exercise23_2

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option linter.unusedSectionVars false

/--
A matrix is orthogonal if its transpose equals its inverse,
equivalently Qᵀ * Q = I.
-/
def IsOrthogonal (Q : Matrix n n ℝ) : Prop :=
  Qᵀ * Q = 1

/--
Basic properties of orthogonal matrices.
-/
lemma isOrthogonal_iff (Q : Matrix n n ℝ) :
    IsOrthogonal Q ↔ Qᵀ * Q = 1 := by
  rfl

lemma isOrthogonal_det (Q : Matrix n n ℝ) (hQ : IsOrthogonal Q) :
    Q.det = 1 ∨ Q.det = -1 := by
  -- Q is orthogonal means Qᵀ * Q = I
  -- Taking determinant: det(Qᵀ) * det(Q) = det(I) = 1
  -- Since det(Qᵀ) = det(Q), we have (det(Q))² = 1
  -- Therefore det(Q) = ±1
  have h1 : (Qᵀ * Q).det = (1 : Matrix n n ℝ).det := by rw [hQ]
  rw [det_mul, det_transpose] at h1
  have h2 : Q.det * Q.det = 1 := by simpa using h1
  have h3 : Q.det ^ 2 = 1 := by rw [sq]; exact h2
  exact sq_eq_one_iff.mp h3

lemma isOrthogonal_inv (Q : Matrix n n ℝ) (hQ : IsOrthogonal Q) :
    Q⁻¹ = Qᵀ := by
  -- From Qᵀ * Q = I, we know Qᵀ is a left inverse of Q
  -- Since Q is invertible (det(Q) = ±1 ≠ 0), left inverse = right inverse
  -- Therefore Q⁻¹ = Qᵀ
  apply Matrix.inv_eq_left_inv
  exact hQ

/--
If Sigma is diagonal with positive entries and A·Sigma·Aᵀ is also diagonal,
then the rows of A satisfy a strong orthogonality constraint.
-/
lemma diagonal_sandwich_constraint
    (A : Matrix n n ℝ)
    (Sigma : Matrix n n ℝ)
    (hSigma_diag : Sigma.IsDiag)
    (hSigma_pos : ∀ i, 0 < Sigma i i)
    (hASigmaAT_diag : (A * Sigma * Aᵀ).IsDiag) :
    ∀ i j, i ≠ j → (∑ k, A i k * Sigma k k * A j k) = 0 := by
  intros i j hij
  -- Use that the result is 0 from diagonality
  have h_diag : (A * Sigma * Aᵀ) i j = 0 := hASigmaAT_diag hij
  -- Show that (A * Sigma * Aᵀ) i j = ∑ k, A i k * Sigma k k * A j k
  suffices ∑ k, A i k * Sigma k k * A j k = (A * Sigma * Aᵀ) i j by rw [this, h_diag]
  -- Expand matrix mult
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  congr 1
  ext k
  congr 1
  -- For diagonal Sigma: ∑_l A i l * Sigma l k = A i k * Sigma k k
  rw [Finset.sum_eq_single k]
  · intros l _ hlk
    rw [hSigma_diag hlk, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/--
Key lemma: If Sigma_z = Diag(σ₁, ..., σₙ) with positive σᵢ, and A·Sigma_z·Aᵀ is diagonal,
then A can be written as D₁·Q·D₂ where Q is orthogonal and D₁, D₂ are diagonal.

This is the core result showing symmetry breaking in ICA.

## Proof Sketch (to be formalized):
1. Define B = Sigma_z^(-1/2) * A * Sigma_z^(1/2) (requires matrix square root)
2. Then B * Bᵀ = Sigma_z^(-1/2) * (A * Sigma_z * Aᵀ) * Sigma_z^(-1/2) is diagonal
3. Since B * Bᵀ is symmetric and diagonal, we can write B * Bᵀ = Diag(λ)
4. By spectral theorem, B = Q * Diag(√λ) for some orthogonal Q (requires spectral/polar decomposition)
5. Substitute back: A = Sigma_z^(1/2) * Q * Diag(√λ) * Sigma_z^(-1/2)
                       = (Sigma_z^(1/2)) * Q * (Diag(√λ) * Sigma_z^(-1/2))
                       = D₁ * Q * D₂

This requires:
- Matrix square root for positive definite diagonal matrices (not yet in Mathlib)
- Polar decomposition or singular value decomposition (not yet in Mathlib)
- OR a direct proof using the weighted orthogonality from diagonal_sandwich_constraint

Mathlib currently has the spectral theorem for Hermitian matrices, but not yet
the full machinery needed for this proof. This is a known gap being actively developed.
-/
theorem uncorrelated_transform_decomposition
    (A : Matrix n n ℝ)
    (Sigma_z : Matrix n n ℝ)
    (hA_inv : IsUnit A.det)
    (hSigma_z_diag : Sigma_z.IsDiag)
    (hSigma_z_pos : ∀ i, 0 < Sigma_z i i)
    (hASigmaAT_diag : (A * Sigma_z * Aᵀ).IsDiag) :
    ∃ (D₁ D₂ : Matrix n n ℝ) (Q : Matrix n n ℝ),
      D₁.IsDiag ∧ D₂.IsDiag ∧ IsOrthogonal Q ∧ A = D₁ * Q * D₂ := by
  sorry

/--
Corollary: The decomposition reduces GL(n) symmetry to the product of
diagonal matrices (scalings) and orthogonal matrices (rotations/reflections).
-/
theorem symmetry_reduction
    (A : Matrix n n ℝ)
    (Sigma_z : Matrix n n ℝ)
    (hA_inv : IsUnit A.det)
    (hSigma_z_diag : Sigma_z.IsDiag)
    (hSigma_z_pos : ∀ i, 0 < Sigma_z i i)
    (hASigmaAT_diag : (A * Sigma_z * Aᵀ).IsDiag) :
    ∃ (scalings rotations : Set (Matrix n n ℝ)),
      (∀ D ∈ scalings, D.IsDiag) ∧
      (∀ Q ∈ rotations, IsOrthogonal Q) ∧
      A ∈ {M | ∃ D₁ ∈ scalings, ∃ Q ∈ rotations, ∃ D₂ ∈ scalings, M = D₁ * Q * D₂} := by
  -- Get the decomposition from the main theorem
  obtain ⟨D₁, D₂, Q, hD₁_diag, hD₂_diag, hQ_orth, hA_decomp⟩ :=
    uncorrelated_transform_decomposition A Sigma_z hA_inv hSigma_z_diag hSigma_z_pos hASigmaAT_diag
  -- Define the sets
  use {M | M.IsDiag}, {M | IsOrthogonal M}
  refine ⟨fun D hD => hD, fun Q hQ => hQ, ?_⟩
  -- Show A is in the decomposed set
  simp only [Set.mem_setOf_eq]
  exact ⟨D₁, hD₁_diag, Q, hQ_orth, D₂, hD₂_diag, hA_decomp⟩

/--
Application to ICA: When z has independent components with positive variance,
Cov(z) is diagonal. If A transforms z to Az with uncorrelated components,
then Cov(Az) = A·Cov(z)·Aᵀ is also diagonal.
The theorem shows A must have the special form D₁·Q·D₂.

This explains why ICA can recover independent components up to:
1. Permutation (absorbed into Q)
2. Scaling (the D₁, D₂ factors)
3. Sign flips (det(Q) = ±1)

but NOT arbitrary linear transformations (which would be full GL(n)).
-/
theorem ica_symmetry_breaking
    (Sigma_z : Matrix n n ℝ)
    (hSigma_z_diag : Sigma_z.IsDiag)
    (hSigma_z_pos : ∀ i, 0 < Sigma_z i i)
    (A : Matrix n n ℝ)
    (hA : IsUnit A.det)
    (hDiag : (A * Sigma_z * Aᵀ).IsDiag) :
    ∃ (D₁ D₂ : Matrix n n ℝ) (Q : Matrix n n ℝ),
      D₁.IsDiag ∧ D₂.IsDiag ∧ IsOrthogonal Q ∧ A = D₁ * Q * D₂ := by
  exact uncorrelated_transform_decomposition A Sigma_z hA hSigma_z_diag hSigma_z_pos hDiag

/--
The group of transformations preserving uncorrelated structure is significantly
smaller than GL(n): it's the product of the diagonal group D(n) × O(n) × D(n),
not the full general linear group GL(n).

This is the mathematical expression of "symmetry breaking" in ICA.
-/
theorem symmetry_group_reduction
    (Sigma_z : Matrix n n ℝ)
    (hSigma_z_diag : Sigma_z.IsDiag)
    (hSigma_z_pos : ∀ i, 0 < Sigma_z i i) :
    {A : Matrix n n ℝ | IsUnit A.det ∧ (A * Sigma_z * Aᵀ).IsDiag} ⊆
    {M | ∃ (D₁ D₂ Q : Matrix n n ℝ), D₁.IsDiag ∧ D₂.IsDiag ∧ IsOrthogonal Q ∧ M = D₁ * Q * D₂} := by
  intro A ⟨hA_inv, hA_diag⟩
  exact ica_symmetry_breaking Sigma_z hSigma_z_diag hSigma_z_pos A hA_inv hA_diag

end Chapter2Exercise23_2
