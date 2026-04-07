/-
  深度表征学习 第2章 练习2.3.2

  ICA对称性：若 z 是零均值、独立分量（正方差）的随机向量，
  A 是可逆方阵，且 Az 的各分量不相关（即 Cov(Az) 是对角阵），
  则 A 可以分解为 A = D₁ Q D₂，其中 Q 是正交矩阵，D₁, D₂ 是对角矩阵。

  See book Chapter 2, Exercise 2.3 (exercise:symmetry-identifiability), part 2.
-/

import Mathlib

/-!
# Exercise 2.3.2: ICA Symmetry — Covariance Preservation and Decomposition

## Statement

Given z with:
- Zero mean: 𝔼[z] = 0
- Independent components z_i with positive variance: Cov(z) = Σ = diagonal(σ), σᵢ > 0
- A is an invertible square matrix

If Az has uncorrelated components (i.e., Cov(Az) = A Cov(z) Aᵀ is diagonal),
then A = D₁ Q D₂ where Q is orthogonal and D₁, D₂ are diagonal.

## Proof strategy

Let Σ = diag(σ₁,...,σd) with σᵢ > 0. Let D = diag(√σ₁,...,√σd).
Define B = A * D (invertible since both A and D are).
Then B * Bᵀ = A * D * Dᵀ * Aᵀ = A * Σ * Aᵀ (since D is diagonal and symmetric, D² = Σ).
Since A Σ Aᵀ is diagonal, B * Bᵀ is diagonal, so B has orthogonal rows.
Since B is invertible, all rows are nonzero.
Let D₁ = diag(‖row_i B‖), then Q = D₁⁻¹ * B is orthogonal and B = D₁ * Q.
Hence A = B * D⁻¹ = D₁ * Q * D⁻¹ = D₁ * Q * D₂ (D₂ = D⁻¹ is diagonal).
-/

open Matrix

noncomputable section

namespace Chapter2Exercise23_2

variable {d : Type*} [Fintype d] [DecidableEq d]

set_option linter.unusedSectionVars false

/-!
## Helper: Invertible diagonal matrix with positive entries
-/

/-- A diagonal matrix with strictly positive entries is invertible. -/
lemma isUnit_diagonal_of_pos (f : d → ℝ) (hf : ∀ i, 0 < f i) :
    IsUnit (diagonal f : Matrix d d ℝ) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
  exact isUnit_iff_ne_zero.mpr (Finset.prod_pos (fun i _ => hf i)).ne'

/-!
## Helper: D * Dᵀ = diagonal σ when D = diagonal(√σ)
-/

/-- If D = diagonal(√σ) then D * Dᵀ = diagonal(σ) when σᵢ ≥ 0. -/
lemma diag_sqrt_mul_transpose (σ : d → ℝ) (hσ : ∀ i, 0 ≤ σ i) :
    (diagonal (fun i => Real.sqrt (σ i))) * (diagonal (fun i => Real.sqrt (σ i)))ᵀ =
    diagonal σ := by
  simp [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Real.mul_self_sqrt, hσ]

/-!
## Helper: BBᵀ positive definite from invertibility of B
-/

/--
An invertible real matrix B satisfies: B * Bᵀ is positive definite.
-/
lemma posDef_mul_transpose_of_isUnit (B : Matrix d d ℝ) (hB : IsUnit B) :
    (B * Bᵀ).PosDef := by
  have hinj : Function.Injective (fun v => Matrix.vecMul v B) :=
    Matrix.vecMul_injective_of_isUnit hB
  have h := Matrix.PosDef.mul_conjTranspose_self B hinj
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-!
## Key Algebraic Lemma: Orthogonal Row Decomposition
-/

/--
An invertible square real matrix B with BBᵀ diagonal decomposes as B = D₁ * Q
where D₁ is diagonal and Q is orthogonal.
-/
lemma ortho_row_decomp
    (B : Matrix d d ℝ)
    (hB : IsUnit B)
    (hOrthoRows : (B * Bᵀ).IsDiag) :
    ∃ (D₁ : Matrix d d ℝ) (Q : Matrix d d ℝ),
      D₁.IsDiag ∧
      Q ∈ Matrix.orthogonalGroup d ℝ ∧
      B = D₁ * Q := by
  -- BBᵀ positive definite ⟹ diagonal entries are positive
  have hBBt_posDef : (B * Bᵀ).PosDef := posDef_mul_transpose_of_isUnit B hB
  -- rowSq i = (BBᵀ) i i > 0 (the squared norm of row i)
  let rowSq : d → ℝ := fun i => (B * Bᵀ) i i
  have hrowSq_pos : ∀ i, 0 < rowSq i := fun i => hBBt_posDef.diag_pos
  -- D₁ = diagonal(√rowSq), invertible since rowSq i > 0
  let D₁ : Matrix d d ℝ := diagonal (fun i => Real.sqrt (rowSq i))
  have hD₁_diag : D₁.IsDiag := Matrix.isDiag_diagonal _
  have hD₁_isUnit : IsUnit D₁ :=
    isUnit_diagonal_of_pos _ (fun i => Real.sqrt_pos.mpr (hrowSq_pos i))
  -- Q = D₁⁻¹ * B; then B = D₁ * Q
  let Q : Matrix d d ℝ := D₁⁻¹ * B
  have hB_eq : B = D₁ * Q := by
    simp only [Q, ← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv D₁ (hD₁_isUnit.map Matrix.detMonoidHom)]
    exact (Matrix.one_mul B).symm
  refine ⟨D₁, Q, hD₁_diag, ?_, hB_eq⟩
  -- Show Q * Qᵀ = 1
  rw [Matrix.mem_orthogonalGroup_iff]
  simp only [Q]
  -- Q * Qᵀ = D₁⁻¹ * B * (D₁⁻¹ * B)ᵀ
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
      ← Matrix.mul_assoc, Matrix.mul_assoc (D₁⁻¹) B]
  -- Goal: D₁⁻¹ * (B * Bᵀ) * D₁⁻ᵀ = 1
  -- BBᵀ = diagonal(rowSq) since BBᵀ is diagonal
  have hBBt_eq_diag : B * Bᵀ = diagonal rowSq := by
    rw [Matrix.isDiag_iff_diagonal_diag] at hOrthoRows
    rw [← hOrthoRows]; rfl
  rw [hBBt_eq_diag]
  -- D₁ᵀ = D₁ (diagonal is symmetric), so D₁⁻ᵀ = D₁⁻¹
  have hD₁t_inv : (D₁.transpose)⁻¹ = D₁⁻¹ := by
    simp only [D₁, Matrix.diagonal_transpose]
  rw [hD₁t_inv]
  -- Goal: D₁⁻¹ * diagonal(rowSq) * D₁⁻¹ = 1
  -- Step: explicitly compute D₁⁻¹ = diagonal(1/√rowSq)
  have hD₁inv : D₁⁻¹ = diagonal (fun i => (Real.sqrt (rowSq i))⁻¹) := by
    apply Matrix.inv_eq_right_inv
    simp only [D₁, Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hrowSq_pos i)).ne']
  rw [hD₁inv, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  have hsi : 0 < Real.sqrt (rowSq i) := Real.sqrt_pos.mpr (hrowSq_pos i)
  have hsq : Real.sqrt (rowSq i) ^ 2 = rowSq i := Real.sq_sqrt (le_of_lt (hrowSq_pos i))
  field_simp [hsi.ne']
  linarith [hsq]

/-!
## Main Theorem: ICA Symmetry Decomposition
-/

/--
ICA Symmetry Theorem (Exercise 2.3.2):
If A is an invertible d×d matrix and Σ = diagonal(σ) with σᵢ > 0,
and A * Σ * Aᵀ is diagonal (uncorrelated components condition),
then A = D₁ * Q * D₂ where Q is orthogonal and D₁, D₂ are diagonal.

This shows that the only matrices preserving the "uncorrelated components"
property of a diagonal covariance are products of diagonal matrices and
orthogonal matrices — confirming the symmetry structure of ICA.
-/
theorem ica_symmetry_decomposition
    (A : Matrix d d ℝ)
    (σ : d → ℝ)
    (hA : IsUnit A)
    (hσ : ∀ i, 0 < σ i)
    (hUncorr : (A * diagonal σ * Aᵀ).IsDiag) :
    ∃ (D₁ D₂ : Matrix d d ℝ) (Q : Matrix d d ℝ),
      D₁.IsDiag ∧
      D₂.IsDiag ∧
      Q ∈ Matrix.orthogonalGroup d ℝ ∧
      A = D₁ * Q * D₂ := by
  -- Step 1: D = diagonal(√σ) is invertible
  let D : Matrix d d ℝ := diagonal (fun i => Real.sqrt (σ i))
  have hD_isUnit : IsUnit D :=
    isUnit_diagonal_of_pos _ (fun i => Real.sqrt_pos.mpr (hσ i))
  -- Step 2: B = A * D is invertible
  let B : Matrix d d ℝ := A * D
  have hB : IsUnit B := hA.mul hD_isUnit
  -- Step 3: B * Bᵀ = A * Σ * Aᵀ
  have hBBt_eq : B * Bᵀ = A * diagonal σ * Aᵀ := by
    -- B * Bᵀ = (A*D) * (A*D)ᵀ = A * (D * Dᵀ) * Aᵀ = A * Σ * Aᵀ
    have hD2 : D * Dᵀ = diagonal σ := diag_sqrt_mul_transpose σ (fun i => le_of_lt (hσ i))
    calc B * Bᵀ
        = (A * D) * (A * D)ᵀ           := rfl
      _ = (A * D) * (Dᵀ * Aᵀ)         := by rw [Matrix.transpose_mul]
      _ = A * (D * Dᵀ) * Aᵀ           := by rw [← Matrix.mul_assoc, Matrix.mul_assoc A]
      _ = A * diagonal σ * Aᵀ          := by rw [hD2]
  -- Step 4: B has orthogonal rows (B * Bᵀ is diagonal)
  have hBOrtho : (B * Bᵀ).IsDiag := hBBt_eq ▸ hUncorr
  -- Step 5: Decompose B = D₁ * Q with D₁ diagonal and Q orthogonal
  obtain ⟨D₁, Q, hD₁_diag, hQ_ortho, hB_decomp⟩ := ortho_row_decomp B hB hBOrtho
  -- Step 6: D₂ = D⁻¹ is diagonal
  let D₂ : Matrix d d ℝ := D⁻¹
  have hD₂_diag : D₂.IsDiag := by
    simp only [D₂, D, Matrix.inv_diagonal]
    exact Matrix.isDiag_diagonal _
  -- Step 7: A = D₁ * Q * D₂
  have hA_decomp : A = D₁ * Q * D₂ := by
    have hD_D₂ : D * D₂ = 1 := Matrix.mul_nonsing_inv D (hD_isUnit.map Matrix.detMonoidHom)
    calc A = A * 1         := (mul_one A).symm
      _ = A * (D * D₂)     := by rw [hD_D₂]
      _ = (A * D) * D₂     := by rw [← Matrix.mul_assoc]
      _ = B * D₂           := rfl
      _ = (D₁ * Q) * D₂   := by rw [hB_decomp]
  exact ⟨D₁, D₂, Q, hD₁_diag, hD₂_diag, hQ_ortho, hA_decomp⟩

/-!
## Corollary: Statistical interpretation
-/

/--
Corollary: Under the ICA model, any invertible A that preserves the
uncorrelated component structure decomposes as D₁ Q D₂ with Q orthogonal
and D₁, D₂ diagonal. This restricts the symmetry group to scale × rotation × scale.
-/
theorem ica_symmetry_group_restriction
    (A : Matrix d d ℝ)
    (σ : d → ℝ)
    (hA : IsUnit A)
    (hσ : ∀ i, 0 < σ i)
    (hUncorr : (A * diagonal σ * Aᵀ).IsDiag) :
    ∃ (Q : Matrix d d ℝ),
      Q ∈ Matrix.orthogonalGroup d ℝ ∧
      ∃ (d₁ d₂ : d → ℝ),
        A = diagonal d₁ * Q * diagonal d₂ := by
  obtain ⟨D₁, D₂, Q, hD₁_diag, hD₂_diag, hQ_ortho, hA_decomp⟩ :=
    ica_symmetry_decomposition A σ hA hσ hUncorr
  -- D₁ and D₂ are diagonal matrices, so D₁ = diagonal D₁.diag
  rw [Matrix.isDiag_iff_diagonal_diag] at hD₁_diag hD₂_diag
  -- Use D₁.diag and D₂.diag as the diagonal vectors
  refine ⟨Q, hQ_ortho, D₁.diag, D₂.diag, ?_⟩
  rw [hA_decomp, ← hD₁_diag, ← hD₂_diag]
  simp [Matrix.diag_diagonal]

end Chapter2Exercise23_2

end
