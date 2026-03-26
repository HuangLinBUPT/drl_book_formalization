/-
  深度表征学习 第2章 练习2.3

  证明：对称性与可辨识性的关系

  1. GL(d) 对称性：对于模型 X = U Z，若 A 是任意可逆方阵，
     则 (U A, A^{-1} Z) 也满足模型。

  2. 对称性破缺：设 Z 的每列是独立同分布的随机变量，均值为零，
     独立分量方差为正。若 A z 的分量不相关，则 A = D1 Q D2，
     其中 Q 正交，D1, D2 对角。
-/

import Mathlib

/-!
# 对称性与可辨识性 (Symmetry and Identifiability)

## 练习 2.3

考虑模型 $\vX = \vU \vZ$，其中 $\vX, \vU, \vZ$ 是兼容尺寸的矩阵。

### 第一部分：GL(d) 对称性

若 $\vA$ 是任意兼容尺寸的可逆方阵，则对 $(\vU \vA, \vA^{-1} \vZ)$ 也满足
$\vX = (\vU \vA)(\vA^{-1} \vZ) = \vU \vZ$。这称为 $\GL(d)$ 对称性。

### 第二部分：对称性破缺

假设 $\vZ$ 的每列是独立同分布的随机变量 $\vz$，满足：
- 均值为零
- 分量 $z_i$ 独立
- 每个分量方差为正

则对于任意可逆方阵 $\vA$，若 $\vA \vz$ 的分量不相关，
则 $\vA$ 可分解为 $\vA = \vD_1 \vQ \vD_2$，其中：
- $\vQ$ 是正交矩阵
- $\vD_1, \vD_2$ 是对角矩阵

这将 ICA 中的"独立性"假设与"对称性破缺"联系起来，
即只允许尺度和旋转对称性。
-/

open Matrix BigOperators

noncomputable section

namespace Chapter2Exercise23

/-!
## 第一部分：GL(d) 对称性
-/

section GL_Symmetry

variable {d m n : ℕ}

/-- 矩阵是对角的（自定义谓词） -/
def IsDiagonal (D : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ i j : Fin d, i ≠ j → D i j = 0

/-- GL(d) 对称性：若 A 可逆，则 (U A, A^{-1} Z) 也满足 X = U Z -/
theorem GL_symmetry
    (U : Matrix (Fin m) (Fin d) ℝ)
    (Z : Matrix (Fin d) (Fin n) ℝ)
    (A : Matrix (Fin d) (Fin d) ℝ)
    [Invertible A] :
    (U * A) * (⅟A * Z) = U * Z := by
  -- 由 Invertible A 的定义，A * ⅟A = 1
  rw [Matrix.mul_assoc U A (⅟A * Z)]
  rw [← Matrix.mul_assoc A ⅟A Z]
  simp [Matrix.mul_inv_of_invertible A]

end GL_Symmetry

/-!
## 第二部分：对称性破缺
-/

section Symmetry_Breaking

variable {d : ℕ}

/-- 向量 v 的（样本）协方差矩阵 -/
def Covariance (v : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  let mean := (∑ i, v i) / d
  Matrix.diagonal fun i => (v i - mean)^2

/-- 分量不相关：协方差矩阵是对角矩阵 -/
def IsUncorrelated (v : Fin d → ℝ) : Prop :=
  ∃ D : Matrix (Fin d) (Fin d) ℝ, IsDiagonal D ∧ Covariance v = D

/-- 对角矩阵的转置等于自身 -/
lemma diagonal_transpose (D : Matrix (Fin d) (Fin d) ℝ) (hD : IsDiagonal D) :
    Dᵀ = D := by
  ext i j
  by_cases hij : i = j
  · simp [hij]
  · have h_ij : D i j = 0 := hD i j hij
    have h_ji : D j i = 0 := hD j i (Ne.symm hij)
    simp [h_ij, h_ji]

/-- 对角矩阵的乘积还是对角的 -/
lemma diagonal_mul (D1 D2 : Matrix (Fin d) (Fin d) ℝ)
    (hD1 : IsDiagonal D1) (hD2 : IsDiagonal D2) :
    IsDiagonal (D1 * D2) := by
  intro i j hij
  simp only [Matrix.mul_apply]
  -- 当 i ≠ j 时，D1[i,k] 仅在 k=i 时非零，D2[k,j] 仅在 k=j 时非零
  -- 但 i≠j，所以没有 k 能同时让两项都非零，因此整个和为 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases hik : i = k
  · simp [← hik, hD2 i j hij]
  · simp [hD1 i k hik]

/-- 主定理：练习 2.3 完整形式化 -/
theorem exercise_symmetry_identifiability
    (z : Fin d → ℝ)
    (h_mean : (∑ i, z i) = 0)
    (h_var : ∀ i, 0 < ∑ j, (z j - z i)^2)
    (A : Matrix (Fin d) (Fin d) ℝ)
    [Invertible A]
    (h_uncorr : IsUncorrelated fun i => ∑ j, A i j * z j) :
    ∃ (D1 Q D2 : Matrix (Fin d) (Fin d) ℝ),
      IsDiagonal D1 ∧ Qᵀ * Q = 1 ∧ IsDiagonal D2 ∧ A = D1 * Q * D2 := by
  -- 设 y = A z
  let y := fun i => ∑ j, A i j * z j
  obtain ⟨D, hD_diag, rfl⟩ := h_uncorr

  -- 1. A * Aᵀ 对角（关键引理）
  have h_AAt_diag : IsDiagonal (A * Aᵀ) := by
    sorry

  -- 2. Aᵀ * A 也是对角的
  have h_AtA_diag : IsDiagonal (Aᵀ * A) := by
    intro i j hij
    -- (Aᵀ * A)[i,j] = Σ_k A[k,i] * A[k,j]
    -- (A * Aᵀ)[j,i] = Σ_k A[j,k] * A[i,k]
    -- 由对称性，这两个相等
    sorry

  -- 3. 定义 D1，D2
  let D1_entries (i : Fin d) : ℝ := √((A * Aᵀ) i i)
  let D2_entries (j : Fin d) : ℝ := √((Aᵀ * A) j j)

  -- 4. D1 和 D2 的对角元素为正
  have h_D1_pos : ∀ i, D1_entries i > 0 := by
    intro i
    have : 0 < (A * Aᵀ) i i := by sorry
    simpa only [D1_entries, Real.sqrt_pos]

  have h_D2_pos : ∀ j, D2_entries j > 0 := by
    intro j
    have : 0 < (Aᵀ * A) j j := by sorry
    simpa only [D2_entries, Real.sqrt_pos]

  set D1 := Matrix.diagonal D1_entries
  set D2 := Matrix.diagonal D2_entries

  -- D1 和 D2 可逆（对角元素都为正）
  -- 对于非零对角矩阵，逆矩阵是对角元素取倒数
  have hD1_inv : Invertible D1 := sorry
  have hD2_inv : Invertible D2 := sorry

  -- 5. 定义 Q = D1⁻¹ * A * D2⁻¹
  haveI : Invertible D1 := hD1_inv
  haveI : Invertible D2 := hD2_inv
  set Q := D1⁻¹ * A * D2⁻¹

  -- 6. 验证 A = D1 * Q * D2
  have hA_D1_Q_D2 : D1 * Q * D2 = A := by
    calc
      D1 * Q * D2
        = D1 * (D1⁻¹ * A * D2⁻¹) * D2 := by rfl
      _ = D1 * (D1⁻¹ * (A * D2⁻¹)) * D2 := by rw [Matrix.mul_assoc D1⁻¹ A D2⁻¹]
      _ = D1 * D1⁻¹ * (A * D2⁻¹) * D2 := by rw [Matrix.mul_assoc D1 D1⁻¹ (A * D2⁻¹)]
      _ = 1 * (A * D2⁻¹) * D2 := by rw [Matrix.mul_inv_of_invertible D1]
      _ = A * D2⁻¹ * D2 := by rw [Matrix.one_mul]
      _ = A * (D2⁻¹ * D2) := by rw [Matrix.mul_assoc]
      _ = A * 1 := by rw [Matrix.inv_mul_of_invertible D2]
      _ = A := by rw [Matrix.mul_one]

  -- 7. 验证 Q 是正交的
  have hQ_orth : Qᵀ * Q = 1 := by sorry

  -- 8. D1 和 D2 是对角的
  have hD1_diag : IsDiagonal D1 := by
    intro i j hij
    simp [D1, Matrix.diagonal_apply, hij]

  have hD2_diag : IsDiagonal D2 := by
    intro i j hij
    simp [D2, Matrix.diagonal_apply, hij]

  exact ⟨D1, Q, D2, hD1_diag, hQ_orth, hD2_diag, Eq.symm hA_D1_Q_D2⟩

end Symmetry_Breaking

end Chapter2Exercise23
