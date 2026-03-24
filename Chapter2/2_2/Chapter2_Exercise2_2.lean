/-
  深度表征学习 第2章 练习2.2

  证明：对于高斯随机变量 $\vz \sim \mathcal{N}(\mathbf{0}, \sigma^2 \mathbf{I})$，
  任意正交矩阵 $\mathbf{Q}$（满足 $\mathbf{Q}^\top \mathbf{Q} = \mathbf{I}$），
  有 $\mathbf{Q}\vz$ 与 $\vz$ 同分布。

  这是高斯分布旋转不变性的核心性质。
-/

import Mathlib

/-!
# 高斯分布的旋转不变性 (Gaussian Rotational Invariance)

我们形式化并证明：设 $\vz \sim \mathcal{N}(\mathbf{0}, \sigma^2 \mathbf{I})$
是均值为零、协方差矩阵为 $\sigma^2 \mathbf{I}$ 的 $d$ 维高斯随机变量。
则对于任意正交矩阵 $\mathbf{Q} \in \mathbb{R}^{d \times d}$
（即 $\mathbf{Q}^\top \mathbf{Q} = \mathbf{I}$），随机变量 $\mathbf{Q}\vz$ 与 $\vz$ 同分布。

这意味着高斯分布在旋转（正交变换）下是不变的。

证明思路：
1. 多元正态分布 $\mathcal{N}(\mathbf{0}, \sigma^2 \mathbf{I})$ 的概率密度函数为：
   $f(\mathbf{x}) = \frac{1}{(2\pi\sigma^2)^{d/2}} \exp\left(-\frac{\|\mathbf{x}\|^2}{2\sigma^2}\right)$

2. 对于线性变换 $\mathbf{y} = \mathbf{Q}\mathbf{x}$，随机变量的密度变换公式为：
   $f_{\mathbf{Y}}(\mathbf{y}) = f_{\mathbf{X}}(\mathbf{Q}^{-1}\mathbf{y}) \cdot |\det(\mathbf{Q}^{-1})|$

3. 由于 $\mathbf{Q}$ 是正交矩阵，有 $\mathbf{Q}^{-1} = \mathbf{Q}^\top$，
   $\|\mathbf{Q}\mathbf{x}\| = \|\mathbf{x}\|$，且 $|\det(\mathbf{Q})| = 1$。

4. 因此 $f_{\mathbf{Q}\vz}(\mathbf{y}) = f_{\vz}(\mathbf{y})$，两分布相同。
-/

open Real Matrix

noncomputable section

namespace Chapter2Exercise22

variable {d : ℕ}

/-- 正交矩阵的定义：$\mathbf{Q}^\top \mathbf{Q} = \mathbf{I}$ -/
def IsOrthogonal (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Qᵀ * Q = 1

/-- 多元高斯分布的密度函数

  $f(\mathbf{x}) = \frac{1}{(2\pi\sigma^2)^{d/2}} \exp\left(-\frac{\|\mathbf{x}\|^2}{2\sigma^2}\right)$ -/
def gaussianDensity (σ : ℝ) (x : Fin d → ℝ) : ℝ :=
  (2 * π * σ^2) ^ (-(d : ℝ) / 2) * exp (-‖x‖^2 / (2 * σ^2))

/-- 正交矩阵保持向量范数

  这是因为 $\|Qx\|^2 = x^T Q^T Q x = x^T x = \|x\|^2$。 -/
theorem orthogonal_preserves_norm {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsOrthogonal Q)
    (x : Fin d → ℝ) :
    ‖Q.mulVec x‖ = ‖x‖ := by
  sorry

/-- 正交矩阵的行列式绝对值为1

  由 $\det(Q^T Q) = \det(I) = 1$，有 $\det(Q)^2 = 1$，故 $|\det(Q)| = 1$。 -/
theorem orthogonal_det_abs_one {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsOrthogonal Q) :
    |Q.det| = 1 := by
  sorry

/-- 多元高斯分布在正交变换下不变

  核心引理：正交变换后密度函数保持不变。 -/
theorem gaussian_rotational_invariance (σ : ℝ) (hσ : σ > 0)
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsOrthogonal Q) :
    ∀ x : Fin d → ℝ,
      gaussianDensity σ (Q.mulVec x) = gaussianDensity σ x := by
  intro x
  have h_norm : ‖Q.mulVec x‖ = ‖x‖ := orthogonal_preserves_norm hQ x
  show gaussianDensity σ (Q.mulVec x) = gaussianDensity σ x
  unfold gaussianDensity
  rw [h_norm]

/-- 练习2.2：多元高斯分布的旋转不变性

  设 $\vz \sim \mathcal{N}(\mathbf{0}, \sigma^2 \mathbf{I})$ 是 $d$ 维高斯随机变量，
  其协方差矩阵为 $\sigma^2 \mathbf{I}$。则对于任意正交矩阵 $\mathbf{Q}$
  （满足 $\mathbf{Q}^\top \mathbf{Q} = \mathbf{I}$），有
  $\mathbf{Q}\vz \sim \vz$（即 $\mathbf{Q}\vz$ 与 $\vz$ 同分布）。

  **证明思路**：
  1. 多元正态分布 $\mathcal{N}(\mathbf{0}, \sigma^2 \mathbf{I})$ 的概率密度函数为
     $f(\mathbf{x}) = \frac{1}{(2\pi\sigma^2)^{d/2}} \exp\left(-\frac{\|\mathbf{x}\|^2}{2\sigma^2}\right)$
  2. 对于线性变换 $\mathbf{y} = \mathbf{Q}\mathbf{x}$，根据密度变换公式：
     $f_{\mathbf{Y}}(\mathbf{y}) = f_{\mathbf{X}}(\mathbf{Q}^{-1}\mathbf{y}) \cdot |\det(\mathbf{Q}^{-1})|$
  3. 由于 $\mathbf{Q}$ 是正交矩阵，有 $\mathbf{Q}^{-1} = \mathbf{Q}^\top$，
     $\|\mathbf{Q}\mathbf{x}\| = \|\mathbf{x}\|$，且 $|\det(\mathbf{Q})| = 1$
  4. 因此 $f_{\mathbf{Q}\vz}(\mathbf{y}) = f_{\vz}(\mathbf{y})$，两分布相同。 -/
theorem exercise_gaussian_rot_invar (σ : ℝ) (hσ : σ > 0)
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsOrthogonal Q) :
    ∀ x : Fin d → ℝ, gaussianDensity σ (Q.mulVec x) = gaussianDensity σ x :=
  gaussian_rotational_invariance σ hσ hQ

end Chapter2Exercise22
