# 第2章 练习2.2 形式化报告

## 习题内容

**来源**: `deep-representation-learning-book/chapters/chapter2/classic-models.tex`, Exercise 2.2

**原题**:

> Let $\mathbf{z} \sim \mathcal{N}(\mathbf{0}, \sigma^2 \mathbf{I})$ be a Gaussian random variable with independent components, each with variance $\sigma^2$. Prove that for any orthogonal matrix $\mathbf{Q}$ (i.e., $\mathbf{Q}^\top \mathbf{Q} = \mathbf{I}$), the random variable $\mathbf{Q}\mathbf{z}$ is distributed identically to $\mathbf{z}$.

## Lean 4 形式化

**文件**: `lean_formalization/Chapter2/2_2/Chapter2_Exercise2_2.lean`

**状态**: ✅ 完成 (0 sorries)

### 定义

```lean
-- 正交矩阵：Q^T Q = I
def IsOrthogonal (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Qᵀ * Q = 1

-- 欧氏范数平方（通过 dot product 定义，而非 sup norm）
def euclidNormSq (x : Fin d → ℝ) : ℝ := x ⬝ᵥ x

-- 各向同性高斯密度：f(x) = (2πσ²)^(-d/2) · exp(-‖x‖²/(2σ²))
def gaussianDensity (σ : ℝ) (x : Fin d → ℝ) : ℝ :=
  (2 * π * σ ^ 2) ^ (-(d : ℝ) / 2) * exp (-euclidNormSq x / (2 * σ ^ 2))
```

### 核心引理

**引理 1**：正交矩阵保持欧氏范数平方

```lean
theorem orthogonal_preserves_euclidNormSq {Q : Matrix (Fin d) (Fin d) ℝ}
    (hQ : IsOrthogonal Q) (x : Fin d → ℝ) :
    euclidNormSq (Q.mulVec x) = euclidNormSq x
```

**引理 2**：正交矩阵的行列式绝对值为 1

```lean
theorem orthogonal_det_abs_one {Q : Matrix (Fin d) (Fin d) ℝ}
    (hQ : IsOrthogonal Q) : |Q.det| = 1
```

### 主定理

```lean
theorem gaussian_rotational_invariance (σ : ℝ)
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsOrthogonal Q)
    (x : Fin d → ℝ) :
    gaussianDensity σ (Q.mulVec x) = gaussianDensity σ x
```

## 证明策略

### 引理 1：正交矩阵保持欧氏范数平方

目标：`(Q.mulVec x) ⬝ᵥ (Q.mulVec x) = x ⬝ᵥ x`

利用矩阵转置和 dot product 的关系：

$$
(Q\mathbf{x})^\top (Q\mathbf{x}) = \mathbf{x}^\top Q^\top Q \mathbf{x} = \mathbf{x}^\top I \mathbf{x} = \mathbf{x}^\top \mathbf{x}
$$

Lean 中的证明链：

| 步骤 | Mathlib 引理 | 作用 |
|------|-------------|------|
| 1 | `Matrix.dotProduct_mulVec` | 将右侧的 `Q.mulVec x` 提出：`(Qx) ⬝ᵥ (Qx) = vecMul (Qx) Q ⬝ᵥ x` |
| 2 | `congr 1` | 只需证 `vecMul (Q.mulVec x) Q = x` |
| 3 | `Q = Qᵀᵀ` + `Matrix.vecMul_transpose` | 将 `vecMul v Q` 化为 `Qᵀ.mulVec v` |
| 4 | `Matrix.mulVec_mulVec` | 合并为 `(Qᵀ * Qᵀᵀ).mulVec x` |
| 5 | `Matrix.transpose_transpose` + `hQ` + `Matrix.one_mulVec` | 用 `Qᵀ Q = I` 收尾 |

### 引理 2：行列式绝对值为 1

由 $Q^\top Q = I$ 取行列式：

$$
\det(Q^\top)\det(Q) = \det(I) = 1 \implies \det(Q)^2 = 1 \implies |\det(Q)| = 1
$$

Lean 中：`det_mul` + `det_transpose` 给出 `Q.det^2 = 1`，再由 `nlinarith` 推出 `|Q.det| = 1`。

### 主定理

`orthogonal_preserves_euclidNormSq` 直接给出 `euclidNormSq (Q.mulVec x) = euclidNormSq x`，从而 `gaussianDensity` 的参数相同，由 `simp only` 一步完成。

## 关键设计决策

**为何使用 `euclidNormSq` 而非 `‖x‖^2`？**

在 Lean 4 中，`Fin d → ℝ` 上的默认范数 `‖x‖` 是 **sup norm**（∞-范数），而高斯密度需要的是 **欧氏范数**（2-范数）。因此定义 `euclidNormSq x := x ⬝ᵥ x`（dot product with itself），对应 $\sum_i x_i^2$，是唯一正确的选择。这也使得正交保范的证明可以直接通过矩阵运算完成，无需借助 `EuclideanSpace`。

## 数学意义

高斯分布在正交变换下不变，体现了各向同性高斯分布的**球对称性**：密度函数只依赖于 $\|\mathbf{x}\|^2$，而正交矩阵恰好保持欧氏范数，因此密度不变。这一性质是：
- PCA（主成分分析）中坐标旋转合法性的基础
- ICA（独立成分分析）中高斯分布不可识别性的根源（书中第2章讨论的核心）
- 多元统计理论中"旋转等价性"的数学表达
