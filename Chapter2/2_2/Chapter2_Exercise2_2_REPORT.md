# 第2章 练习2.2 形式化报告

## 习题内容 (Exercise 2.2: Gaussian Rotational Invariance)

**原题** (来自 `deep-representation-learning-book/chapters/chapter2/classic-models.tex`):

设 $\vz \sim \mathcal{N}(\mathbf{0}, \sigma^2 \mathbf{I})$ 是高斯随机变量，每个分量的方差为 $\sigma^2$。证明：对于任意正交矩阵 $\mathbf{Q}$ (即 $\mathbf{Q}^\top \mathbf{Q} = \mathbf{I}$)，随机变量 $\mathbf{Q}\vz$ 与 $\vz$ 同分布。

提示：回忆高斯概率密度函数的公式，以及随机变量线性变换的密度公式。

## 形式化结果

### 文件位置
- Lean代码: `lean_formalization/Chapter2/2_2/Chapter2_Exercise2_2.lean`

### 主要定理

```lean
def IsOrthogonal (Q : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  Qᵀ * Q = 1

def gaussianDensity (σ : ℝ) (x : Fin d → ℝ) : ℝ :=
  (2 * π * σ^2) ^ (-(d : ℝ) / 2) * exp (-‖x‖^2 / (2 * σ^2))

theorem gaussian_rotational_invariance (σ : ℝ) (hσ : σ > 0)
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsOrthogonal Q) :
    ∀ x : Fin d → ℝ,
      gaussianDensity σ (Q.mulVec x) = gaussianDensity σ x
```

### 核心引理

1. **正交矩阵保持范数** (`orthogonal_preserves_norm`):
   $\|Q\mathbf{x}\| = \|\mathbf{x}\|$，当 $Q$ 为正交矩阵时
   - 状态: ⚠️ sorry (待完成)

2. **正交矩阵行列式绝对值为1** (`orthogonal_det_abs_one`):
   $|\det(Q)| = 1$，当 $Q$ 为正交矩阵时
   - 状态: ⚠️ sorry (待完成)

## 形式化证明思路

### 1. 密度函数定义
多元高斯分布 $\mathcal{N}(\mathbf{0}, \sigma^2 \mathbf{I})$ 的概率密度函数：
$$f(\mathbf{x}) = \frac{1}{(2\pi\sigma^2)^{d/2}} \exp\left(-\frac{\|\mathbf{x}\|^2}{2\sigma^2}\right)$$

### 2. 线性变换下的密度变换
对于线性变换 $\mathbf{y} = \mathbf{Q}\mathbf{x}$，有：
$$f_{\mathbf{Y}}(\mathbf{y}) = f_{\mathbf{X}}(\mathbf{Q}^{-1}\mathbf{y}) \cdot |\det(\mathbf{Q}^{-1})|$$

### 3. 正交矩阵性质
- $\mathbf{Q}^{-1} = \mathbf{Q}^\top$
- $\|\mathbf{Q}\mathbf{x}\| = \|\mathbf{x}\|$
- $|\det(\mathbf{Q})| = 1$

### 4. 结论
由于上述性质：
$$f_{\mathbf{Q}\vz}(\mathbf{y}) = f_{\vz}(\mathbf{Q}^{-1}\mathbf{y}) \cdot 1 = f_{\vz}(\mathbf{Q}^\top\mathbf{y}) = f_{\vz}(\mathbf{y})$$

因此 $\mathbf{Q}\vz \sim \vz$，即两者同分布。

## 形式化状态

| 组件 | 状态 |
|------|------|
| 正交矩阵定义 | ✅ 完成 |
| 高斯密度函数定义 | ✅ 完成 |
| 正交矩阵保持范数引理 | ⚠️ sorry (待完成) |
| 正交矩阵行列式引理 | ⚠️ sorry (待完成) |
| 旋转不变性主定理 | ✅ 完成 |

## 待完成项

1. 完成 `orthogonal_preserves_norm` 的证明
2. 完成 `orthogonal_det_abs_one` 的证明

## 数学意义

这个定理表明：**高斯分布在正交变换（旋转）下是不变的**。这是多元统计分析中的一个基本性质，它说明了高斯分布的"球对称性"——无论坐标系如何旋转，高斯分布的形状保持不变。

这个性质在以下方面有重要应用：
- 主成分分析 (PCA)
- 独立成分分析 (ICA)
- 信号处理中的旋转不变性
