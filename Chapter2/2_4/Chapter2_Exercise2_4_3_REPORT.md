# 第2章 练习2.4 第3部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.4（`exercise:whitening`），第3部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex:2304`
**Lean 文件**：`lean_formalization/Chapter2/2_4/Chapter2_Exercise2_4_3.lean`
**日期**：2026-04-11

## 非形式化陈述

书中第 2.4 题第 3 问要求证明：

> Show, by using the singular value decomposition of $U$, that the matrix $V$ can be
> chosen so that the whitened matrix satisfies
> $(YY^\top)^{-1/2}Y = W[z_1,\dots,z_N]$, where $W$ is an orthonormal matrix.

即：利用 $U$ 的奇异值分解（SVD），可以适当选取矩阵 $V$，使得由此得到的
白化矩阵 $(YY^\top)^{-1/2}Y$ 可以写成

$$
(YY^\top)^{-1/2}Y = W Z,
$$

其中 $W$ 是一个列正交矩阵，$Z = [z_1,\dots,z_N]$ 是潜在因子矩阵。

## 非形式化证明思路

### 第一步：对 $U$ 进行奇异值分解

设 $U \in \mathbb{R}^{D \times d}$ 的奇异值分解为

$$
U = P \Sigma Q^\top,
$$

其中：
- $P \in \mathbb{R}^{D \times d}$：左奇异向量矩阵，$P^\top P = I_d$；
- $\Sigma \in \mathbb{R}^{d \times d}$：对角奇异值矩阵，可逆且对称（$\Sigma^\top = \Sigma$）；
- $Q \in \mathbb{R}^{d \times d}$：右奇异向量矩阵，正交（$Q^\top Q = I_d$，$QQ^\top = I_d$）。

### 第二步：选取 $V = P$，确定 $Y$

取 $V = P$（左奇异向量矩阵）。则

$$
X = UZ = P\Sigma Q^\top Z = P \cdot (\Sigma Q^\top Z),
$$

因此令

$$
Y := \Sigma Q^\top Z.
$$

此时 $X = VY$ 成立，且 $V^\top V = P^\top P = I_d$，满足练习 2.4.1 中的正交分解条件。

### 第三步：计算 $YY^\top$（在 $ZZ^\top = I$ 的条件下）

在经验协方差为单位阵的假设 $ZZ^\top = I_d$ 下，

$$
YY^\top
= \Sigma Q^\top Z Z^\top Q \Sigma
= \Sigma Q^\top \cdot I_d \cdot Q \Sigma
= \Sigma (Q^\top Q) \Sigma
= \Sigma \cdot I_d \cdot \Sigma
= \Sigma^2.
$$

### 第四步：取白化算子 $M = \Sigma^{-1}$

由于 $YY^\top = \Sigma^2$，取

$$
M_{\text{invSqrt}} := \Sigma^{-1}.
$$

**验证白化条件**：

$$
M_{\text{invSqrt}} (YY^\top) M_{\text{invSqrt}}^\top
= \Sigma^{-1} \Sigma^2 \Sigma^{-1}
= (\Sigma^{-1}\Sigma)(\Sigma\Sigma^{-1})
= I_d \cdot I_d = I_d.
$$

**验证白化等式**：

$$
M_{\text{invSqrt}} Y = \Sigma^{-1}(\Sigma Q^\top Z) = (\Sigma^{-1}\Sigma) Q^\top Z = I_d \cdot Q^\top Z = Q^\top Z.
$$

### 第五步：确定正交矩阵 $W$

令

$$
W := Q^\top.
$$

则 $W$ 正交：

$$
W W^\top = Q^\top (Q^\top)^\top = Q^\top Q = I_d.
$$

并且

$$
(YY^\top)^{-1/2} Y = \Sigma^{-1} Y = Q^\top Z = W Z.
$$

这正是书中所要求的等式。

## 形式化策略

### 主要建模对象

| Lean 对象 | 数学含义 | 类型 |
|----------|----------|------|
| `P` | 左奇异向量矩阵 | `Matrix (Fin D) (Fin d) ℝ` |
| `Sigma` | 奇异值对角矩阵 | `Matrix (Fin d) (Fin d) ℝ` |
| `Q` | 右奇异向量矩阵 | `Matrix (Fin d) (Fin d) ℝ` |
| `Z` | 潜在因子矩阵 $[z_1,\dots,z_N]$ | `Matrix (Fin d) (Fin N) ℝ` |
| `U := P * Sigma * Qᵀ` | 数据生成矩阵（SVD 形式） | `Matrix (Fin D) (Fin d) ℝ` |
| `X := U * Z` | 数据矩阵 | `Matrix (Fin D) (Fin N) ℝ` |
| `V := P` | 正交因子矩阵 | `Matrix (Fin D) (Fin d) ℝ` |
| `Y := Sigma * Qᵀ * Z` | 低维坐标矩阵 | `Matrix (Fin d) (Fin N) ℝ` |
| `W := Qᵀ` | 白化后的正交矩阵 | `Matrix (Fin d) (Fin d) ℝ` |
| `Sigma⁻¹` | 白化算子 $(YY^\top)^{-1/2}$ 的具体实现 | `Matrix (Fin d) (Fin d) ℝ` |

### 假设

| 假设名 | 数学含义 |
|--------|----------|
| `hP : Pᵀ * P = 1` | $P$ 列正交 |
| `hQ_left : Qᵀ * Q = 1` | $Q$ 左正交 |
| `hQ_right : Q * Qᵀ = 1` | $Q$ 右正交（本证明未用，留作完整性） |
| `hSigma_unit : IsUnit Sigma` | $\Sigma$ 可逆 |
| `hSigma_sym : Sigmaᵀ = Sigma` | $\Sigma$ 对称（对角矩阵） |
| `hZZt : Z * Zᵀ = 1` | 经验协方差为单位阵 |

### 主定理结构

```
exercise_2_4_3
├── hXVY    : X = V * Y              （P * Sigma * Qᵀ * Z = P * (Sigma * Qᵀ * Z)）
├── hP      : Vᵀ * V = 1            （直接来自假设 hP）
├── hWWt    : W * Wᵀ = 1            （Qᵀ * Q = I，即 hQ_left）
├── hYYt    : Y * Yᵀ = Sigma * Sigma （关键计算：利用 hZZt 和 hQ_left）
├── hwhiten : Σ⁻¹ * (Y Yᵀ) * (Σ⁻¹)ᵀ = 1  （白化条件）
└── hMY_WZ  : Σ⁻¹ * Y = Qᵀ * Z     （白化等式：(Y Yᵀ)^{-1/2} Y = W Z）
```

## 关键证明步骤

### 1. $X = V \cdot Y$ 的证明

目标为

$$
P \cdot \Sigma \cdot Q^\top \cdot Z = P \cdot (\Sigma \cdot Q^\top \cdot Z).
$$

这是纯矩阵乘法结合律。在 Lean 中用：

```lean
rw [Matrix.mul_assoc P, Matrix.mul_assoc P]
```

关键点：需要以 `P` 为左端点的 `mul_assoc`，而不是普通的泛型 `mul_assoc`（后者会改变结合方式，导致形式不符合目标）。

### 2. $W \cdot W^\top = I$ 的证明

目标为

$$
Q^\top \cdot (Q^\top)^\top = Q^\top Q = I.
$$

```lean
rw [Matrix.transpose_transpose]; exact hQ_left
```

### 3. 核心计算 $Y \cdot Y^\top = \Sigma^2$

这是全证明中最实质性的计算步骤。展开转置后，目标变为

$$
\Sigma \cdot Q^\top \cdot Z \cdot (Z^\top \cdot (Q \cdot \Sigma)) = \Sigma \cdot \Sigma.
$$

先用 `simp [Matrix.mul_assoc]` 把左端重排为

$$
\Sigma \cdot (Q^\top \cdot (Z \cdot Z^\top) \cdot Q) \cdot \Sigma,
$$

再依次代入：
- $Z Z^\top = I$（`hZZt`）：消去 $Z Z^\top$，得 $\Sigma \cdot (Q^\top \cdot Q) \cdot \Sigma$；
- $Q^\top Q = I$（`hQ_left`）：得 $\Sigma \cdot I \cdot \Sigma = \Sigma^2$。

```lean
have : Sigma * Qᵀ * Z * (Zᵀ * (Q * Sigma)) =
       Sigma * (Qᵀ * (Z * Zᵀ) * Q) * Sigma := by
  simp [Matrix.mul_assoc]
rw [this, hZZt, Matrix.mul_one, hQ_left, Matrix.mul_one]
```

### 4. 白化条件 $\Sigma^{-1}(YY^\top)(\Sigma^{-1})^\top = I$

代入 $YY^\top = \Sigma^2$ 后，目标变为

$$
\Sigma^{-1} \cdot \Sigma^2 \cdot \Sigma^{-1} = I.
$$

利用矩阵乘法结合律重排为

$$
(\Sigma^{-1}\Sigma) \cdot (\Sigma\Sigma^{-1}) = I \cdot I = I.
$$

```lean
have : Sigma⁻¹ * (Sigma * Sigma) * Sigma⁻¹ =
       (Sigma⁻¹ * Sigma) * (Sigma * Sigma⁻¹) := by
  simp [Matrix.mul_assoc]
rw [this, hSigma_inv_l, hSigma_inv_r, Matrix.mul_one]
```

另需处理转置：`(Sigma⁻¹)ᵀ = Sigma⁻¹`，
通过 `Matrix.transpose_nonsing_inv` 和 `hSigma_sym` 化简。

### 5. 白化等式 $\Sigma^{-1} Y = W Z$

目标为

$$
\Sigma^{-1} \cdot (\Sigma \cdot Q^\top \cdot Z) = Q^\top \cdot Z.
$$

利用结合律把左端整理为 $(\Sigma^{-1}\Sigma) \cdot Q^\top \cdot Z$，再代入 $\Sigma^{-1}\Sigma = I$：

```lean
have : Sigma⁻¹ * (Sigma * Qᵀ * Z) = (Sigma⁻¹ * Sigma) * Qᵀ * Z := by
  simp [Matrix.mul_assoc]
rw [this, hSigma_inv_l, Matrix.one_mul]
```

## 与书中原句的对应关系

书中原句：

> Show, by using the singular value decomposition of $U$, that the matrix $V$ can be
> chosen so that the whitened matrix satisfies $(YY^\top)^{-1/2}Y = W[z_1,\dots,z_N]$,
> where $W$ is an orthonormal matrix.

| 书中片段 | Lean 对应 | 状态 |
|---------|-----------|------|
| SVD 分解 $U = P\Sigma Q^\top$ | 参数化为 `P`, `Sigma`, `Q` 三个矩阵及其正交性假设 | ✅ |
| 选取 $V$ | `V := P`（左奇异向量矩阵） | ✅ |
| $X = VY$ | `hXVY` | ✅ |
| $V^\top V = I$ | `hP`（直接假设） | ✅ |
| $(YY^\top)^{-1/2}Y = WZ$ | `hMY_WZ : Sigma⁻¹ * Y = Qᵀ * Z` | ✅ |
| $W$ 正交 | `hWWt : Qᵀ * Q = I` | ✅ |
| 白化条件成立 | `hwhiten` | ✅ |

**形式化的精炼点**：书中隐含了"$Z Z^\top = I$"这一经验协方差假设（即潜在因子在样本上是正交归一的）。当前 Lean 文件将这一条件显式化为参数 `hZZt : Z * Zᵀ = 1`，明确了该结论成立所需的代数前提。

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `exercise_2_4_3` | SVD 白化：存在 $V,W,\Sigma^{-1}$ 使 $(YY^\top)^{-1/2}Y = WZ$ | ✅ |

## 验证

### 编译状态

```text
lean_diagnostic_messages → success: true, items: []
```

✅ 零错误，零 sorry。

唯一警告：`hQ_right` 未使用（`Q * Qᵀ = 1`），属于完整性参数，不影响正确性。

### 公理检查

```text
propext, Classical.choice, Quot.sound
```

✅ 无自定义公理。

## Mathlib 依赖

| 工具 | 用途 |
|------|------|
| `Matrix.mul_assoc` | 矩阵乘法结合律（带显式参数） |
| `Matrix.transpose_mul` | 展开乘积的转置 |
| `Matrix.transpose_transpose` | 双重转置化简 |
| `Matrix.transpose_nonsing_inv` | 逆矩阵的转置等于转置的逆 |
| `Matrix.nonsing_inv_mul` | $\Sigma^{-1}\Sigma = I$（需要 `IsUnit det`） |
| `Matrix.mul_nonsing_inv` | $\Sigma\Sigma^{-1} = I$ |
| `IsUnit.map Matrix.detMonoidHom` | 从 `IsUnit Sigma` 推出 `IsUnit (det Sigma)` |

## 与 2.4 系列的关系

| 部分 | 内容 | 相互关系 |
|------|------|----------|
| 2.4.1 | $\operatorname{rank}(X) \le d$ 且存在 $X = VY$，$V^\top V = I$ | 本文件用 SVD 给出了一个具体的 $V = P$ |
| 2.4.2 | 白化矩阵 $(YY^\top)^{-1/2}Y$ 具有单位经验协方差 | 本文件中的 `hwhiten` 验证了白化条件；两者互补 |
| 2.4.3（本文件） | SVD 视角：$(YY^\top)^{-1/2}Y = WZ$ | 在 2.4.1 正交分解基础上，用 SVD 结构给出白化矩阵的显式因子分解 |

三部分共同构成了白化理论的完整线性代数基础：

1. **2.4.1**：样本矩阵存在正交低维分解 $X = VY$；
2. **2.4.2**：白化矩阵 $(YY^\top)^{-1/2}Y$ 具有单位经验协方差；
3. **2.4.3**：利用 SVD，白化后的结构还可以写成 $WZ$（正交变换作用于原始潜在因子）。

## 总结

**完成度**：100%（零 sorry）

本文件完整形式化了书中第 2.4.3 问的核心主张：

1. **SVD 分解的代入**：通过将 $U = P\Sigma Q^\top$ 的参数化代入数据模型，直接得到 $Y = \Sigma Q^\top Z$；
2. **核心代数计算**：在 $ZZ^\top = I$ 的条件下，推导出 $YY^\top = \Sigma^2$；
3. **白化矩阵的显式构造**：取 $\Sigma^{-1}$ 作为白化算子，验证其满足白化条件，并直接得到 $(YY^\top)^{-1/2}Y = Q^\top Z$；
4. **正交矩阵 $W$ 的识别**：$W = Q^\top$（右奇异向量矩阵的转置）是所要求的正交矩阵。

本形式化的核心价值在于：

- **将 SVD 结构显式化**：不依赖 Mathlib 的 SVD 定理机械推进，而是将奇异值分解的三要素 $(P, \Sigma, Q)$ 直接参数化，让证明结构与书中推导完全对应；
- **关键假设的显式化**：$ZZ^\top = I$ 这一代数条件被明确写出，揭示了定理成立的精确前提；
- **计算的完全可验证性**：所有矩阵等式都通过可机械检查的 `rw` / `simp` 步骤完成，无任何抽象跳跃。
