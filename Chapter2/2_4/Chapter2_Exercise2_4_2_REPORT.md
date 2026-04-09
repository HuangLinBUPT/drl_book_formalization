# 第2章 练习2.4 第2部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.4（`exercise:whitening`），第2部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex:2296`
**Lean 文件**：`lean_formalization/Chapter2/2_4/Chapter2_Exercise2_4_2.lean`
**日期**：2026-04-09

## 非形式化陈述

书中第 2.4 题第 2 问要求证明：

> the *whitened matrix* $(Y Y^\top)^{-1/2}Y$ exists in expectation whenever
> $\operatorname{Cov}(z)$ is nonsingular, and that it has identity empirical covariance.

这里的数学核心可以拆成两层：

1. **线性代数层**：若矩阵 $Y Y^\top$ 可逆，则可以定义白化矩阵
   $$
   (Y Y^\top)^{-1/2}Y,
   $$
   并证明其经验协方差为单位阵。
2. **概率层**：若随机变量 $z$ 的协方差 $\operatorname{Cov}(z)$ 非奇异，则在“期望意义/高概率意义”下，样本矩阵对应的 Gram 矩阵可逆，从而白化矩阵存在。

当前 Lean 文件完整形式化了第 1 层，并为第 2 层提供了一个纯线性代数桥接条件：

- 若 `Y` 的行向量线性无关（满行秩），则 `Y * Yᵀ` 非奇异；
- 因而可以定义逆平方根白化矩阵，并证明其经验协方差为单位阵。

## 非形式化证明思路

### 第一步：白化矩阵的代数目标

设

$$
W := (Y Y^\top)^{-1/2} Y.
$$

则其经验协方差为

$$
W W^\top
= (Y Y^\top)^{-1/2} Y Y^\top ((Y Y^\top)^{-1/2})^\top.
$$

如果 $(Y Y^\top)^{-1/2}$ 确实是 Gram 矩阵 $Y Y^\top$ 的逆平方根，那么上式应化简为单位阵：

$$
W W^\top = I.
$$

因此白化证明的核心是一个纯矩阵恒等式。

### 第二步：为什么“可逆性”足够

只要 $Y Y^\top$ 非奇异，就可以取它的正平方根 $S = (Y Y^\top)^{1/2}$，再令

$$
W = S^{-1} Y.
$$

因为 $S S = Y Y^\top$，所以

$$
W W^\top = S^{-1}(Y Y^\top)(S^{-1})^\top = I.
$$

因此“白化矩阵存在并具有单位经验协方差”的核心前提，可以被 Lean 中的纯线代条件

$$
Y Y^\top \text{ 可逆}
$$

所替代。

### 第三步：从满行秩推出可逆性

如果 `Y` 的行向量线性无关，那么 `Y` 具有满行秩。此时对任意向量 $v$，

$$
(Y Y^\top) v = 0
$$

可推出

$$
Y^\top v = 0.
$$

而行向量线性无关等价于 $Y^\top$ 诱导的线性映射是单射，因此 $v=0$。这说明

$$
Y Y^\top
$$

对应的线性映射也是单射，故该方阵可逆。

这就给出了从“适当满秩条件”到“可白化”的桥梁。

## 形式化策略

### 主要建模对象

| Lean 对象 | 数学含义 | 类型 |
|----------|----------|------|
| `Y` | 低维坐标矩阵 | `Matrix (Fin d) (Fin N) ℝ` |
| `Y * Yᵀ` | Gram 矩阵 | `Matrix (Fin d) (Fin d) ℝ` |
| `gramPosSqrt d N Y` | Gram 矩阵的正平方根 $(Y Y^\top)^{1/2}$ | `Matrix (Fin d) (Fin d) ℝ` |
| `(gramPosSqrt d N Y)⁻¹ * Y` | 白化矩阵 | `Matrix (Fin d) (Fin N) ℝ` |

### Lean 中使用的关键 Mathlib 工具

| 工具 | 用途 |
|------|------|
| `Matrix.posSemidef_self_mul_conjTranspose` | 证明 `Y * Yᵀ` 正半定 |
| `CFC.sqrt` | 构造矩阵正平方根 |
| `CFC.sqrt_mul_sqrt_self` | 证明平方根平方回到原矩阵 |
| `CFC.isUnit_sqrt_iff` | 把平方根的可逆性与原矩阵的可逆性等价起来 |
| `Matrix.transpose_nonsing_inv` | 处理逆矩阵与转置 |
| `Matrix.self_mul_conjTranspose_mulVec_eq_zero` | 从 `(Y Yᵀ)v = 0` 推出 `Yᵀ v = 0` |
| `Matrix.mulVec_injective_iff` | 将 `mulVec` 单射转成列线性无关 |
| `Matrix.mulVec_injective_iff_isUnit` | 将方阵 `mulVec` 单射转成矩阵可逆 |

### 形式化分层

当前文件将书中第 2 问拆成三层定理：

```text
exercise_2_4_2
├── whitening_has_identity_empirical_covariance   任意白化见证 M 的核心恒等式
├── exercise_2_4_2_inv_sqrt_form                  用逆平方根给出书本形式的白化矩阵
├── exercise_2_4_2_exists_whitening               “存在白化矩阵”的线性代数版本
├── rows_linearIndependent_implies_gram_isUnit    满行秩 ⇒ Y Yᵀ 可逆
└── exercise_2_4_2_from_row_full_rank             满行秩 ⇒ 逆平方根白化成立
```

## 关键证明步骤

### 1. Gram 矩阵正半定与正平方根

首先证明

```lean
private theorem gram_posSemidef ... :
  (Y * Yᵀ).PosSemidef
```

这说明 `Y * Yᵀ` 落在 `CFC.sqrt` 可处理的正矩阵范围内。

随后定义：

```lean
noncomputable def gramPosSqrt ... :=
  CFC.sqrt (Y * Yᵀ)
```

并证明：

```lean
private theorem gramPosSqrt_mul_self ... :
  gramPosSqrt d N Y * gramPosSqrt d N Y = Y * Yᵀ
```

这一步是 Lean 中对

$$
S^2 = Y Y^\top
$$

的正式表达。

### 2. 白化核心恒等式

定理

```lean
whitening_has_identity_empirical_covariance
```

形式化了如下最基础的代数事实：若一个矩阵 `M` 满足

$$
M (Y Y^\top) M^\top = I,
$$

则对 `W = M Y` 有

$$
W W^\top = I.
$$

Lean 中的证明几乎就是逐步重写：

```lean
(M * Y) * (M * Y)ᵀ = M * (Y * Yᵀ) * Mᵀ
```

然后代入假设 `hM`。

### 3. 书本形式的逆平方根白化

定理

```lean
exercise_2_4_2_inv_sqrt_form
```

直接对应书中的矩阵形式，只不过 Lean 中把

$$
(Y Y^\top)^{1/2}
$$

实现为 `gramPosSqrt d N Y`。

证明结构是：

1. 假设 `Y * Yᵀ` 可逆；
2. 推出 `gramPosSqrt d N Y` 也可逆；
3. 构造
   $$
   W := (gramPosSqrt d N Y)^{-1} Y;
   $$
4. 验证
   $$
   (gramPosSqrt d N Y)^{-1} (Y Y^\top) ((gramPosSqrt d N Y)^{-1})^\top = I;
   $$
5. 套用白化核心恒等式。

这是当前文件中最贴近书面公式

$$
(Y Y^\top)^{-1/2}Y
$$

的地方。

### 4. 线性代数“存在性”定理

定理

```lean
exercise_2_4_2_exists_whitening
```

将前述结果改写成“存在某个白化矩阵”的形式：

- 若 `Y * Yᵀ` 非奇异，
- 则存在 `M_invSqrt = (gramPosSqrt d N Y)⁻¹`，
- 使得 `M_invSqrt * Y` 的经验协方差为单位阵。

这对应了书中“whitened matrix exists”的**纯线代版本**。

### 5. 满行秩桥接引理

定理

```lean
rows_linearIndependent_implies_gram_isUnit
```

是本次增强 2.4.2 的关键新增内容。

其思路是：

1. `LinearIndependent ℝ Y.row` 推出 `Yᵀ.mulVec` 单射；
2. 若 `(Y * Yᵀ) *ᵥ (v - w) = 0`，则由
   `Matrix.self_mul_conjTranspose_mulVec_eq_zero` 推出
   `Yᵀ *ᵥ (v - w) = 0`；
3. 由于 `Yᵀ.mulVec` 单射，得到 `v = w`；
4. 所以 `(Y * Yᵀ).mulVec` 单射；
5. 方阵上 `mulVec` 单射等价于矩阵可逆，因此 `IsUnit (Y * Yᵀ)`。

这一步把“样本矩阵在低维空间中没有退化”形式化为一个完全可检查的充分条件。

### 6. 从满行秩直接推出白化结论

定理

```lean
exercise_2_4_2_from_row_full_rank
```

把桥接引理与逆平方根白化定理直接拼接起来：

- 假设 `Y.row` 线性无关；
- 先得出 `Y * Yᵀ` 可逆；
- 再推出白化矩阵 `(gramPosSqrt d N Y)⁻¹ * Y` 具有单位经验协方差。

从叙述上说，这是目前文件中最接近书本“在合理非退化条件下白化成立”的版本。

## 与书中原句的对应关系

书中原句：

> the *whitened matrix* $(Y Y^\top)^{-1/2}Y$ exists in expectation whenever
> $\operatorname{Cov}(z)$ is nonsingular, and that it has identity empirical covariance.

当前 Lean 形式化对应如下：

| 书中片段 | Lean 对应 | 状态 |
|---------|-----------|------|
| 白化矩阵 $(Y Y^\top)^{-1/2}Y$ | `(gramPosSqrt d N Y)⁻¹ * Y` | ✅ |
| has identity empirical covariance | `exercise_2_4_2_inv_sqrt_form` | ✅ |
| exists | `exercise_2_4_2_exists_whitening` | ✅（线代版本） |
| whenever `Cov(z)` is nonsingular | 尚未直接形式化 | ⏳ |
| exists in expectation | 尚未直接形式化 | ⏳ |

因此，这个 Lean 文件已经完整覆盖了**白化矩阵的线性代数核心**，但还没有进入协方差随机变量、样本矩阵和“期望意义存在性”的概率层。

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `gram_posSemidef` | `Y * Yᵀ` 正半定 | ✅ |
| `gramPosSqrt_mul_self` | `(Y Yᵀ)^{1/2}` 的平方回到 `Y Yᵀ` | ✅ |
| `whitening_has_identity_empirical_covariance` | 任意白化见证给出单位经验协方差 | ✅ |
| `exercise_2_4_2` | 白化核心定理 | ✅ |
| `exercise_2_4_2_inv_sqrt_form` | 逆平方根形式的白化结论 | ✅ |
| `exercise_2_4_2_exists_whitening` | 白化矩阵存在的线代版本 | ✅ |
| `rows_linearIndependent_implies_gram_isUnit` | 满行秩推出 Gram 矩阵可逆 | ✅ |
| `exercise_2_4_2_from_row_full_rank` | 满行秩下直接得到白化结论 | ✅ |

## 验证

### 编译状态

```text
lean_diagnostic_messages → success: true, items: []
lake env lean Chapter2/2_4/Chapter2_Exercise2_4_2.lean → success
```

✅ 零错误，零 warning，零 sorry。

### 公理检查

```text
propext, Classical.choice, Quot.sound
```

✅ 无自定义公理。

## Mathlib 依赖

| 模块/工具 | 用途 |
|-----------|------|
| `Mathlib` | 总入口，覆盖矩阵、正定性、CFC、线性代数 API |
| `MatrixOrder` | 为矩阵提供 `≤` 顺序结构，使 `CFC.sqrt` 可用 |
| `CFC.sqrt` | 构造 Gram 矩阵平方根 |
| `CFC.isUnit_sqrt_iff` | 平方根与原矩阵可逆性的等价 |
| `Matrix.self_mul_conjTranspose_mulVec_eq_zero` | 把 Gram 零向量条件退化回 `Yᵀ` 的零向量条件 |
| `Matrix.mulVec_injective_iff_isUnit` | 从单射得到矩阵可逆 |

## 与 2.4 系列其余部分的关系

| 部分 | 内容 | 当前文件提供的作用 |
|------|------|------------------|
| 2.4.1 | `X = VY`，其中 `VᵀV = I` | 提供低维正交坐标表示 `Y` |
| 2.4.2（本文件） | 白化矩阵存在与单位经验协方差 | 对 `Y` 做 Gram 白化 |
| 2.4.3 | SVD 视角下将白化矩阵写成 `W [z₁, …, z_N]` | 需要本文件的白化结果作为输入 |

从数学流程看，2.4.1 先把样本投影到一个正交的 `d` 维坐标系中，2.4.2 再对白化矩阵进行构造与验证，2.4.3 则进一步通过 SVD 解释白化后的结构。

## 总结

**完成度**：当前线性代数核心部分 100%（零 sorry）

本文件已经成功把书中第 2.4.2 问的**矩阵白化核心**形式化为 Lean 代码。它证明了：

1. 若存在矩阵 `M` 使得 `M (Y Yᵀ) Mᵀ = I`，则 `MY` 的经验协方差为单位阵；
2. 若 `Y Yᵀ` 非奇异，则可以取 `M = (Y Yᵀ)^{-1/2}` 的 Lean 版本，从而得到书本同型的白化矩阵；
3. 若进一步假设 `Y` 满行秩，则 `Y Yᵀ` 自动非奇异，因此白化矩阵的构造和单位经验协方差结论都成立。

这份形式化的主要价值在于：

- **把书中的白化公式真正落到可检查的矩阵定理上**；
- **用 `CFC.sqrt` 严格实现了矩阵正平方根**，避免停留在符号层；
- **给出一个纯线代桥接条件**，为未来从 `Cov(z)` 非奇异推进到样本矩阵可逆性提供了接口。

尚未完成的部分，是书中带概率意味的那一句：

> exists in expectation whenever `Cov(z)` is nonsingular.

那需要进一步引入随机向量、样本矩阵、协方差以及集中不等式/高概率可逆性的形式化工具。当前文件尚未覆盖这一层，但已经把其所依赖的核心矩阵论部分全部完成。