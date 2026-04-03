# 第2章 练习2.5 第2部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.5（峰度线性性质），第2部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex:2308`
**日期**：2026-04-03

## 非形式化陈述

设 $X$ 是随机变量，$\alpha \in \mathbb{R}$ 为任意实数标量。

**第2部分**：证明 $\mathrm{kurt}(\alpha X) = \alpha^4 \, \mathrm{kurt}(X)$。

其中峰度定义为（书中公式 kurtosis）：
$$\mathrm{kurt}(X) = \mathbb{E}[X^4] - 3\bigl(\mathbb{E}[X^2]\bigr)^2$$

## 非形式化证明思路

**展开 $(\alpha X)^4$ 和 $(\alpha X)^2$**：
$$
(\alpha X)^4 = \alpha^4 X^4, \qquad (\alpha X)^2 = \alpha^2 X^2
$$

**取期望**，利用期望的线性性（常数倍提出）：
$$
\mathbb{E}[(\alpha X)^4] = \mathbb{E}[\alpha^4 X^4] = \alpha^4 \mathbb{E}[X^4]
$$
$$
\mathbb{E}[(\alpha X)^2] = \mathbb{E}[\alpha^2 X^2] = \alpha^2 \mathbb{E}[X^2]
$$

**代入峰度定义**：
$$
\mathrm{kurt}(\alpha X) = \alpha^4 \mathbb{E}[X^4] - 3\bigl(\alpha^2 \mathbb{E}[X^2]\bigr)^2
= \alpha^4 \mathbb{E}[X^4] - 3\alpha^4\bigl(\mathbb{E}[X^2]\bigr)^2
= \alpha^4 \bigl(\mathbb{E}[X^4] - 3(\mathbb{E}[X^2])^2\bigr)
= \alpha^4 \, \mathrm{kurt}(X)
$$

## 形式化策略

### Lean 中使用的关键 Mathlib 工具

| 工具 | 用途 |
|------|------|
| `MeasureTheory.integral_const_mul` | $\int c \cdot f \, d\mu = c \cdot \int f \, d\mu$（无需可积性前提） |
| `MeasureTheory.integral_congr_ae` / `ext` | 逐点等式化简被积函数 |
| `ring` | 最终代数化简 |

### 无可积性假设

与习题 2.5.1 不同，本定理**无需任何可积性假设**。
原因：`integral_const_mul` 在 Mathlib 中无条件成立——若被积函数不可积，两边均为 0。

### 文件结构

```
Chapter2_Exercise2_5_2.lean
├── import Chapter2.«2_5».Chapter2_Exercise2_5_1   -- 复用 kurtosis 定义
└── exercise_2_5_part_2                             -- 主定理
```

### 假设

定理 `exercise_2_5_part_2` 的前提条件：

| 假设 | 含义 |
|------|------|
| `X : Ω → ℝ` | 随机变量 X |
| `α : ℝ` | 任意实数标量 |

（无可测性、无可积性、无零均值要求）

## 形式化状态

### ✅ 完全完成（零 sorry）

**主定理**：
```lean
theorem exercise_2_5_part_2
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (X : Ω → ℝ) (α : ℝ) :
    kurtosis (fun ω => α * X ω) μ = α ^ 4 * kurtosis X μ
```
**状态**：完整证明，无 sorry，无公理警告。

## 验证

### 公理检查

```
propext, Classical.choice, Quot.sound
```

✅ 仅标准公理，无自定义公理。

### 关键技术细节

1. **函数外延性 (`ext`)**：
   将 `(fun ω => (α * X ω) ^ 4)` 化为 `(fun ω => α ^ 4 * X ω ^ 4)` 时，
   使用 `ext ω; ring` 建立逐点等式，再用 `integral_congr_ae` 等价为…
   实际上直接用 `have : (fun ω => ...) = (fun ω => ...)  := by ext ω; ring`
   配合 `rw [this, integral_const_mul]` 即可，无需 `integral_congr_ae`。

2. **`integral_const_mul` 的签名**：
   ```lean
   MeasureTheory.integral_const_mul (r : L) (f : α → L) :
       ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
   ```
   适用于 `RCLike L`（包含 `ℝ`），无可积性前提。

3. **最终代数化简**：
   代入 `h4` 和 `h2` 后，目标化为：
   ```
   α ^ 4 * ∫ ω, X ω ^ 4 ∂μ - 3 * (α ^ 2 * ∫ ω, X ω ^ 2 ∂μ) ^ 2
   = α ^ 4 * (∫ ω, X ω ^ 4 ∂μ - 3 * (∫ ω, X ω ^ 2 ∂μ) ^ 2)
   ```
   由 `ring` 自动完成。

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.MeasureTheory.Integral.Bochner.Basic` | `integral_const_mul` |

（通过 `import Chapter2.«2_5».Chapter2_Exercise2_5_1` 间接引入 `import Mathlib`）

## 与书中的对应关系

| 书中陈述 | Lean 形式化 | 状态 |
|---------|------------|------|
| $\mathrm{kurt}(\alpha X) = \alpha^4 \, \mathrm{kurt}(X)$ | `exercise_2_5_part_2` | ✅ 完整证明 |

## 与习题 2.5.1 的对比

| 维度 | 习题 2.5.1（加法性） | 习题 2.5.2（齐次性） |
|------|---------------------|---------------------|
| 核心工具 | 独立性、期望分解 | 积分常数倍 |
| 假设数量 | 9 个（可测性、独立性、零均值、7 个可积性） | 0 个 |
| 辅助引理 | 5 个 | 0 个 |
| 证明行数 | ~60 行（主定理体） | 12 行 |
| 最终步骤 | `ring` | `ring` |

## 总结

**完成度**：100%（零 sorry）

练习2.5 第2部分完全形式化完成。证明极为简洁：
- 两步逐点化简（`ext ω; ring`）+ 积分常数提出（`integral_const_mul`）
- `ring` 完成代数化简

这是本项目中假设最少、证明最短的定理之一，体现了 Lean 4 对纯代数推导的高效处理。
