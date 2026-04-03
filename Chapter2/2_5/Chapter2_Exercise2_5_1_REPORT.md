# 第2章 练习2.5 第1部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.5（峰度线性性质），第1部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex:2308`
**日期**：2026-04-03

## 非形式化陈述

设 $X$ 和 $Y$ 是零均值独立随机变量。

**第1部分**：证明 $\mathrm{kurt}(X + Y) = \mathrm{kurt}(X) + \mathrm{kurt}(Y)$。

其中峰度定义为（书中公式 kurtosis）：
$$\mathrm{kurt}(X) = \mathbb{E}[X^4] - 3\bigl(\mathbb{E}[X^2]\bigr)^2$$

## 非形式化证明思路

**展开 $(X+Y)^4$**：
$$
(X+Y)^4 = X^4 + 4X^3Y + 6X^2Y^2 + 4XY^3 + Y^4
$$

**取期望**，利用独立性 $\mathbb{E}[f(X)g(Y)] = \mathbb{E}[f(X)]\mathbb{E}[g(Y)]$ 以及零均值 $\mathbb{E}[X]=\mathbb{E}[Y]=0$：
- $\mathbb{E}[X^3Y] = \mathbb{E}[X^3]\mathbb{E}[Y] = 0$（因为 $\mathbb{E}[Y]=0$）
- $\mathbb{E}[XY^3] = \mathbb{E}[X]\mathbb{E}[Y^3] = 0$（因为 $\mathbb{E}[X]=0$）
- $\mathbb{E}[X^2Y^2] = \mathbb{E}[X^2]\mathbb{E}[Y^2]$（独立性）

因此：
$$
\mathbb{E}[(X+Y)^4] = \mathbb{E}[X^4] + 6\mathbb{E}[X^2]\mathbb{E}[Y^2] + \mathbb{E}[Y^4]
$$

**展开 $(X+Y)^2$**：
$$
\mathbb{E}[(X+Y)^2] = \mathbb{E}[X^2] + 2\mathbb{E}[XY] + \mathbb{E}[Y^2] = \mathbb{E}[X^2] + \mathbb{E}[Y^2]
$$
（因为 $\mathbb{E}[XY] = \mathbb{E}[X]\mathbb{E}[Y] = 0$）

**代入峰度定义**：
$$
\mathrm{kurt}(X+Y) = \bigl(\mathbb{E}[X^4] + 6\mathbb{E}[X^2]\mathbb{E}[Y^2] + \mathbb{E}[Y^4]\bigr) - 3\bigl(\mathbb{E}[X^2] + \mathbb{E}[Y^2]\bigr)^2
$$
$$
= \mathbb{E}[X^4] + 6\mathbb{E}[X^2]\mathbb{E}[Y^2] + \mathbb{E}[Y^4] - 3(\mathbb{E}[X^2])^2 - 6\mathbb{E}[X^2]\mathbb{E}[Y^2] - 3(\mathbb{E}[Y^2])^2
$$
$$
= \bigl(\mathbb{E}[X^4] - 3(\mathbb{E}[X^2])^2\bigr) + \bigl(\mathbb{E}[Y^4] - 3(\mathbb{E}[Y^2])^2\bigr) = \mathrm{kurt}(X) + \mathrm{kurt}(Y)
$$

## 形式化策略

### Lean 中使用的关键 Mathlib 工具

| 工具 | 用途 |
|------|------|
| `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral` | $\mathbb{E}[(XY)(\omega)] = \mathbb{E}[X]\cdot\mathbb{E}[Y]$ |
| `ProbabilityTheory.IndepFun.comp` | 对可测函数复合保持独立性 |
| `MeasureTheory.integral_add` | 积分线性性：$\int(f+g) = \int f + \int g$ |
| `MeasureTheory.integral_const_mul` | 常数倍：$\int(c \cdot f) = c \cdot \int f$ |
| `MeasureTheory.integral_congr_ae` | 逐点相等蕴含积分相等 |

### 文件结构

```
Chapter2_Exercise2_5_1.lean
├── kurtosis                          -- 峰度定义
├── integral_mul_of_indepFun_zero_mean          -- E[XY]=0 引理
├── integral_cube_mul_of_indepFun_zero_mean_right -- E[X³Y]=0 引理
├── integral_mul_cube_of_indepFun_zero_mean_left  -- E[XY³]=0 引理
├── integral_sq_mul_sq_of_indepFun              -- E[X²Y²]=E[X²]E[Y²] 引理
├── integral_fourth_moment_expand      -- 展开 ∫(X+Y)⁴
└── exercise_2_5_part_1               -- 主定理
```

### 假设

定理 `exercise_2_5_part_1` 的前提条件：

| 假设 | 含义 |
|------|------|
| `hXm`, `hYm` | X, Y 可测 |
| `hI : IndepFun X Y μ` | X 与 Y 统计独立 |
| `hX0`, `hY0` | 零均值：$\mathbb{E}[X]=\mathbb{E}[Y]=0$ |
| `hX4`, `hY4` | $X^4, Y^4$ 可积 |
| `hX3Y`, `hXY3` | $X^3Y, XY^3$ 可积 |
| `hX2Y2` | $X^2Y^2$ 可积 |
| `hX2`, `hY2` | $X^2, Y^2$ 可积 |
| `hXY` | $XY$ 可积 |

这些可积性条件在实际应用中（如当 $X, Y$ 有有限四阶矩时）自然满足。

## 形式化状态

### ✅ 完全完成（零 sorry）

**主定理**：
```lean
theorem exercise_2_5_part_1 :
    kurtosis (fun ω => X ω + Y ω) μ = kurtosis X μ + kurtosis Y μ
```
**状态**：完整证明，无 sorry，无公理警告。

所有辅助引理也均已完整证明：
- `integral_mul_of_indepFun_zero_mean` ✅
- `integral_cube_mul_of_indepFun_zero_mean_right` ✅
- `integral_mul_cube_of_indepFun_zero_mean_left` ✅
- `integral_sq_mul_sq_of_indepFun` ✅
- `integral_fourth_moment_expand` ✅

## 验证

### 类型检查

```bash
$ lake env lean Chapter2/2_5/Chapter2_Exercise2_5_1.lean
# 无输出 = 无错误
```

✅ 文件类型检查通过，**零错误，零 sorry**。

### 关键技术细节

1. **`IndepFun.comp` 的使用**：
   `IndepFun.comp hI φ_meas ψ_meas : (φ ∘ f) ⟂ᵢ[μ] ψ ∘ g`
   需要用 `simpa` 将 `Function.comp` 化简为 `(fun ω => X ω ^ n)` 的形式。

2. **`integral_add` 的匹配**：
   `integral_add` 需要 `Pi.add_apply` 形式（`f + g`），
   而我们写成 `∫ ω, (A ω + B ω)` 形式。使用 `convert h using 1` 绕过此匹配问题，
   再用 `linarith` 组合多步拆分结果。

3. **最终代数化简**：
   代入所有矩的计算结果后，`ring` 自动完成代数化简。

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.Probability.Independence.Integration` | `IndepFun.integral_mul_eq_mul_integral`, `IndepFun.comp` |
| `Mathlib.MeasureTheory.Integral.Bochner.Basic` | `integral_add`, `integral_const_mul`, `integral_congr_ae` |

## 与书中的对应关系

| 书中陈述 | Lean 形式化 | 状态 |
|---------|------------|------|
| $\mathrm{kurt}(X+Y) = \mathrm{kurt}(X) + \mathrm{kurt}(Y)$ | `exercise_2_5_part_1` | ✅ 完整证明 |

## 总结

**完成度**：100%（零 sorry）

练习2.5 第1部分完全形式化完成。证明完整捕获了非形式化推导的所有步骤：
- 利用独立性消去混合矩
- 对 $(X+Y)^4$ 和 $(X+Y)^2$ 展开并用积分线性性分解
- 最终通过 `ring` 完成代数化简

这是本项目首个涉及概率论独立性与期望理论的完整证明（零 sorry）。
