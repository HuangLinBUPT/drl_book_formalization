# 第2章 练习2.7 第4部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.7（`exercise:kurtosis-sphere-landscape`），第4部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex`
**Lean 文件**：`lean_formalization/Chapter2/2_7/Chapter2_Exercise2_7_4.lean`
**日期**：2026-04-06

## 非形式化陈述

对球面约束峰度最大化问题

$$\max_{\|\mathbf{w}\|_2 = 1} f(\mathbf{w}) = \sum_i \kappa_i w_i^4$$

**假设**：$\kappa_j < 0$ 对所有 $j = 1, \dots, d$（"过度紧缩"情形）。

利用黎曼 Hessian（练习 2.6.3）证明该问题的唯一局部极大值是"符号稠密向量"：

$$w_\text{full} = \sum_{i=1}^d \pm\sqrt{\frac{\sigma_\text{full}}{\kappa_i}}\, e_i, \qquad
\sigma_\text{full} = \frac{1}{\displaystyle\sum_{j=1}^d \frac{1}{\kappa_j}} < 0$$

（即临界点公式中取 $S = \{1,\dots,d\}$ 全支撑的情形）。

## 非形式化证明思路

### 关键量的符号

- $\kappa_i < 0 \Rightarrow 1/\kappa_i < 0 \Rightarrow \sum_j 1/\kappa_j < 0 \Rightarrow \sigma_\text{full} < 0$
- $\sigma_\text{full}/\kappa_i > 0$（两负相除），从而 $\sqrt{\sigma_\text{full}/\kappa_i}$ 有意义
- $w_{\text{full},i}^2 = \sigma_\text{full}/\kappa_i$，即 $\kappa_i \cdot w_{\text{full},i}^2 = \sigma_\text{full}$

### 核心计算：全支撑临界点处的 Riemannian Hessian

目标函数值：

$$f(w_\text{full}) = \sigma_\text{full} \quad \text{（所有临界点均满足此性质）}$$

对任意 $v$，Hessian 二次型：

$$\text{Hess}\,f(w_\text{full})[v,v]
= \sum_i 12\kappa_i w_{\text{full},i}^2 v_i^2 - 4\sigma_\text{full}\|v\|^2$$

由于 $\kappa_i w_{\text{full},i}^2 = \sigma_\text{full}$ 对所有 $i$ 成立（全支撑，无零项）：

$$= 12\sigma_\text{full}\sum_i v_i^2 - 4\sigma_\text{full}\|v\|^2
= 12\sigma_\text{full}\|v\|^2 - 4\sigma_\text{full}\|v\|^2
= 8\sigma_\text{full}\|v\|^2$$

由于 $\sigma_\text{full} < 0$，故 $8\sigma_\text{full}\|v\|^2 \leq 0$，Hessian 负半定，$w_\text{full}$ 为局部极大值。

**注**：全支撑假设是关键——仅当 $S = \{1,\dots,d\}$ 时，$\kappa_i w_{\text{full},i}^2 = \sigma$ 对所有 $i$ 均成立，才能将求和 $\sum_i$ 整体化简为 $\sigma\|v\|^2$。

## 形式化策略

### 关键定义

| 定义名 | 数学含义 | Lean 类型 |
|--------|----------|-----------|
| `kurtObj₄ κ w` | $f(\mathbf{w}) = \sum_i \kappa_i w_i^4$ | `ℝ` |
| `sigma₄ κ S` | $\sigma_S = 1/(\sum_{j\in S} 1/\kappa_j)$ | `ℝ` |
| `critPoint₄ κ S` | $w_S$（坐标 $\sqrt{\sigma_S/\kappa_i}$ 或 $0$） | `EuclideanSpace ℝ (Fin d)` |
| `hessForm₄ κ w v` | $\sum_i 12\kappa_i w_i^2 v_i^2 - 4f(w)\|v\|^2$ | `ℝ` |

### 关键辅助引理

| 引理名 | 内容 |
|--------|------|
| `sum_inv_neg` | $\forall i \in S,\, \kappa_i < 0 \Rightarrow \sum_{j\in S} 1/\kappa_j < 0$ |
| `sigma₄_neg` | $\sigma_S < 0$（所有 $\kappa_i < 0$） |
| `sigma₄_div_pos` | $\sigma_S/\kappa_i > 0$（两负相除） |
| `sigma₄_mul_sum` | $\sigma_S \cdot \sum_j 1/\kappa_j = 1$ |
| `coord_sq_mul_kappa` | $\kappa_i \cdot w_{S,i}^2 = \sigma_S$（$i \in S$） |
| `kurtObj₄_critPoint` | $f(w_S) = \sigma_S$ |

### 主要定理

| 定理名 | 数学内容 |
|--------|----------|
| `hessForm₄_critPoint_univ` | $\text{hessForm}(\kappa, w_\text{full}, v) = 8\sigma_\text{full}\|v\|^2$ |
| `hessForm₄_neg_semidef_univ` | $\text{hessForm}(\kappa, w_\text{full}, v) \leq 0$ |
| `kurtObj₄_critPoint_neg` | $f(w_S) < 0$（负峰度情形） |
| `exercise_2_7_4` | 三条性质的合取（主定理） |

### 证明结构

```
exercise_2_7_4
├── hessForm₄_critPoint_univ         hessForm = 8σ‖v‖²
│   ├── kurtObj₄_critPoint           f(w_full) = σ_full
│   │   ├── sigma₄_mul_sum           σ · ∑(1/κ_j) = 1
│   │   └── sum_sigma₄_div_eq_one    ∑(σ/κ_i) = 1（辅助）
│   ├── coord_sq_mul_kappa           κ_i w_i² = σ（全支撑关键）
│   │   ├── Real.sq_sqrt             √(σ/κ_i)² = σ/κ_i
│   │   └── field_simp               κ_i · (σ/κ_i) = σ
│   ├── Finset.sum_congr             改写每项
│   ├── norm_sq_eq_sum₄              ‖v‖² = ∑ v_i²
│   └── ring                         整理 12σ‖v‖² - 4σ‖v‖² = 8σ‖v‖²
├── sigma₄_neg                       σ_full < 0
│   └── sum_inv_neg                  ∑(1/κ_j) < 0
└── hessForm₄_neg_semidef_univ       hessForm ≤ 0
    ├── hessForm₄_critPoint_univ     代入 = 8σ‖v‖²
    └── nlinarith                    σ < 0, ‖v‖² ≥ 0 → 8σ‖v‖² ≤ 0
```

### 技术关键点

#### 1. 全支撑的必要性

对一般的 $S \subsetneq \{1,\dots,d\}$，`hessForm = 8σ‖v‖²` 并不成立。对于 $i \notin S$，
$w_{S,i} = 0$，左侧该项贡献为 $0$，右侧 $8\sigma v_i^2$ 不一定为零。
因此定理 `hessForm₄_critPoint_univ` 仅对 `S = Finset.univ` 成立，通过 `[NeZero d]` 保证
`Finset.univ_nonempty`。

#### 2. 负号传递

关键不等式链：
```
κ_i < 0
  → 1/κ_i < 0  (div_neg_of_pos_of_neg)
  → ∑ 1/κ_j < 0  (Finset.sum_neg)
  → σ = 1/(∑ 1/κ_j) < 0  (div_neg_of_pos_of_neg)
  → σ/κ_i > 0  (div_pos_of_neg_of_neg)
  → √(σ/κ_i) 有意义  (Real.sqrt_nonneg)
```

#### 3. `coord_sq_mul_kappa` 的证明

```lean
κ_i * (√(σ/κ_i))² = κ_i * (σ/κ_i) = σ
```

用 `Real.sq_sqrt`（需要 `σ/κ_i ≥ 0`）和 `field_simp [ne_of_lt (hκ i hi)]` 完成。

#### 4. 与习题 2.7.3 的对比

| | 习题 2.7.3（$\exists \kappa_i > 0$） | 习题 2.7.4（$\forall \kappa_i < 0$） |
|-|------|------|
| 临界点 | $\pm e_j$（标准基向量） | $w_\text{full}$（稠密向量） |
| $w_i^2$ | $1$（仅第 $j$ 分量）或 $0$ | $\sigma/\kappa_i > 0$（所有分量） |
| Hessian 公式 | $-4\kappa_j\|v\|^2$（需 $v_j = 0$） | $8\sigma_\text{full}\|v\|^2$（无需切向量条件） |
| 条件 | $\kappa_j > 0$ | $\sigma_\text{full} < 0$ |
| 景观结论 | ICA 可行（稀疏恢复） | 优化公式无法直接使用 |

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `sum_inv_neg` | $\sum_{j \in S} 1/\kappa_j < 0$（各 $\kappa_j < 0$） | ✅ |
| `sigma₄_neg` | $\sigma_S < 0$ | ✅ |
| `sigma₄_div_pos` | $\sigma_S/\kappa_i > 0$ | ✅ |
| `sigma₄_mul_sum` | $\sigma_S \cdot \sum_j 1/\kappa_j = 1$ | ✅ |
| `sum_sigma₄_div_eq_one` | $\sum_{i \in S} \sigma_S/\kappa_i = 1$ | ✅ |
| `coord_sq_mul_kappa` | $\kappa_i \cdot w_{S,i}^2 = \sigma_S$ | ✅ |
| `kurtObj₄_critPoint` | $f(w_S) = \sigma_S$ | ✅ |
| `kurtObj₄_critPoint_neg` | $f(w_S) < 0$ | ✅ |
| `hessForm₄_critPoint_univ` | $\text{Hess} = 8\sigma_\text{full}\|v\|^2$ | ✅ |
| `hessForm₄_neg_semidef_univ` | $\text{Hess} \leq 0$ | ✅ |
| `exercise_2_7_4` | 主定理（三条性质合取） | ✅ |

## 验证

### 编译状态

```
lean_diagnostic_messages → success: true, items: []
```

✅ 零错误，零 sorry，零警告。

### 公理检查

```
propext, Classical.choice, Quot.sound
```

✅ 无自定义公理。

## 与书中的对应关系

| 书中陈述 | Lean 形式化 | 状态 |
|---------|------------|------|
| $\sigma_\text{full} < 0$（过度紧缩） | `sigma₄_neg` | ✅ |
| $\kappa_i \cdot w_{\text{full},i}^2 = \sigma_\text{full}$ | `coord_sq_mul_kappa` | ✅ |
| $\text{Hess}\,f(w_\text{full})[v,v] = 8\sigma_\text{full}\|v\|^2$ | `hessForm₄_critPoint_univ` | ✅ |
| $\sigma_\text{full} < 0 \Rightarrow w_\text{full}$ 是局部极大值 | `hessForm₄_neg_semidef_univ` | ✅ |

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.Analysis.InnerProductSpace.PiL2` | `EuclideanSpace`、`PiLp.inner_apply` |
| `Mathlib.Analysis.SpecialFunctions.Pow.Real` | 实数幂运算 |
| `Mathlib.Analysis.SpecialFunctions.Sqrt` | `Real.sqrt`、`Real.sq_sqrt` |

## 与练习 2.7 系列的联系

| 维度 | 2.7.1 | 2.7.2 | 2.7.3 | 2.7.4 |
|------|-------|-------|-------|-------|
| 主题 | 驻点方程 | 临界点构造 | 正峰度景观 | 负峰度景观 |
| 核心结果 | 一阶最优性条件 | $\|w_S\|=1$，满足驻点方程 | $e_j$（$\kappa_j>0$）局部极大 | $w_\text{full}$ 局部极大（$\forall\kappa_i<0$） |
| Hessian 公式 | — | — | $-4\kappa_j\|v\|^2$ | $8\sigma_\text{full}\|v\|^2$ |
| sorry 数 | 0 | 0 | 0 | **0** |

## 总结

**完成度**：100%（零 sorry）

习题 2.7.4 形式化了"过度紧缩"情形下球面峰度景观的核心计算：

1. **符号传递**：$\kappa_i < 0 \Rightarrow \sigma_\text{full} < 0 \Rightarrow \sigma_\text{full}/\kappa_i > 0$，保证临界点的平方根定义有意义。

2. **坐标平方恒等式**：$\kappa_i \cdot w_{\text{full},i}^2 = \sigma_\text{full}$（由 `Real.sq_sqrt` + `field_simp` 直接得到），这是全部推导的基础。

3. **Hessian 化简**：利用全支撑条件（$S = \text{univ}$），每项 $12\kappa_i w_i^2 v_i^2 = 12\sigma v_i^2$，从而整个求和等于 $12\sigma\|v\|^2$，再与 $-4\sigma\|v\|^2$ 合并得 $8\sigma\|v\|^2$。

4. **负半定性**：$\sigma < 0$ 与 $\|v\|^2 \geq 0$ 由 `nlinarith` 立即完成。

与习题 2.7.3 对比，本习题展示了"稠密"临界点的景观分析：当峰度全为负时，优化会被"全平均"方向所吸引，无法识别稀疏的独立成分，从而说明朴素的峰度最大化公式在此情形下失效。
