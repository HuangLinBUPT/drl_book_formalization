# 第2章 练习2.7 第2部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.7（`exercise:kurtosis-sphere-landscape`），第2部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex`
**Lean 文件**：`lean_formalization/Chapter2/2_7/Chapter2_Exercise2_7_2.lean`
**日期**：2026-04-05

## 非形式化陈述

对球面约束峰度最大化问题 $\max_{\|\mathbf{w}\|_2 = 1}\sum_i \kappa_i w_i^4$ 的正号临界点进行显式构造与验证。

给定非空子集 $S \subseteq \{1,\ldots,d\}$，且对所有 $i \in S$ 有 $\kappa_i > 0$，定义：

$$\sigma_S = \frac{1}{\displaystyle\sum_{j \in S} \frac{1}{\kappa_j}}, \qquad
w_S(i) = \begin{cases} \sqrt{\sigma_S/\kappa_i} & i \in S \\ 0 & i \notin S \end{cases}$$

**习题要求**：证明

1. $\|\mathbf{w}_S\|_2 = 1$（$\mathbf{w}_S$ 在单位球面上）
2. $f(\mathbf{w}_S)\cdot \mathbf{w}_S = \boldsymbol{\kappa} \odot \mathbf{w}_S^{\odot 3}$（满足练习 2.7.1 的驻点方程）

## 非形式化证明思路

### 第1部分：单位范数

$$\|\mathbf{w}_S\|^2 = \sum_{i \in S} w_S(i)^2 = \sum_{i \in S} \frac{\sigma_S}{\kappa_i} = \sigma_S \sum_{i \in S} \frac{1}{\kappa_i} = 1$$

最后一步用到 $\sigma_S$ 的定义：$\sigma_S \cdot \sum_{j \in S} \frac{1}{\kappa_j} = 1$。

### 第2部分：驻点方程

先计算目标函数值：

$$f(\mathbf{w}_S) = \sum_{i \in S} \kappa_i w_S(i)^4 = \sum_{i \in S} \kappa_i \left(\frac{\sigma_S}{\kappa_i}\right)^2 = \sum_{i \in S} \frac{\sigma_S^2}{\kappa_i} = \sigma_S^2 \sum_{i \in S} \frac{1}{\kappa_i} = \sigma_S$$

然后逐坐标验证驻点方程（对 $i \in S$）：

$$f(\mathbf{w}_S) \cdot w_S(i) = \sigma_S \sqrt{\frac{\sigma_S}{\kappa_i}}, \qquad \kappa_i w_S(i)^3 = \kappa_i \left(\sqrt{\frac{\sigma_S}{\kappa_i}}\right)^3 = \kappa_i \cdot \sqrt{\frac{\sigma_S}{\kappa_i}} \cdot \frac{\sigma_S}{\kappa_i} = \sigma_S\sqrt{\frac{\sigma_S}{\kappa_i}}$$

两者相等。对 $i \notin S$ 两边均为 $0$。

## 形式化策略

### 关键定义

| 定义名 | 数学含义 | Lean 类型 |
|--------|----------|-----------|
| `sigma_S κ S` | $\sigma_S = 1/(\sum_{j \in S} 1/\kappa_j)$ | `ℝ` |
| `critPoint κ S` | 临界点 $\mathbf{w}_S$ | `EuclideanSpace ℝ (Fin d)` |
| `kurtObj' κ w` | $f(\mathbf{w}) = \sum_i \kappa_i w_i^4$ | `ℝ` |
| `elemCube' κ w` | $\boldsymbol{\kappa} \odot \mathbf{w}^{\odot 3}$，即 $(\kappa_i w_i^3)_i$ | `EuclideanSpace ℝ (Fin d)` |

### Lean 中使用的关键 Mathlib 工具

| 工具 | 用途 |
|------|------|
| `Finset.sum_add_sum_compl` | 将全集上的求和拆分为 $S$ 内和 $S^c$ 内两部分 |
| `Finset.sum_pos` | 正项有限和的正性 |
| `Finset.mul_sum` | 提取求和中的公因子 |
| `Real.sq_sqrt` | $(\sqrt{x})^2 = x$（$x \geq 0$） |
| `Real.norm_of_nonneg` | $\|\sqrt{x}\| = \sqrt{x}$（$\sqrt{x} \geq 0$） |
| `PiLp.smul_apply` | `(c • v).ofLp i = c • v.ofLp i` |
| `nlinarith` | 非线性实数算术，用于最终的等式验证 |

### 关键辅助引理

| 引理名 | 内容 |
|--------|------|
| `sum_inv_pos` | $\sum_{j \in S} 1/\kappa_j > 0$（由 $\kappa_j > 0$ 和 $S \neq \emptyset$）|
| `sigma_pos` | $\sigma_S > 0$ |
| `sigma_div_pos` | $\sigma_S/\kappa_i > 0$（对 $i \in S$）|
| `sigma_mul_sum` | $\sigma_S \cdot \sum_{j \in S} 1/\kappa_j = 1$（核心恒等式）|
| `sum_sigma_div_eq_one` | $\sum_{i \in S} \sigma_S/\kappa_i = 1$ |
| `kurtObj_critPoint` | $f(\mathbf{w}_S) = \sigma_S$ |

### 证明结构

```
exercise_2_7_2
├── critPoint_norm               ‖w_S‖ = 1
│   ├── EuclideanSpace.norm_eq   展开范数为坐标平方和
│   ├── Finset.sum_add_sum_compl 拆分 S 与 Sᶜ
│   ├── Real.sq_sqrt             ‖√(σ/κᵢ)‖² = σ/κᵢ
│   └── sum_sigma_div_eq_one     ∑ σ/κᵢ = 1
└── exercise_2_7_2_stationarity  f(w_S)·w_S = κ ⊙ w_S^⊙3
    ├── kurtObj_critPoint         f(w_S) = σ
    │   ├── Finset.sum_add_sum_compl
    │   ├── Real.sq_sqrt (×2)    √(σ/κᵢ)⁴ = (σ/κᵢ)²
    │   └── sigma_mul_sum        σ² · Σ 1/κᵢ = σ
    └── 逐坐标 (by_cases hi : i ∈ S)
        ├── i ∈ S: nlinarith + hκᵢr : κᵢ·(σ/κᵢ) = σ
        └── i ∉ S: simp（两边均为 0）
```

### 技术难点与解决方案

#### 1. Section 变量的陷阱

初始版本将 `hκ` 和 `hSne` 放在 `section helpers` 的 `variable` 中，但由于它们未出现在辅助引理的**类型**中（只在证明体中使用），Lean 4 不会自动将其纳入参数列表，导致 `Unknown identifier 'hκ'` 错误。

**解决方案**：将所有辅助引理改为独立的私有引理，显式声明 `hκ` 和 `hSne` 参数：

```lean
private lemma sum_inv_pos (κ : ...) (S : ...) (hκ : ∀ i ∈ S, 0 < κ.ofLp i)
    (hSne : S.Nonempty) : 0 < ∑ j ∈ S, 1 / κ.ofLp j := ...
```

#### 2. 求和拆分

`Finset.disjoint_compl_right`（初始代码使用）在 Mathlib 中不存在。正确做法是使用 `Finset.sum_add_sum_compl`：

```lean
rw [← Finset.sum_add_sum_compl S f]
-- 将 ∑ i : Fin d, f i 改写为 ∑ i ∈ S, f i + ∑ i ∈ Sᶜ, f i
```

#### 3. `∑ σ/κᵢ` 的因式分解

`← Finset.mul_sum` 需要匹配 `∑ a * f i` 模式，而 `σ/κᵢ` 不直接匹配。解决方法：先手动改写为乘法形式再提取公因子：

```lean
have : ∀ i ∈ S, sigma_S κ S / κ.ofLp i = sigma_S κ S * (1 / κ.ofLp i) :=
  fun _ _ => by ring
rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
```

#### 4. 驻点方程的算术步骤

最终等式 $\sigma \cdot \sqrt{r} = \kappa_i \cdot (\sqrt{r} \cdot r)$ 的验证：
- 先建立 `cube : √r^3 = √r * r`（通过 `pow_succ` + `mul_comm` + `Real.sq_sqrt`）
- 再建立 `hκr : κᵢ * r = σ`（通过 `field_simp [ne_of_gt (hκ i hi)]`）
- 最后用 `nlinarith [Real.sqrt_nonneg r]` 结合两者完成证明

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `critPoint_norm` | $\|\mathbf{w}_S\|_2 = 1$ | ✅ |
| `kurtObj_critPoint` | $f(\mathbf{w}_S) = \sigma_S$ | ✅ |
| `exercise_2_7_2_stationarity` | $f(\mathbf{w}_S)\mathbf{w}_S = \boldsymbol{\kappa}\odot\mathbf{w}_S^{\odot 3}$ | ✅ |
| `exercise_2_7_2` | 上述两者的合取 | ✅ |

## 验证

### 编译状态

```
lean_diagnostic_messages → success: true, items: []
lake build → Build completed successfully
```

✅ 零错误，零 sorry，零警告。

### 公理检查

仅使用标准 Lean 4 / Mathlib 公理：
```
propext, Classical.choice, Quot.sound
```
✅ 无自定义公理。

## 与书中的对应关系

| 书中陈述 | Lean 形式化 | 状态 |
|---------|------------|------|
| $\sigma_S = 1/(\sum_{j \in S} 1/\kappa_j)$ | `sigma_S κ S` | ✅ |
| $\mathbf{w}_S(i) = \sqrt{\sigma_S/\kappa_i}$（$i \in S$）；$0$（$i \notin S$）| `critPoint κ S` | ✅ |
| $\|\mathbf{w}_S\|_2 = 1$ | `critPoint_norm` | ✅ |
| $f(\mathbf{w}_S)\mathbf{w}_S = \boldsymbol{\kappa}\odot\mathbf{w}_S^{\odot 3}$ | `exercise_2_7_2_stationarity` | ✅ |

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.Analysis.InnerProductSpace.PiL2` | `EuclideanSpace` 的坐标结构与范数 |
| `Mathlib.Analysis.SpecialFunctions.Sqrt` | `Real.sqrt`，`Real.sq_sqrt` |
| `Mathlib.Analysis.SpecialFunctions.Pow.Real` | 实数幂运算 |

## 与练习 2.7.1 的联系

本习题（2.7.2）是 2.7.1 的直接续篇：

| 维度 | 习题 2.7.1 | 习题 2.7.2 |
|------|-----------|-----------|
| 主题 | 驻点方程的推导 | 临界点的显式构造与验证 |
| 核心结果 | $P_w^\perp \nabla f = 0 \iff f(w)w = \kappa \odot w^{\odot 3}$ | $w_S$ 满足驻点方程且 $\|w_S\|=1$ |
| 主要工具 | `HasFDerivAt`，黎曼投影 | `Real.sqrt` 算术，`Finset.sum_add_sum_compl` |
| sorry 数 | 0 | 0 |

## 总结

**完成度**：100%（零 sorry）

练习 2.7.2 完全形式化了球面峰度目标的正号临界点 $\mathbf{w}_S$ 的两个关键性质：

1. **单位范数**：$\|\mathbf{w}_S\|_2 = 1$，由 $\sigma_S$ 的定义恒等式 $\sigma_S \cdot \sum_{j \in S} 1/\kappa_j = 1$ 直接推出。
2. **驻点方程**：$f(\mathbf{w}_S)\mathbf{w}_S = \boldsymbol{\kappa} \odot \mathbf{w}_S^{\odot 3}$，通过先计算 $f(\mathbf{w}_S) = \sigma_S$，再逐坐标利用 $\kappa_i \cdot (\sigma_S/\kappa_i) = \sigma_S$ 验证。

技术上，本习题展示了在 Lean 4 section 中 variable 的作用域规则（变量须出现在声明类型中才被自动包含）、`Finset.sum_add_sum_compl` 的正确用法，以及结合 `nlinarith` 处理包含 `Real.sqrt` 的非线性等式的技巧。
