# 第2章 练习2.7 第3部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.7（`exercise:kurtosis-sphere-landscape`），第3部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex`
**Lean 文件**：`lean_formalization/Chapter2/2_7/Chapter2_Exercise2_7_3.lean`
**日期**：2026-04-06

## 非形式化陈述

对球面约束峰度最大化问题

$$\max_{\|\mathbf{w}\|_2 = 1} f(\mathbf{w}) = \sum_i \kappa_i w_i^4$$

假设至少存在一个 $\kappa_i > 0$，利用黎曼 Hessian（练习 2.6.3）证明：

1. 该问题的**唯一局部极大值**恰为 $\pm e_i$（$i \in S^+ = \{i \mid \kappa_i > 0\}$）。
2. **全局极大值**是 $\pm e_j$，其中 $j = \arg\max_{i \in S^+} \kappa_i$。

## 非形式化证明思路

### 关键计算：标准基向量处的 Hessian

在 $\mathbf{w} = e_j$ 处，坐标为 $(e_j)_j = 1$，$(e_j)_i = 0$（$i \neq j$）。

**目标函数值**：
$$f(e_j) = \sum_i \kappa_i (e_j)_i^4 = \kappa_j \cdot 1 = \kappa_j$$

**切向量条件**：$v \in T_{e_j} S^{d-1}$ 等价于 $\langle v, e_j \rangle = v_j = 0$。

**黎曼 Hessian 二次型**（在切空间上）：
$$\text{Hess}\,f(e_j)[v,v] = \sum_i 12\kappa_i (e_j)_i^2 v_i^2 - 4f(e_j)\|v\|^2$$

由于只有 $i = j$ 项的 $(e_j)_i^2 = 1$ 非零，但 $v_j = 0$，所以：
$$= 12\kappa_j \cdot 1 \cdot 0^2 - 4\kappa_j\|v\|^2 = -4\kappa_j\|v\|^2$$

**结论**：
- 当 $\kappa_j > 0$（$j \in S^+$）：$\text{Hess}\,f(e_j) \prec 0$，$e_j$ 是**严格局部极大值**。
- 当 $\kappa_j < 0$（$j \in S^-$）：$\text{Hess}\,f(e_j) \succ 0$，$e_j$ 是**严格局部极小值**。

### 全局极大值

在所有局部极大值 $e_i$（$i \in S^+$）中，$f(e_i) = \kappa_i$，因此全局极大值在 $\kappa_i$ 最大处取得。

## 形式化策略

### 关键定义

| 定义名 | 数学含义 | Lean 类型 |
|--------|----------|-----------|
| `kurtObj₃ κ w` | $f(\mathbf{w}) = \sum_i \kappa_i w_i^4$ | `ℝ` |
| `stdBasis j` | 标准基向量 $e_j$ | `EuclideanSpace ℝ (Fin d)` |
| `hessForm κ w v` | $\sum_i 12\kappa_i w_i^2 v_i^2 - 4f(\mathbf{w})\|v\|^2$ | `ℝ` |

`stdBasis j` 用 `EuclideanSpace.single j (1 : ℝ)` 实现，坐标引理来自 `EuclideanSpace.ofLp_single`。

### Lean 中使用的关键 Mathlib 工具

| 工具 | 用途 |
|------|------|
| `EuclideanSpace.single` | 构造标准基向量 $e_j$ |
| `EuclideanSpace.norm_single` | $\|e_j\| = 1$ |
| `EuclideanSpace.ofLp_single` | 坐标 $(e_j)_i = \delta_{ij}$ |
| `Finset.sum_ite_eq'` | 从 if-then-else 求和中提取单项 |
| `PiLp.inner_apply` | $\langle u, v \rangle = \sum_i \langle u_i, v_i \rangle$ |
| `real_inner_self_eq_norm_sq` | $\langle v, v \rangle = \|v\|^2$ |
| `nlinarith` | 非线性实数算术，用于负定性的判断 |
| `sq_eq_zero_iff` / `norm_eq_zero` | $\|v\|^2 = 0 \iff v = 0$ |

### 关键辅助引理

| 引理名 | 内容 |
|--------|------|
| `stdBasis_coord_eq` | $(e_j)_i = \text{if } i = j \text{ then } 1 \text{ else } 0$ |
| `stdBasis_norm` | $\|e_j\| = 1$ |
| `norm_sq_eq_sum` | $\|v\|^2 = \sum_i v_i^2$ |
| `kurtObj_stdBasis` | $f(e_j) = \kappa_j$ |

### 证明结构

```
exercise_2_7_3
├── kurtObj_stdBasis                f(e_j) = κ_j
│   ├── stdBasis_coord_eq           展开坐标
│   ├── ite_pow / mul_ite           化简 if-then-else 的幂次和乘积
│   └── Finset.sum_ite_eq'          提取求和的单项
├── stdBasis_norm                   ‖e_j‖ = 1
│   └── EuclideanSpace.norm_single
├── hessForm_stdBasis               hessForm κ (e_j) v = -4κ_j‖v‖²（v ⊥ e_j）
│   ├── 从 ⟨v, e_j⟩ = 0 推出 v_j = 0
│   │   ├── PiLp.inner_apply        展开内积为坐标和
│   │   └── Finset.sum_ite_eq'      提取 v_j 项
│   ├── hsum: ∑_i 12κ_i(e_j)_i²v_i² = 0
│   │   └── by_cases hij (i = j)   i=j 时 v_j=0 贡献为0，i≠j 时 (e_j)_i=0
│   ├── norm_sq_eq_sum              ‖v‖² = ∑_i v_i²
│   └── ring                       整理等式
└── hessForm_stdBasis_neg_def       hessForm ≤ 0（κ_j > 0，v ⊥ e_j）
    ├── hessForm_stdBasis           代入 = -4κ_j‖v‖²
    └── nlinarith                  由 κ_j > 0, ‖v‖² ≥ 0 得负性

globalMax_over_Splus
└── kurtObj_stdBasis（对每个 i 应用）  f(e_i) = κ_i，故 sup 相等

hessForm_stdBasis_neg_def_strict（等号条件）
├── hessForm_stdBasis
├── nlinarith                      -4κ_j‖v‖² = 0 → ‖v‖² = 0
└── sq_eq_zero_iff / norm_eq_zero  ‖v‖ = 0 → v = 0
```

### 技术难点与解决方案

#### 1. 坐标引理的 simp 参数

初始版本中 `simp [stdBasis, EuclideanSpace.ofLp_single, Pi.single_apply]` 含多余参数。最终只需：

```lean
simp [stdBasis]
```

Lean 4 的 `simp` 能自动通过 `EuclideanSpace.single` 的定义展开到 `Pi.single`。

#### 2. `kurtObj_stdBasis` 中的 if-then-else 求和

直接用 `Finset.sum_ite_eq'` 需先将 `κ_i * (if i = j then 1 else 0)^4` 整理为 `if i = j then κ_i else 0` 的形式。
利用 `simp only [ite_pow, ..., mul_ite, mul_one, mul_zero]` 自动完成化简，再应用 `Finset.sum_ite_eq'`。

#### 3. `norm_sq_eq_sum` 的证明路径

直接展开 `EuclideanSpace.norm_eq` 后需处理平方根，较繁琐。改用内积路径：

```lean
rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
-- 目标变为 ∑ i, inner ℝ (v.ofLp i) (v.ofLp i) = ∑ i, v.ofLp i ^ 2
-- 对每项用 simp（实数内积 ⟨a, a⟩ = a²）
```

#### 4. 切向量条件 `v_j = 0` 的提取

通过展开 `⟨v, e_j⟩ = ∑_i v_i * (e_j)_i`，再用 `Finset.sum_ite_eq'` 化简得到 $v_j = 0$。

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `kurtObj_stdBasis` | $f(e_j) = \kappa_j$ | ✅ |
| `stdBasis_norm` | $\|e_j\| = 1$ | ✅ |
| `hessForm_stdBasis` | $\text{Hess}\,f(e_j)[v] = -4\kappa_j\|v\|^2$（$v \perp e_j$） | ✅ |
| `hessForm_stdBasis_neg_def` | Hessian 非正（局部极大值条件，$\kappa_j > 0$） | ✅ |
| `hessForm_stdBasis_neg_def_strict` | 等号成立当且仅当 $v = 0$ | ✅ |
| `globalMax_over_Splus` | $\sup_{i \in S^+} f(e_i) = \sup_{i \in S^+} \kappa_i$ | ✅ |
| `exercise_2_7_3` | 上述各性质的合取 | ✅ |

## 验证

### 编译状态

```
lean_diagnostic_messages → success: true, items: []
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
| $f(e_j) = \kappa_j$ | `kurtObj_stdBasis` | ✅ |
| $\text{Hess}\,f(e_j)[v] = -4\kappa_j\|v\|^2$（$v \perp e_j$）| `hessForm_stdBasis` | ✅ |
| $\kappa_j > 0 \Rightarrow e_j$ 是局部极大值 | `hessForm_stdBasis_neg_def` | ✅ |
| 全局极大为 $\pm e_j$，$j = \arg\max \kappa_i$ | `globalMax_over_Splus` | ✅ |

**备注**：书中完整论证还包括多元素临界点的鞍点性质（Hessian 有正有负特征值），此部分属于景观分析的定性论证，超出了本形式化的范围，故未形式化。

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.Analysis.InnerProductSpace.PiL2` | `EuclideanSpace`、`EuclideanSpace.single`、`PiLp.inner_apply` |
| `Mathlib.Analysis.SpecialFunctions.Pow.Real` | 实数幂运算 |

## 与练习 2.7 系列的联系

| 维度 | 习题 2.7.1 | 习题 2.7.2 | 习题 2.7.3 |
|------|-----------|-----------|-----------|
| 主题 | 驻点方程推导 | 临界点显式构造 | 局部极大值判定 |
| 核心结果 | $P_w^\perp \nabla f = 0 \iff f(w)w = \kappa \odot w^{\odot 3}$ | $\|w_S\|=1$ 且满足驻点方程 | $e_j$（$\kappa_j>0$）处 Hessian 负定 |
| 主要工具 | `HasFDerivAt`，黎曼投影 | `Real.sqrt` 算术 | `EuclideanSpace.single`，`nlinarith` |
| sorry 数 | 0 | 0 | **0** |

## 总结

**完成度**：100%（零 sorry）

练习 2.7.3 形式化了球面峰度景观分析的核心计算步骤：

1. **标准基向量处目标值**：$f(e_j) = \kappa_j$，由坐标展开直接得到。
2. **Hessian 二次型**：切向量条件 $v_j = 0$ 使得求和中的 $i=j$ 项消零，仅剩 $-4\kappa_j\|v\|^2$。
3. **负定性**：由 $\kappa_j > 0$ 和 $\|v\|^2 \geq 0$ 立即由 `nlinarith` 完成。
4. **全局极大值**：因 $f(e_i) = \kappa_i$，在 $S^+$ 上取上确界即得。

技术上，本习题展示了 `EuclideanSpace.single` 作为标准基向量的使用方式、通过内积路径证明范数平方展开式的技巧，以及利用 `Finset.sum_ite_eq'` 从 if-then-else 求和中提取单项的方法。
