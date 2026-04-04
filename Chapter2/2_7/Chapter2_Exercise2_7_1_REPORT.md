# 第2章 练习2.7 第1部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.7（`exercise:kurtosis-sphere-landscape`），第1部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex:2404`
**Lean 文件**：`lean_formalization/Chapter2/2_7/Chapter2_Exercise2_7_1.lean`
**日期**：2026-04-04

## 非形式化陈述

考虑球面约束的种群峰度最大化问题：

$$\max_{\|\mathbf{w}\|_2^2 = 1}\; \sum_{i=1}^d \kappa_i w_i^4$$

其中 $\kappa_i = \mathrm{kurt}(z_i)$ 为各独立分量的峰度值。

**习题要求**：利用练习 2.6.1 的黎曼梯度公式，证明该问题的一阶最优性条件为：

$$\left(\sum_{i=1}^d \kappa_i w_i^4\right) \mathbf{w} = \boldsymbol{\kappa} \odot \mathbf{w}^{\odot 3}$$

其中 $\odot$ 表示逐元素乘法，$\mathbf{w}^{\odot 3}$ 表示逐元素三次方。

## 非形式化证明思路

设 $f(\mathbf{w}) = \sum_i \kappa_i w_i^4$，则其欧氏梯度为 $\nabla f(\mathbf{w})_i = 4\kappa_i w_i^3$，即

$$\nabla f(\mathbf{w}) = 4(\boldsymbol{\kappa} \odot \mathbf{w}^{\odot 3}).$$

由练习 2.6.1，球面约束问题的黎曼梯度为：

$$\mathrm{grad}\, f(\mathbf{w}) = P_\mathbf{w}^\perp \nabla f(\mathbf{w}) = \nabla f(\mathbf{w}) - \langle \nabla f(\mathbf{w}),\, \mathbf{w}\rangle \mathbf{w}.$$

计算内积：

$$\langle \nabla f(\mathbf{w}),\, \mathbf{w}\rangle = 4\sum_i \kappa_i w_i^3 \cdot w_i = 4\sum_i \kappa_i w_i^4 = 4f(\mathbf{w}).$$

因此驻点条件 $\mathrm{grad}\, f(\mathbf{w}) = 0$ 等价于：

$$4(\boldsymbol{\kappa} \odot \mathbf{w}^{\odot 3}) - 4f(\mathbf{w})\mathbf{w} = 0
\quad\Longleftrightarrow\quad
f(\mathbf{w})\mathbf{w} = \boldsymbol{\kappa} \odot \mathbf{w}^{\odot 3}.$$

## 形式化策略

### 关键定义

| 定义名 | 数学含义 | Lean 类型 |
|--------|----------|-----------|
| `kurtObj κ w` | $f(\mathbf{w}) = \sum_i \kappa_i w_i^4$ | `ℝ` |
| `elemCube κ w` | $\boldsymbol{\kappa} \odot \mathbf{w}^{\odot 3}$，即 $(\kappa_i w_i^3)_i$ | `EuclideanSpace ℝ (Fin d)` |
| `kurtGrad κ w` | $\nabla f(\mathbf{w}) = 4 \cdot \mathrm{elemCube}\ \kappa\ \mathbf{w}$ | `EuclideanSpace ℝ (Fin d)` |
| `coordLinear i` | 第 $i$ 坐标线性映射 $v \mapsto v_i$ | `EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ` |

### Lean 中使用的关键 Mathlib 工具

| 工具 | 用途 |
|------|------|
| `PiLp.inner_apply` | 展开 `EuclideanSpace` 的内积为坐标级求和 |
| `HasFDerivAt.pow` | 函数 $t \mapsto t^n$ 的 Fréchet 导数 |
| `HasFDerivAt.const_mul` | 与常数相乘的导数规则 |
| `HasFDerivAt.sum` | 有限求和的导数规则 |
| `Submodule.starProjection_orthogonal_val` | 投影的显式公式 $P^\perp v = v - Pv$ |
| `smul_eq_zero` | 数量积为零的等价刻画 |
| `sub_eq_zero` | $a - b = 0 \iff a = b$ |
| `PiLp.smul_apply` | 坐标级数量乘 |

### EuclideanSpace 坐标计算技术

本文件中处理 `EuclideanSpace ℝ (Fin d)` 的关键技巧：

1. **坐标访问**：`w.ofLp i` 给出第 $i$ 个坐标值
2. **内积展开**：`PiLp.inner_apply` 将内积化为 $\sum_i \langle u_i, v_i \rangle$，再用 `inner_ℝ` 化 ℝ 上的内积为乘法
3. **构造元素**：`(EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => ...)` 构造坐标已知的向量，其 `ofLp i` 直接为 `rfl`
4. **smul 坐标**：`(c • w).ofLp i = c * w.ofLp i`，需 `PiLp.smul_apply` + `simp`
5. **PiLp.continuousLinearEquiv 的 `change`**：在 `HasFDerivAt.sum` 展开后，坐标映射以 `↑(PiLp.continuousLinearEquiv 2 ℝ fun x => ℝ) v i` 形式出现，与 `v.ofLp i` 定义等价（`rfl`），但需显式 `change` 才能让 `ring` 生效

### 梯度公式的证明方法

`hasFDerivAt_kurtObj` 是技术上最难的引理，证明路线：

1. **逐坐标求导**：对每个 $i$，函数 $\mathbf{w} \mapsto \kappa_i w_i^4$ 的 Fréchet 导数是 `κᵢ • (4 wᵢ³) • coordLinear i`，由 `HasFDerivAt.pow(n=4)` + `HasFDerivAt.const_mul` 给出
2. **求和**：用 `HasFDerivAt.sum (u := Finset.univ)` 合并各分量的导数（注意需要显式写 `Finset.univ` 才能与 `∑ i : Fin d` 的 unification 成功）
3. **内积形式转换**：将 `∑ i, κᵢ • (4wᵢ³) • coordLinear i` 改写为 `innerSL ℝ (kurtGrad κ w)` ——逐点展开内积并用 `ring` 验证

### 主定理的证明结构

`exercise_2_7_1` 的 iff 证明：

```
P_w^⊥(kurtGrad κ w) = 0
  ↕ [proj_perp_explicit]
kurtGrad κ w - ⟨w, kurtGrad κ w⟩ · w = 0
  ↕ [inner_kurtGrad_self: ⟨kurtGrad, w⟩ = 4·kurtObj]
4·elemCube κ w - 4·kurtObj κ w · w = 0
  ↕ [提取公因子 4]
4 • (elemCube κ w - kurtObj κ w • w) = 0
  ↕ [smul_eq_zero + 4≠0]
elemCube κ w - kurtObj κ w • w = 0
  ↕ [sub_eq_zero]
kurtObj κ w • w = elemCube κ w  ✓
```

### 文件结构

```
Chapter2_Exercise2_7_1.lean
├── inner_ℝ (私有辅助)               -- ℝ 上内积 = 乘法
├── coordLinear                       -- 坐标线性映射
├── kurtObj                           -- 目标函数定义
├── elemCube                          -- κ ⊙ w⊙³ 向量定义
├── kurtGrad                          -- 欧氏梯度定义
├── inner_kurtGrad_self               -- ⟨∇f(w), w⟩ = 4f(w)
├── hasFDerivAt_kurtObj               -- 梯度公式（HasFDerivAt）
├── proj_perp_explicit (私有辅助)     -- P_w^⊥ 显式公式（来自 2.6.1）
└── exercise_2_7_1                    -- 主定理：驻点条件等价性
```

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `inner_kurtGrad_self` | $\langle \nabla f(\mathbf{w}), \mathbf{w}\rangle = 4f(\mathbf{w})$ | ✅ |
| `hasFDerivAt_kurtObj` | `D(kurtObj κ)(w) = innerSL ℝ (kurtGrad κ w)` | ✅ |
| `exercise_2_7_1` | $P_w^\perp \nabla f = 0 \iff f(w)\cdot w = \boldsymbol{\kappa}\odot\mathbf{w}^{\odot 3}$ | ✅ |

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
| $f(\mathbf{w}) = \sum_i \kappa_i w_i^4$ | `kurtObj κ w` | ✅ |
| $\nabla f(\mathbf{w}) = 4(\kappa_i w_i^3)_i$ | `hasFDerivAt_kurtObj` | ✅ |
| 驻点条件等价性 | `exercise_2_7_1` | ✅ |

## 与相关练习的对比

| 维度 | 习题 2.7.1（驻点条件） | 习题 2.6.1（切空间） | 习题 2.6.3（黎曼 Hessian） |
|------|------------------------|----------------------|---------------------------|
| 数学领域 | 微分几何 + 微积分 | 微分几何 | 微分几何 |
| sorry 数 | 0 | 0 | 0 |
| 核心技术 | `HasFDerivAt.sum` + 坐标计算 | `starProjection` API | `starProjection` + 对称性 |
| 主定理数 | 1（iff 形式） | 7 | 4 |
| Lean 难点 | `HasFDerivAt.sum` 的 unification；`PiLp.continuousLinearEquiv` 的 `change` | `starRingEnd ℝ` 化简 | 投影自伴性的组合使用 |

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.Analysis.InnerProductSpace.PiL2` | `EuclideanSpace` 的内积与坐标结构 |
| `Mathlib.Analysis.InnerProductSpace.Projection.Basic` | `starProjection`，正交投影公式 |
| `Mathlib.Analysis.Calculus.FDeriv.Pow` | `HasFDerivAt.pow`，幂函数导数 |

## 总结

**完成度**：100%（零 sorry）

练习 2.7.1（球面约束峰度最大化的一阶驻点条件）完全形式化完成。

本习题是 FastICA 景观分析的起点，严格证明了：

1. **梯度公式**：在 `EuclideanSpace ℝ (Fin d)` 中，目标函数 $\sum_i \kappa_i w_i^4$ 的 Fréchet 导数可以表示为 $\mathrm{innerSL}$ 作用在梯度向量上（`hasFDerivAt_kurtObj`）。
2. **驻点等价**：利用 2.6.1 的黎曼梯度公式，一阶驻点条件等价于方程 $f(\mathbf{w})\mathbf{w} = \boldsymbol{\kappa}\odot\mathbf{w}^{\odot 3}$，后者正是书中关于球面峰度极值点结构的出发点（`exercise_2_7_1`）。

技术上，关键挑战在于在有限维欧氏空间中正确使用 `HasFDerivAt.sum`，以及处理 `PiLp.continuousLinearEquiv` 的语法表示与 `v.ofLp i` 之间的定义等价性。
