# 第2章 练习2.8 第1部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.8（`exercise:orthogonal-group-calculus`），第1部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex`
**Lean 文件**：`lean_formalization/Chapter2/2_8/Chapter2_Exercise2_8_1.lean`
**日期**：2026-04-06

## 非形式化陈述

对正交群

$$O(d) = \{\,Q \in \mathbb{R}^{d\times d} \mid Q^\top Q = I\,\}$$

以矩阵内积 $\langle X, Y \rangle = \operatorname{tr}(X^\top Y)$（Frobenius 内积）为度量。

**第1a部分**：正交群在 $Q$ 处的切空间为

$$T_Q O(d) = \{\,Q\Omega \in \mathbb{R}^{d\times d} \mid \Omega^\top = -\Omega\,\}$$

即 $Q$ 乘以一个斜对称矩阵所张成的集合。

**第1b部分**：到该切空间的正交投影为

$$\mathcal{P}_{T_Q O(d)}(\Delta) = Q \cdot \operatorname{Skew}(Q^\top \Delta)$$

其中 $\operatorname{Skew}(\Delta) = \tfrac{1}{2}(\Delta - \Delta^\top)$ 提取矩阵的斜对称部分。

## 非形式化证明思路

### 切空间的刻画

设 $F(Q) = Q^\top Q$，则 $O(d) = F^{-1}(I)$。对 $F$ 在 $Q$ 处的 Fréchet 微分作用于方向 $V$：

$$DF_Q[V] = V^\top Q + Q^\top V$$

切空间 $T_Q O(d) = \ker(DF_Q)$，即满足 $Q^\top V + V^\top Q = 0$ 的矩阵 $V$，等价于 $Q^\top V$ 是斜对称矩阵。令 $\Omega = Q^\top V$，则 $V = Q\Omega$（当 $Q \in O(d)$ 时，由 $QQ^\top = I$ 还原）。

### 投影公式的正确性

需证明 $P(\Delta) = Q \cdot \operatorname{Skew}(Q^\top \Delta)$ 是到 $T_Q O(d)$ 的正交投影，即：

1. **像在切空间内**：$Q^\top P(\Delta) = \operatorname{Skew}(Q^\top\Delta)$ 是斜对称的。
2. **幂等性**：若 $V \in T_Q O(d)$，则 $P(V) = V$。
   - 此时 $Q^\top V$ 已是斜对称的，故 $\operatorname{Skew}(Q^\top V) = Q^\top V$，再由 $QQ^\top = I$ 还原。
3. **正交补性**：对任意切向量 $Q\Omega$（$\Omega^\top = -\Omega$），
   $$\langle Q\Omega,\, \Delta - P(\Delta)\rangle = \operatorname{tr}(\Omega^\top Q^\top (\Delta - Q\operatorname{Skew}(Q^\top\Delta)))$$
   利用 $Q^\top Q = I$ 化简后得 $\operatorname{tr}(\Omega^\top(\Delta' - \operatorname{Skew}(\Delta')))$（$\Delta' = Q^\top\Delta$），而 $\Delta' - \operatorname{Skew}(\Delta') = \tfrac{1}{2}(\Delta' + \Delta'^\top)$ 是对称的，斜对称矩阵与对称矩阵之积的迹为零。

### 斜对称×对称迹为零

设 $\Omega^\top = -\Omega$，$S^\top = S$，则：

$$\operatorname{tr}(\Omega S) = \operatorname{tr}((\Omega S)^\top) = \operatorname{tr}(S^\top \Omega^\top) = \operatorname{tr}(S(-\Omega)) = -\operatorname{tr}(S\Omega) = -\operatorname{tr}(\Omega S)$$

故 $\operatorname{tr}(\Omega S) = 0$。

## 形式化策略

### 关键定义

| 定义名 | 数学含义 | Lean 类型 |
|--------|----------|-----------|
| `matInner d X Y` | $\langle X, Y\rangle = \operatorname{tr}(X^\top Y)$ | `ℝ` |
| `skewPart d Δ` | $\operatorname{Skew}(\Delta) = \tfrac{1}{2}(\Delta - \Delta^\top)$ | `Mat` |
| `inTangentSpace d Q V` | $(Q^\top V)^\top = -(Q^\top V)$（切空间成员条件） | `Prop` |
| `tangentProj d Q Δ` | $P(\Delta) = Q \cdot \operatorname{Skew}(Q^\top \Delta)$ | `Mat` |

其中 `Mat` 是 `Matrix (Fin d) (Fin d) ℝ` 的本地缩写。

### 关键辅助引理

| 引理名 | 内容 |
|--------|------|
| `skewPart_transpose` | $\operatorname{Skew}(\Delta)^\top = -\operatorname{Skew}(\Delta)$ |
| `skewPart_of_skew` | $\Delta^\top = -\Delta \Rightarrow \operatorname{Skew}(\Delta) = \Delta$ |
| `symmPart_eq` | $\Delta - \operatorname{Skew}(\Delta) = \tfrac{1}{2}(\Delta + \Delta^\top)$ |
| `tangent_reconstruction` | $Q \in O(d) \Rightarrow V = Q \cdot (Q^\top V)$ |
| `trace_skew_mul_symm` | $\Omega^\top=-\Omega,\, S^\top=S \Rightarrow \operatorname{tr}(\Omega S) = 0$ |

### 主要定理

| 定理名 | 数学内容 |
|--------|----------|
| `tangentProj_in_tangentSpace` | $P(\Delta) \in T_Q O(d)$（需 $Q \in O(d)$） |
| `tangentProj_idempotent` | $V \in T_Q O(d) \Rightarrow P(V) = V$ |
| `tangentProj_complement_orthogonal` | $\langle Q\Omega,\, \Delta - P(\Delta)\rangle = 0$（$\Omega^\top=-\Omega$） |
| `exercise_2_8_1` | 主定理（四条性质的合取） |

### 证明结构

```
exercise_2_8_1
├── rfl                                  P(Δ) = Q · Skew(QᵀΔ)（定义）
├── tangentProj_in_tangentSpace          P(Δ) ∈ T_Q O(d)
│   ├── skewPart_transpose               Skew(·)ᵀ = -Skew(·)
│   └── QᵀQ = I                         (mem_orthogonalGroup_iff')
├── tangentProj_idempotent               P(P(Δ)) = P(Δ)
│   ├── skewPart_of_skew                 QᵀP(Δ) 已斜对称 → Skew = id
│   └── tangent_reconstruction           Q(QᵀV) = V（由QQᵀ=I）
└── tangentProj_complement_orthogonal    ⟪QΩ, Δ-P(Δ)⟫ = 0
    ├── expand                           展开为 tr(ΩᵀM) - tr(ΩᵀSkew(M))
    │   └── QᵀQ = I                      消去中间的 QᵀQ
    ├── symmPart_eq                      M - Skew(M) = ½(M + Mᵀ)
    └── trace_skew_mul_symm              tr(斜对称 × 对称) = 0
        ├── trace_transpose              tr(AB) = tr((AB)ᵀ)
        ├── transpose_mul + hS + hΩ     展开转置
        └── trace_mul_comm              tr(AB) = tr(BA)
```

### 技术关键点

#### 1. 矩阵结合律的手动管理

Lean 对非方阵不能直接用 `mul_assoc`，需要显式写出 `Matrix.mul_assoc A B C`。本文件中多处需要在 `show` 块内手动重排结合方式，例如：

```lean
rw [show (skewPart d (Qᵀ * Δ))ᵀ * Qᵀ * Q =
    (skewPart d (Qᵀ * Δ))ᵀ * (Qᵀ * Q) from Matrix.mul_assoc _ _ _]
```

#### 2. `tangentProj_in_tangentSpace` 的证明障碍

直接展开 `inTangentSpace d Q (tangentProj d Q Δ)` 后，目标变为：

```
(skewPart d (Qᵀ * Δ))ᵀ * Qᵀ * Q = -(Qᵀ * (Q * skewPart d (Qᵀ * Δ)))
```

两侧都需要利用 $Q^\top Q = I$ 化简，且负号的位置需要分别处理（左侧用 `Matrix.mul_assoc` + `hQtQ`，右侧用 `simp [Matrix.mul_assoc]` + `neg` 化简）。

#### 3. `trace_skew_mul_symm` 的证明路线

直接计算 $\operatorname{tr}(\Omega S) = -\operatorname{tr}(\Omega S)$，再用 `linarith` 推出为零。关键步骤：

```
tr(ΩS)
  = tr((ΩS)ᵀ)     [trace_transpose]
  = tr(SᵀΩᵀ)      [transpose_mul]
  = tr(S · (-Ω))   [hS, hΩ]
  = -tr(SΩ)        [Matrix.mul_neg + trace_neg]
  = -tr(ΩS)        [trace_mul_comm]
```

#### 4. 正交补性证明中的分拆策略

将 $\langle Q\Omega, \Delta - P(\Delta)\rangle$ 的计算分为四步：

- **展开**：利用 $Q^\top Q = I$ 将二次型化为 $\operatorname{tr}(\Omega^\top M) - \operatorname{tr}(\Omega^\top \operatorname{Skew}(M))$
- **合并**：写成 $\operatorname{tr}(\Omega^\top(M - \operatorname{Skew}(M)))$
- **识别**：$M - \operatorname{Skew}(M) = \tfrac{1}{2}(M + M^\top)$ 是对称的（`symmPart_eq`）
- **消去**：$\Omega^\top$ 是斜对称的（因 $\Omega^\top = -\Omega$ 故 $(\Omega^\top)^\top = \Omega = -\Omega^\top$），由 `trace_skew_mul_symm` 得零

#### 5. 与练习 2.6.1 的平行结构

| | 球面 S^{d-1}（练习2.6.1） | 正交群 O(d)（练习2.8.1） |
|-|--------------------------|--------------------------|
| 约束 | $\|u\|^2 = 1$ | $Q^\top Q = I$ |
| 切空间 | $\{v \mid \langle v, u\rangle = 0\} = (ℝ\cdot u)^\perp$ | $\{Q\Omega \mid \Omega^\top = -\Omega\}$ |
| 投影 | $P_u^\perp(v) = v - \langle u,v\rangle u$ | $P(Δ) = Q\operatorname{Skew}(Q^\top\Delta)$ |
| 关键引理 | `sphere_tangent_projection_explicit` | `tangentProj_in_tangentSpace` |
| 正交性来源 | $\langle u, P_u^\perp v\rangle = 0$ | $\operatorname{tr}(\text{斜对称}\times\text{对称}) = 0$ |
| Mathlib 工具 | `Submodule.starProjection` | `Matrix.trace`、手动推导 |

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `matInner_comm` | $\langle X, Y\rangle = \langle Y, X\rangle$ | ✅ |
| `skewPart_transpose` | $\operatorname{Skew}(\Delta)^\top = -\operatorname{Skew}(\Delta)$ | ✅ |
| `skewPart_of_skew` | $\Delta^\top=-\Delta \Rightarrow \operatorname{Skew}(\Delta)=\Delta$ | ✅ |
| `symmPart_eq` | $\Delta - \operatorname{Skew}(\Delta) = \tfrac{1}{2}(\Delta+\Delta^\top)$ | ✅ |
| `tangent_reconstruction` | $V = Q(Q^\top V)$（$Q \in O(d)$） | ✅ |
| `tangentProj_in_tangentSpace` | $P(\Delta) \in T_Q O(d)$ | ✅ |
| `tangentProj_idempotent` | $V\in T_Q O(d) \Rightarrow P(V)=V$ | ✅ |
| `trace_skew_mul_symm` | $\operatorname{tr}(\Omega S)=0$（斜对称×对称） | ✅ |
| `tangentProj_complement_orthogonal` | $\langle Q\Omega,\Delta-P(\Delta)\rangle=0$ | ✅ |
| `exercise_2_8_1` | 主定理（四条性质合取） | ✅ |

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
| $T_Q O(d) = \{Q\Omega \mid \Omega^\top=-\Omega\}$ | `inTangentSpace` + `tangentSpace_from_skew` 思路 | ✅ |
| $\mathcal{P}_{T_Q O(d)}(\Delta) = Q\operatorname{Skew}(Q^\top\Delta)$ | `tangentProj` | ✅ |
| 投影像在切空间内 | `tangentProj_in_tangentSpace` | ✅ |
| 投影的幂等性 | `tangentProj_idempotent` | ✅ |
| 残差与切空间正交 | `tangentProj_complement_orthogonal` | ✅ |

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.LinearAlgebra.Matrix.Trace` | `Matrix.trace`、`trace_mul_comm`、`trace_transpose`、`trace_neg` |
| `Mathlib.LinearAlgebra.UnitaryGroup` | `Matrix.orthogonalGroup`、`mem_orthogonalGroup_iff` |
| `Mathlib.Data.Real.Basic` | 实数域 `ℝ` |
| `Mathlib.Data.Matrix.Basic` | `Matrix.mul_assoc`、`transpose_mul`、`Matrix.mul_neg` |

## 与练习 2.8 系列的联系

| 维度 | 2.8.1（本文件） | 2.8.2（待形式化） | 2.8.3（待形式化） |
|------|----------------|------------------|------------------|
| 主题 | 切空间与投影 | 黎曼 Hessian | O(d) 上的最近点投影 |
| 核心结果 | $P(\Delta)=Q\operatorname{Skew}(Q^\top\Delta)$ | Hess $f$ 的显式公式 | $\operatorname{proj}_{O(d)}(X) = UV^\top$（SVD） |
| sorry 数 | **0** | — | — |

## 总结

**完成度**：100%（零 sorry）

习题 2.8.1 完成了正交群黎曼几何的基础构件：

1. **切空间刻画**：$T_Q O(d) = \{Q\Omega \mid \Omega^\top=-\Omega\}$，通过 `inTangentSpace` 用斜对称条件 $(Q^\top V)^\top = -(Q^\top V)$ 捕捉。

2. **投影公式**：$P(\Delta) = Q\operatorname{Skew}(Q^\top\Delta)$，利用正交性 $Q^\top Q = I$ 证明幂等性，利用"斜对称×对称迹为零"证明正交补性。

3. **关键恒等式**：$\operatorname{tr}(\Omega S) = 0$（$\Omega$ 斜、$S$ 对称），是整个正交性证明的核心，通过迹的转置不变性和乘法交换性得到。

与球面（习题 2.6.1）相比，正交群的切空间由矩阵方程（斜对称条件）而非向量正交性定义，投影公式也更复杂，需要 Frobenius 内积而非欧氏内积。两者的证明结构高度平行，体现了黎曼几何在不同约束曲面上的统一框架。
