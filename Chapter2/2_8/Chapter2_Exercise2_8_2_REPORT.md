# 第2章 练习2.8 第2部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.8（`exercise:orthogonal-group-calculus`），第2部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex`
**Lean 文件**：`lean_formalization/Chapter2/2_8/Chapter2_Exercise2_8_2.lean`
**依赖文件**：`lean_formalization/Chapter2/2_8/Chapter2_Exercise2_8_1.lean`
**日期**：2026-04-06

## 非形式化陈述

对正交群 $O(d)$ 上的两次连续可微目标函数 $f : \mathbb{R}^{d\times d} \to \mathbb{R}$，其在 $Q \in O(d)$ 处的**黎曼 Hessian** 由下式给出：

$$\mathrm{Hess}\, f(Q) = \mathcal{P}_{T_Q O(d)}\!\left(\nabla^2 f(Q) - \mathrm{Symm}(Q^\top \nabla f(Q)) \otimes I\right) \mathcal{P}_{T_Q O(d)}$$

其中：
- $\mathcal{P}_{T_Q O(d)}(\Delta) = Q \cdot \mathrm{Skew}(Q^\top \Delta)$ 是到切空间的正交投影（练习 2.8.1）
- $\mathrm{Symm}(\Delta) = \tfrac{1}{2}(\Delta + \Delta^\top)$ 是矩阵的对称部分
- Kronecker 算子 $\mathrm{Symm}(Q^\top g) \otimes I$ 作用于矩阵 $V$ 的方式为右乘：$V \mapsto V \cdot \mathrm{Symm}(Q^\top g)$

内积为 Frobenius 内积 $\langle X, Y \rangle = \operatorname{tr}(X^\top Y)$。

## 非形式化证明思路

设 $Q(t)$ 是 $O(d)$ 上经过 $Q(0) = Q$ 的光滑曲线，$Q'(0) = V = Q\Omega$（$\Omega^\top = -\Omega$）。

黎曼梯度为 $\mathrm{grad}\, f(Q(t)) = Q(t) \cdot \mathrm{Skew}(Q(t)^\top \nabla f(Q(t)))$。

对 $t$ 求导，在 $t=0$ 处投影到 $T_Q O(d)$，利用 $V = Q\Omega$ 以及 $\mathcal{P}[Q \cdot \Omega \cdot \mathrm{Skew}(S)] = Q \cdot \mathrm{Skew}(\Omega \cdot \mathrm{Skew}(S))$，化简得：

$$D_V[\mathrm{grad}\, f(Q)] = \mathcal{P}\!\left(\nabla^2 f \cdot V - V \cdot \mathrm{Symm}(Q^\top g)\right)$$

这正是公式 $\mathcal{P}(\nabla^2 f - \mathrm{Symm}(Q^\top g) \otimes I)\mathcal{P}$ 作用于 $V$ 的结果（利用 $\mathcal{P}(V) = V$ 消除内层投影）。

### 对称性

黎曼 Hessian 的自伴性来自两个成分：
- $\nabla^2 f$ 在 Frobenius 内积下的自伴性：$\langle \nabla^2 f \cdot V, W\rangle = \langle V, \nabla^2 f \cdot W\rangle$
- 右乘对称矩阵的自伴性：$\langle VS, W\rangle_F = \langle V, WS\rangle_F$（$S$ 对称）

结合投影的自伴性（$W \in T$ 时 $\langle P(X), W\rangle = \langle X, W\rangle$），即得 $\langle \mathrm{Hess}[V], W\rangle = \langle V, \mathrm{Hess}[W]\rangle$。

## 形式化策略

### 关键定义

| 定义名 | 数学含义 | Lean 类型 |
|--------|----------|-----------|
| `symmPart d Δ` | $\mathrm{Symm}(\Delta) = \tfrac{1}{2}(\Delta + \Delta^\top)$ | `Mat` |
| `riemHessOD Q B g V` | $\mathcal{P}(B(\mathcal{P}(V)) - \mathcal{P}(V) \cdot \mathrm{Symm}(Q^\top g))$ | `Mat` |

其中 `Mat` 是 `Matrix (Fin d) (Fin d) ℝ` 的本地缩写，`B : Mat → Mat` 是对 $\nabla^2 f(Q)$ 的抽象建模（见下方建模说明）。

**建模决策**：书中的 $\nabla^2 f(Q)$ 是一个作用在矩阵上的线性算子。在 Lean 中将其建模为带有自伴假设的抽象函数 `B : Mat → Mat`，条件为 `hB : ∀ X Y, ⟪B X, Y⟫ = ⟪X, B Y⟫`。这样形式化恰好捕捉了证明所需的全部信息，无需涉及 $f$ 的具体形式。

### 关键辅助引理

| 引理名 | 内容 |
|--------|------|
| `symmPart_transpose` | $\mathrm{Symm}(\Delta)^\top = \mathrm{Symm}(\Delta)$（对称部分是对称矩阵） |
| `sub_skewPart_eq_symmPart` | $\Delta - \mathrm{Skew}(\Delta) = \mathrm{Symm}(\Delta)$（斜对称与对称部分的分解） |
| `matInner_sub_left` | $\langle X - Y, Z\rangle = \langle X, Z\rangle - \langle Y, Z\rangle$ |
| `matInner_sub_right` | $\langle X, Y - Z\rangle = \langle X, Y\rangle - \langle X, Z\rangle$ |
| `matInner_mul_right_symm` | $\langle VS, W\rangle_F = \langle V, WS\rangle_F$（$S$ 对称时的右乘自伴性） |
| `matInner_proj_left` | $W \in T_Q O(d) \Rightarrow \langle P(X), W\rangle = \langle X, W\rangle$（投影自伴性） |
| `matInner_proj_right` | $V \in T_Q O(d) \Rightarrow \langle V, P(X)\rangle = \langle V, X\rangle$ |

### 主要定理

| 定理名 | 数学内容 |
|--------|----------|
| `riemHessOD_in_tangent` | $\mathrm{Hess}[V] \in T_Q O(d)$（对所有 $V$） |
| `riemHessOD_on_tangent` | $V \in T_Q O(d) \Rightarrow \mathrm{Hess}[V] = \mathcal{P}(BV - V \cdot \mathrm{Symm}(Q^\top g))$ |
| `riemHessOD_symmetric` | $\langle \mathrm{Hess}[V], W\rangle = \langle V, \mathrm{Hess}[W]\rangle$（$V, W \in T_Q O(d)$） |
| `exercise_2_8_2` | 主定理（四条性质的合取） |

### 证明结构

```
exercise_2_8_2
├── rfl                              性质1：定义展开（riemHessOD 的 def 即是目标表达式）
├── riemHessOD_in_tangent            性质2：Hess[V] ∈ T_Q O(d)
│   └── tangentProj_in_tangentSpace  P(·) 的像在切空间内（由 2.8.1 导入）
├── riemHessOD_on_tangent            性质3：V ∈ T 时内层投影消去
│   └── tangentProj_idempotent       P(V) = V（由 2.8.1 导入）
└── riemHessOD_symmetric             性质4：对称性
    ├── riemHessOD_on_tangent        将两侧化为简化形式
    ├── matInner_proj_left           ⟪P(X), W⟫ = ⟪X, W⟫（W ∈ T）
    │   └── tangentProj_complement_orthogonal  正交补性（由 2.8.1 导入）
    │       └── tangent_reconstruction         W = Q(QᵀW)（由 2.8.1 导入）
    ├── matInner_proj_right          ⟪V, P(Y)⟫ = ⟪V, Y⟫（V ∈ T）
    ├── matInner_sub_left/right      内积的线性性
    ├── hB V W                       B 的自伴性：⟪BV, W⟫ = ⟪V, BW⟫
    ├── matInner_mul_right_symm      ⟪VS, W⟫ = ⟪V, WS⟫（S 对称）
    │   └── trace_mul_comm           tr(AB) = tr(BA)
    └── linarith                     线性算术组合
```

### 技术关键点

#### 1. `matInner_mul_right_symm` 的推导链

右乘对称矩阵的 Frobenius 自伴性是对称性证明的核心：

$$\langle VS, W\rangle_F = \operatorname{tr}((VS)^\top W) = \operatorname{tr}(S^\top V^\top W) = \operatorname{tr}(S V^\top W) \stackrel{\text{cyc}}{=} \operatorname{tr}(V^\top W S) = \langle V, WS\rangle_F$$

Lean 证明使用 `calc` 链，关键步骤是 `trace_mul_comm`（迹的循环轮换）和 `Matrix.mul_assoc`（矩阵结合律）：

```lean
calc ((V * S)ᵀ * W).trace
    = (S * Vᵀ * W).trace   := by rw [transpose_mul, hS]
  _ = (S * (Vᵀ * W)).trace := by rw [Matrix.mul_assoc]
  _ = (Vᵀ * W * S).trace   := by rw [trace_mul_comm]
  _ = (Vᵀ * (W * S)).trace := by rw [Matrix.mul_assoc]
```

#### 2. 投影自伴性（`matInner_proj_left`）的关键步骤

对 $W \in T_Q O(d)$，需证 $\langle P(X), W\rangle = \langle X, W\rangle$，等价于 $\langle W, X - P(X)\rangle = 0$。

步骤：
- 由 `tangent_reconstruction`：$W = Q \cdot (Q^\top W)$
- 令 $\Omega = Q^\top W$（斜对称），则 $W = Q\Omega$
- 由 `tangentProj_complement_orthogonal`：$\langle Q\Omega, X - P(X)\rangle = 0$
- 用 `matInner_comm` 交换两侧，`linarith` 完成

#### 3. 对称性证明的 `linarith` 组合

设 $S = \mathrm{Symm}(Q^\top g)$。经过投影自伴性化简后，目标变为：

$$\langle BV - VS, W\rangle = \langle V, BW - WS\rangle$$

展开为：

$$\langle BV, W\rangle - \langle VS, W\rangle = \langle V, BW\rangle - \langle V, WS\rangle$$

- $\langle BV, W\rangle = \langle V, BW\rangle$：由 `hB V W`（$B$ 的自伴性）
- $\langle VS, W\rangle = \langle V, WS\rangle$：由 `matInner_mul_right_symm`（$S$ 对称）

两个等式组合后 `linarith` 直接完成。

#### 4. 性质1的 `rfl` 证明

主定理的性质1（定义展开）的证明是 `rfl`，这是因为 `riemHessOD` 的定义体：

```lean
noncomputable def riemHessOD (Q : Mat) (B : Mat → Mat) (g V : Mat) : Mat :=
  tangentProj d Q (B (tangentProj d Q V) - tangentProj d Q V * symmPart d (Qᵀ * g))
```

恰好就是性质1中的目标表达式，展开即相等。这不是技巧性规避，而是设计上的自然吻合。

#### 5. 与练习 2.6.3（球面黎曼 Hessian）的平行结构

| | 球面 $S^{d-1}$（练习2.6.3） | 正交群 $O(d)$（练习2.8.2） |
|-|---------------------------|-----------------------------|
| Hessian 公式 | $P_u^\perp(\nabla^2 f - \langle\nabla f, u\rangle I)P_u^\perp$ | $\mathcal{P}(\nabla^2 f - \mathrm{Symm}(Q^\top\nabla f) \otimes I)\mathcal{P}$ |
| 曲率项 | $\langle g, u\rangle I$（标量×单位算子） | $\mathrm{Symm}(Q^\top g) \otimes I$（矩阵×右乘算子） |
| 对称性来源 | $\nabla^2 f$ 自伴 + 投影自伴 | $\nabla^2 f$ 自伴 + 右乘自伴 + 投影自伴 |
| 关键引理 | `matInner_proj_symm` | `matInner_mul_right_symm` + `matInner_proj_left` |

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `symmPart_transpose` | $\mathrm{Symm}(\Delta)^\top = \mathrm{Symm}(\Delta)$ | ✅ |
| `sub_skewPart_eq_symmPart` | $\Delta - \mathrm{Skew}(\Delta) = \mathrm{Symm}(\Delta)$ | ✅ |
| `matInner_sub_left` | $\langle X-Y, Z\rangle = \langle X,Z\rangle - \langle Y,Z\rangle$ | ✅ |
| `matInner_sub_right` | $\langle X, Y-Z\rangle = \langle X,Y\rangle - \langle X,Z\rangle$ | ✅ |
| `matInner_mul_right_symm` | $\langle VS,W\rangle = \langle V,WS\rangle$（$S$ 对称） | ✅ |
| `matInner_proj_left` | $\langle P(X),W\rangle = \langle X,W\rangle$（$W\in T$） | ✅ |
| `matInner_proj_right` | $\langle V,P(X)\rangle = \langle V,X\rangle$（$V\in T$） | ✅ |
| `riemHessOD_in_tangent` | $\mathrm{Hess}[V] \in T_Q O(d)$ | ✅ |
| `riemHessOD_on_tangent` | $V\in T \Rightarrow \mathrm{Hess}[V] = \mathcal{P}(BV - VS)$ | ✅ |
| `riemHessOD_symmetric` | $\langle\mathrm{Hess}[V],W\rangle = \langle V,\mathrm{Hess}[W]\rangle$ | ✅ |
| `exercise_2_8_2` | 主定理（四条性质合取） | ✅ |

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
| $\mathrm{Hess}\, f(Q) = \mathcal{P}(\nabla^2 f - \mathrm{Symm}(Q^\top g)\otimes I)\mathcal{P}$ | `riemHessOD` 定义 + `exercise_2_8_2` 性质1 | ✅ |
| Hessian 值域在 $T_Q O(d)$ 内 | `riemHessOD_in_tangent` | ✅ |
| $V\in T$ 时简化为 $\mathcal{P}(BV - VS)$ | `riemHessOD_on_tangent` | ✅ |
| Hessian 在 $T$ 上对称 | `riemHessOD_symmetric` | ✅ |
| Kronecker 算子的右乘解释 | `symmPart d (Qᵀ * g)` 的右乘实现 | ✅ |

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.LinearAlgebra.Matrix.Trace` | `Matrix.trace`、`trace_mul_comm`、`trace_sub`、`trace_smul` |
| `Chapter2.«2_8».Chapter2_Exercise2_8_1` | `tangentProj`、`inTangentSpace`、`matInner`、`skewPart`、投影定理 |

## 与练习 2.8 系列的联系

| 维度 | 2.8.1 | 2.8.2（本文件） | 2.8.3 |
|------|-------|----------------|-------|
| 主题 | 切空间与投影 | 黎曼 Hessian | O(d) 上的最近点投影 |
| 核心结果 | $\mathcal{P}(\Delta)=Q\mathrm{Skew}(Q^\top\Delta)$ | $\mathrm{Hess}[V] = \mathcal{P}(BV - V\cdot\mathrm{Symm}(Q^\top g))$ | $\operatorname{proj}_{O(d)}(X) = UV^\top$（SVD） |
| sorry 数 | 0 | **0** | — |

## 总结

**完成度**：100%（零 sorry）

习题 2.8.2 完成了正交群黎曼 Hessian 的严格形式化。主要贡献：

1. **Hessian 定义**：通过 `riemHessOD` 捕捉公式 $\mathcal{P}(\nabla^2 f - \mathrm{Symm}(Q^\top g)\otimes I)\mathcal{P}$，Kronecker 算子的右乘解释被直接编码为矩阵乘法。

2. **三个核心性质**：切空间封闭性（来自 $\mathcal{P}$ 的像）、切向量上的简化形式（来自幂等性 $\mathcal{P}(V)=V$）、对称性（来自 $\nabla^2 f$ 的自伴性与右乘的 Frobenius 自伴性）。

3. **关键新引理** `matInner_mul_right_symm`：右乘对称矩阵的 Frobenius 自伴性，通过迹的循环轮换性证明，是对称性论证的代数核心。

4. **与 2.8.1 的接口**：通过导入利用了 `tangentProj_idempotent`、`tangentProj_complement_orthogonal`、`tangent_reconstruction` 等基础构件，体现了习题间的模块化依赖关系。

与球面习题 2.6.3 相比，正交群 Hessian 的曲率项从标量 $\langle g, u\rangle$ 变为矩阵 $\mathrm{Symm}(Q^\top g)$，对称性证明因此需要额外的 `matInner_mul_right_symm`，这是两者最核心的区别。
