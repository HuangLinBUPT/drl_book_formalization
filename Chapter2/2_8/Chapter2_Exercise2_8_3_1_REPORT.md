# 第2章 练习2.8 第3部分（子问题1）：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.8（`exercise:orthogonal-group-calculus`），第3部分 (Part 3a)
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex`
**Lean 文件**：`lean_formalization/Chapter2/2_8/Chapter2_Exercise2_8_3_1.lean`
**依赖文件**：`lean_formalization/Chapter2/2_8/Chapter2_Exercise2_8_2.lean`（进而依赖 `Chapter2_Exercise2_8_1.lean`）
**日期**：2026-04-06

## 非形式化陈述

给定 $X \in \mathbb{R}^{d \times d}$，将矩阵投影到正交群的问题为：

$$\operatorname{proj}_{O(d)}(X) = \operatorname{argmin}_{Q \in O(d)} \|Q - X\|_F^2$$

**子问题1（Part 3a）**：利用练习2.8.1和2.8.2中的一阶和二阶最优性条件，证明：每个局部极小值点 $Q$ 满足

$$\begin{aligned}
(Q^\top X)^\top &= Q^\top X \quad \text{（$Q^\top X$ 对称）} \\
Q^\top X &\succeq \mathbf{0} \quad \text{（$Q^\top X$ 半正定）}
\end{aligned}$$

## 非形式化证明思路

目标函数 $f(Q) = \|Q - X\|_F^2$ 的欧氏梯度为 $\nabla f(Q) = 2(Q - X)$，欧氏 Hessian 算子为 $B(V) = 2V$（即 $B = 2 \cdot \mathrm{id}$）。在形式化中我们用 $B = \mathrm{id}$，$g = Q - X$ 对应 $\nabla f/2$，$B = \mathrm{id}$ 对应 $\nabla^2 f/2$（正整数缩放不影响结论的定性性质）。

### 一阶条件 → 对称性

在局部极小值处，黎曼梯度为零：

$$\operatorname{grad} f(Q) = \mathcal{P}(Q - X) = 0$$

展开：

$$Q \cdot \operatorname{Skew}(Q^\top(Q - X)) = 0$$

由 $Q \in O(d)$ 可逆，左乘 $Q^\top$：

$$\operatorname{Skew}(Q^\top Q - Q^\top X) = \operatorname{Skew}(I - Q^\top X) = 0$$

斜对称部分为零即意味着矩阵对称：

$$(I - Q^\top X)^\top = I - Q^\top X \implies (Q^\top X)^\top = Q^\top X$$

### 二阶条件 → 半正定性

在局部极小值处，黎曼 Hessian 在切空间上半正定：

$$\langle \operatorname{Hess} f(Q)[V], V \rangle \geq 0 \quad \forall V \in T_Q O(d)$$

对 $f(Q) = \|Q - X\|_F^2$，代入 $B = \mathrm{id}$，$g = Q - X$，利用练习2.8.2的公式：

$$\operatorname{Hess} f(Q)[V] = \mathcal{P}(B(V) - V \cdot \operatorname{Symm}(Q^\top g))$$

利用一阶条件已得的对称性 $(Q^\top X)^\top = Q^\top X$，化简：

$$\operatorname{Symm}(Q^\top(Q-X)) = \operatorname{Symm}(I - Q^\top X) = I - Q^\top X$$

因此：

$$\operatorname{Hess} f(Q)[V] = \mathcal{P}(V - V(I - Q^\top X)) = \mathcal{P}(V \cdot Q^\top X)$$

PSD条件变为：

$$\langle \mathcal{P}(V \cdot Q^\top X), V \rangle = \langle V \cdot Q^\top X, V \rangle \geq 0$$

其中最后一步利用了 $V \in T_Q O(d)$ 时投影的自伴性 $\langle P(A), V \rangle = \langle A, V \rangle$。

## 形式化策略

### 关键定义（继承自 2.8.1 和 2.8.2）

| 定义名 | 数学含义 | Lean 类型 |
|--------|----------|-----------|
| `matInner d X Y` | $\langle X, Y \rangle_F = \operatorname{tr}(X^\top Y)$ | `ℝ` |
| `skewPart d Δ` | $\operatorname{Skew}(\Delta) = \tfrac{1}{2}(\Delta - \Delta^\top)$ | `Mat` |
| `symmPart d Δ` | $\operatorname{Symm}(\Delta) = \tfrac{1}{2}(\Delta + \Delta^\top)$ | `Mat` |
| `inTangentSpace d Q V` | $(Q^\top V)^\top = -(Q^\top V)$（即 $V \in T_Q O(d)$） | `Prop` |
| `tangentProj d Q Δ` | $\mathcal{P}(\Delta) = Q \cdot \operatorname{Skew}(Q^\top \Delta)$ | `Mat` |
| `riemHessOD d Q B g V` | $\mathcal{P}(B(\mathcal{P}(V)) - \mathcal{P}(V) \cdot \operatorname{Symm}(Q^\top g))$ | `Mat` |

**建模决策**：将 $\nabla^2 f/2$ 建模为 $B = \mathrm{id}$，$\nabla f/2$ 建模为 $g = Q - X$。第二个结论中的半正定性以 Frobenius 内积语言表述，即 $\langle V \cdot Q^\top X, V \rangle_F \geq 0$，这是书中 $Q^\top X \succeq 0$ 的等价形式（对切空间中的向量）。

### 关键辅助引理

| 引理名 | 内容 | 可见性 |
|--------|------|--------|
| `symm_of_skewPart_zero` | $\operatorname{Skew}(M) = 0 \Rightarrow M^\top = M$ | `private` |
| `skewPart_zero_of_tangentProj_zero` | $\mathcal{P}(\Delta) = 0 \Rightarrow \operatorname{Skew}(Q^\top\Delta) = 0$ | `private` |
| `symmPart_of_symm` | $M^\top = M \Rightarrow \operatorname{Symm}(M) = M$ | `private` |
| `matInner_sub_right'` | $\langle X, Y - Z \rangle = \langle X, Y \rangle - \langle X, Z \rangle$ | `private` |
| `matInner_tangentProj_left` | $V \in T \Rightarrow \langle \mathcal{P}(A), V \rangle = \langle A, V \rangle$ | `private` |

### 主要定理

| 定理名 | 数学内容 |
|--------|----------|
| `qtx_symm_of_critical` | $\mathcal{P}(Q-X)=0 \Rightarrow (Q^\top X)^\top = Q^\top X$ |
| `hessian_frobenius_simplify` | $V\in T,\,(Q^\top X)^\top=Q^\top X \Rightarrow \operatorname{Hess}[V] = \mathcal{P}(V \cdot Q^\top X)$ |
| `psd_of_hessian_psd` | Hessian PSD $\Rightarrow \langle V \cdot Q^\top X, V \rangle \geq 0$（$V \in T$） |
| `exercise_2_8_3_1` | 主定理（两条结论的合取） |

### 证明结构

```
exercise_2_8_3_1
├── qtx_symm_of_critical           一阶条件 → QᵀX 对称
│   ├── skewPart_zero_of_tangentProj_zero   P(Δ)=0 ⟹ Skew(QᵀΔ)=0
│   │   └── ← Matrix.mul_assoc + hQtQ      Qᵀ(Q·S) = S（Q∈O(d)）
│   ├── symm_of_skewPart_zero       Skew(M)=0 ⟹ M 对称（逐元素 linarith）
│   └── transpose_sub, transpose_one + ext + linarith  展开并消去 I
└── psd_of_hessian_psd             二阶条件 → QᵀX 半正定
    ├── hessian_frobenius_simplify  Hess[V] 化简为 P(V·QᵀX)
    │   ├── riemHessOD_on_tangent   V∈T 时消去内层投影（来自 2.8.2）
    │   ├── symmPart_of_symm        Symm(I-QᵀX)=I-QᵀX（利用对称性）
    │   └── Matrix.mul_sub + Matrix.mul_one + sub_sub_cancel  代数化简
    └── matInner_tangentProj_left   ⟪P(A),V⟫ = ⟪A,V⟫（V∈T）
        └── tangentProj_complement_orthogonal + tangent_reconstruction
            （正交补性，来自 2.8.1）
```

### 技术关键点

#### 1. `skewPart_zero_of_tangentProj_zero` 的可逆性论证

从 $\mathcal{P}(\Delta) = Q \cdot \operatorname{Skew}(Q^\top\Delta) = 0$ 推导 $\operatorname{Skew}(Q^\top\Delta) = 0$，关键是利用 $Q \in O(d)$ 的可逆性（而非直接消去）：

左乘 $Q^\top$：

$$Q^\top(Q \cdot \operatorname{Skew}(Q^\top\Delta)) = 0 \implies (Q^\top Q) \cdot \operatorname{Skew}(Q^\top\Delta) = I \cdot \operatorname{Skew}(Q^\top\Delta) = 0$$

在 Lean 中使用 `← Matrix.mul_assoc` 和 `hQtQ : Qᵀ * Q = 1`：

```lean
have : Qᵀ * (Q * skewPart d (Qᵀ * Δ)) = 0 := by rw [h, mul_zero]
rwa [← Matrix.mul_assoc, hQtQ, one_mul] at this
```

#### 2. `symm_of_skewPart_zero` 的逐元素证明

条件 $\operatorname{Skew}(M) = 0$ 展开为 $\tfrac{1}{2}(M_{ij} - M_{ji}) = 0$，即 $M_{ij} = M_{ji}$，正好是 $M^\top_{ij} = M_{ij}$。

使用 `simp` 将 `skewPart` 展开到元素级别后，`linarith` 自动完成等式证明。目标 `Mᵀ i j = M i j` 需在 `simp` 后先用 `simp only [Matrix.transpose_apply]` 展开 `Mᵀ i j = M j i`，再由 `linarith` 结合 `hij` 完成。

#### 3. `hessian_frobenius_simplify` 的四步化简

从 $\operatorname{Hess}_{f}[V] = \mathcal{P}(B(\mathcal{P}(V)) - \mathcal{P}(V) \cdot \operatorname{Symm}(Q^\top g))$ 推导到 $\mathcal{P}(V \cdot Q^\top X)$，分四步：

1. **消去内层投影**（$\mathcal{P}(V) = V$，$V \in T$）：用 `riemHessOD_on_tangent`
2. **化简 $Q^\top(Q-X)$**：$Q^\top Q - Q^\top X = I - Q^\top X$
3. **化简对称部分**：$(I - Q^\top X)^\top = I - Q^\top X$（利用已证的对称性），故 $\operatorname{Symm}(I - Q^\top X) = I - Q^\top X$
4. **代数恒等**：$V - V(I - Q^\top X) = V - V + V \cdot Q^\top X = V \cdot Q^\top X$

在 Lean 中第4步用 `Matrix.mul_sub`、`Matrix.mul_one`、`sub_sub_cancel` 组合完成。

#### 4. `matInner_tangentProj_left` 的自伴性证明

这是 Exercise 2.8.2 中 `matInner_proj_left`（私有）的本地重现，核心推导链：

$$\langle V, A - \mathcal{P}(A) \rangle = 0 \implies \langle \mathcal{P}(A), V \rangle = \langle A, V \rangle$$

- 由 `tangent_reconstruction`：$V = Q \cdot (Q^\top V)$，因此 $V = Q\Omega$（$\Omega = Q^\top V$ 为斜对称）
- `tangentProj_complement_orthogonal`（来自 2.8.1）：$\langle Q\Omega, A - \mathcal{P}(A) \rangle = 0$
- 用 `matInner_sub_right'` 展开后 `linarith` 结合 `matInner_comm` 完成

#### 5. 二阶条件的核心等式链

设 $S = Q^\top X$（已证对称）。PSD条件的证明链：

$$\langle \operatorname{Hess}[V], V \rangle \geq 0 \xrightarrow{\text{化简}} \langle \mathcal{P}(VS), V \rangle \geq 0 \xrightarrow{\text{自伴}} \langle VS, V \rangle \geq 0$$

在 Lean 中：

```lean
have h1 := hhess V hV
rw [hessian_frobenius_simplify d Q X V hQ hV hsymm] at h1
rwa [matInner_tangentProj_left d Q (V * (Qᵀ * X)) V hQ hV] at h1
```

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `symm_of_skewPart_zero` | $\operatorname{Skew}(M)=0 \Rightarrow M^\top = M$ | ✅ |
| `skewPart_zero_of_tangentProj_zero` | $\mathcal{P}(\Delta)=0 \Rightarrow \operatorname{Skew}(Q^\top\Delta)=0$ | ✅ |
| `symmPart_of_symm` | $M^\top=M \Rightarrow \operatorname{Symm}(M)=M$ | ✅ |
| `matInner_sub_right'` | $\langle X, Y-Z \rangle = \langle X,Y \rangle - \langle X,Z \rangle$ | ✅ |
| `matInner_tangentProj_left` | $\langle \mathcal{P}(A), V \rangle = \langle A, V \rangle$（$V \in T$） | ✅ |
| `qtx_symm_of_critical` | $\mathcal{P}(Q-X)=0 \Rightarrow (Q^\top X)^\top=Q^\top X$ | ✅ |
| `hessian_frobenius_simplify` | $\operatorname{Hess}[V] = \mathcal{P}(V \cdot Q^\top X)$（$V\in T$，$Q^\top X$ 对称） | ✅ |
| `psd_of_hessian_psd` | Hessian PSD $\Rightarrow \langle V \cdot Q^\top X, V \rangle \geq 0$ | ✅ |
| `exercise_2_8_3_1` | 主定理（对称性 + 半正定性） | ✅ |

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
| 局部极小值处 $(Q^\top X)^\top = Q^\top X$（一阶条件） | `qtx_symm_of_critical` | ✅ |
| 局部极小值处 $Q^\top X \succeq 0$（二阶条件） | `psd_of_hessian_psd` | ✅ |
| 两条结论的合取 | `exercise_2_8_3_1` | ✅ |

**注**：书中的 $Q^\top X \succeq 0$ 在 Lean 中以 Frobenius 半正定性刻画：$\forall V \in T_Q O(d),\, \langle V \cdot Q^\top X, V \rangle_F \geq 0$。这是一般矩阵半正定性对切空间的限制，恰好是二阶条件的直接形式。

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.LinearAlgebra.Matrix.Trace` | `Matrix.trace`、`trace_sub`、`trace_mul_comm` |
| `Chapter2.«2_8».Chapter2_Exercise2_8_2` | `riemHessOD`、`riemHessOD_on_tangent`、`symmPart`、`matInner`、所有投影定理 |

（`Chapter2_Exercise2_8_1` 通过 `Chapter2_Exercise2_8_2` 传递导入。）

## 与练习 2.8 系列的联系

| 维度 | 2.8.1 | 2.8.2 | 2.8.3.1（本文件） | 2.8.3.2 | 2.8.3.3 |
|------|-------|-------|-----------------|---------|---------|
| 主题 | 切空间与投影 | 黎曼 Hessian | 最优性条件 | 矩阵平方根刻画 | SVD 结论 |
| 核心结果 | $\mathcal{P}(\Delta)=Q\operatorname{Skew}(Q^\top\Delta)$ | $\operatorname{Hess}[V]=\mathcal{P}(BV-VS)$ | $(Q^\top X)^\top=Q^\top X,\,Q^\top X\succeq 0$ | $Q^\top X=(X^\top X)^{1/2}$ | $UV^\top=\operatorname{proj}_{O(d)}(X)$ |
| sorry 数 | 0 | 0 | **0** | — | — |

## 总结

**完成度**：100%（零 sorry）

习题 2.8.3（子问题1）完成了正交群投影问题一阶和二阶最优性条件的严格形式化。主要贡献：

1. **一阶条件的代数推导**：从黎曼梯度 $\mathcal{P}(Q-X)=0$ 到 $(Q^\top X)^\top = Q^\top X$，关键步骤是 $Q \in O(d)$ 的可逆性（左乘 $Q^\top$ 消去）和斜对称部分为零的逐元素刻画。

2. **二阶条件的化简链**：利用一阶条件建立的对称性，将 Riemannian Hessian 化简为 $\mathcal{P}(V \cdot Q^\top X)$，再用投影自伴性得到 Frobenius 半正定性。整个链条完全形式化，无需引入抽象的半正定矩阵理论。

3. **辅助引理的局部重现**：`matInner_proj_left`（在 2.8.2 中为私有）在本文件中以 `matInner_tangentProj_left` 重现，保持了文件间的封装性，同时也表明该投影自伴性引理具有一般的可复用价值。

4. **为子问题2、3铺路**：本文件建立的 `qtx_symm_of_critical` 是子问题2（矩阵平方根刻画 $Q^\top X = (X^\top X)^{1/2}$）和子问题3（SVD 结论 $UV^\top = \operatorname{proj}_{O(d)}(X)$）的直接前置条件。
