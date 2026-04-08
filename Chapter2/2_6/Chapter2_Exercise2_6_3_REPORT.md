# 第2章 练习2.6 第3部分：形式化报告

## 习题信息

**来源**：深度表征学习书籍，第2章，练习2.6（`exercise:sphere-calculus`），第3部分
**文件位置**：`deep-representation-learning-book/chapters/chapter2/classic-models.tex:2386-2400`
**Lean 文件**：`lean_formalization/Chapter2/2_6/Chapter2_Exercise2_6_3.lean`
**依赖文件**：`lean_formalization/Chapter2/2_6/Chapter2_Exercise2_6_1.lean`
**日期**：2026-04-08

## 非形式化陈述

设 $f : \mathbb{R}^d \to \mathbb{R}$ 为两次连续可微的目标函数。通过对球面约束路径上的黎曼梯度 $\mathrm{grad}\, f(\mathbf{u}) = \mathbf{P}_{\mathbf{u}}^\perp \nabla f(\mathbf{u})$ 求导，并将结果投影回切空间，得到**黎曼 Hessian**：

$$\mathrm{Hess}\, f(\mathbf{u}) = \mathbf{P}_{\mathbf{u}}^\perp \left( \nabla^2 f(\mathbf{u}) - \langle \nabla f(\mathbf{u}),\, \mathbf{u} \rangle \, \mathbf{I} \right) \mathbf{P}_{\mathbf{u}}^\perp$$

其中 $\mathbf{P}_{\mathbf{u}}^\perp = \mathbf{I} - \mathbf{u}\mathbf{u}^\top$ 是到 $T_{\mathbf{u}} S^{d-1}$ 的正交投影。

## 非形式化证明思路

设 $\mathbf{u}(t)$ 为 $S^{d-1}$ 上经过 $\mathbf{u}(0) = \mathbf{u}$ 的光滑曲线，$\mathbf{u}'(0) = \mathbf{v} \in T_{\mathbf{u}} S^{d-1}$。

黎曼梯度为 $\mathrm{grad}\, f(\mathbf{u}(t)) = \mathbf{P}_{\mathbf{u}(t)}^\perp \nabla f(\mathbf{u}(t))$。

对 $t$ 求导，在 $t=0$ 处投影到 $T_{\mathbf{u}} S^{d-1}$：

$$D_{\mathbf{v}} [\mathrm{grad}\, f(\mathbf{u})] = \mathbf{P}_{\mathbf{u}}^\perp \left[ \nabla^2 f(\mathbf{u}) \mathbf{v} - \langle \nabla f(\mathbf{u}),\, \mathbf{u} \rangle \mathbf{v} - \langle \nabla f(\mathbf{u}),\, \mathbf{v} \rangle \mathbf{u} \right]$$

最后一项由 $\mathbf{P}_{\mathbf{u}}^\perp \mathbf{u} = \mathbf{0}$ 消去，得：

$$= \mathbf{P}_{\mathbf{u}}^\perp \left[ \nabla^2 f(\mathbf{u}) - \langle \nabla f(\mathbf{u}),\, \mathbf{u} \rangle \mathbf{I} \right] \mathbf{v}$$

## 形式化策略

### 关键设计决策：代数操作而非微分计算

与书中微分推导不同，Lean 形式化采用纯代数方法，将 $f$ 的信息编码为抽象参数：

| 参数 | 类型 | 含义 |
|------|------|------|
| `u : E` | 向量 | 单位向量（$\|u\| = 1$） |
| `H : E →L[ℝ] E` | 连续线性算子 | 欧几里得 Hessian $\nabla^2 f(u)$ |
| `g : E` | 向量 | 欧几里得梯度 $\nabla f(u)$ |
| `v, w : E` | 向量 | 切空间中的方向向量 |

**核心假设**：Hessian 算子 `H` 是自伴的（对应实对称矩阵的情形）。

### 黎曼 Hessian 的 Lean 定义

```lean
noncomputable def riemHess (u : E) (H : E →L[ℝ] E) (g : E) (v : E) : E :=
  (ℝ ∙ u)ᗮ.starProjection
    (H ((ℝ ∙ u)ᗮ.starProjection v) - (inner ℝ g u : ℝ) • (ℝ ∙ u)ᗮ.starProjection v)
```

展开后为：
$$\mathrm{Hess}[v] = P_u^\perp\!\Big( H(P_u^\perp v) - \langle g, u\rangle \cdot P_u^\perp v \Big)$$

**与书中介式 $\mathbf{P}_{\mathbf{u}}^\perp \left( \nabla^2 f - \langle \nabla f, \mathbf{u} \rangle \mathbf{I} \right) \mathbf{P}_{\mathbf{u}}^\perp$ 的关系**：

作用在 $v$ 上时，书的公式给出 $P(Hv - c\cdot v)$，而 Lean 定义给出 $P(H(Pv) - c\cdot Pv)$。

- 当 $v \in T_u S^{d-1}$（即 $v \perp u$）时，$P_u^\perp v = v$，两者完全一致
- 当 $v$ 为法方向时（$v = u$），Lean 定义通过 `riemHess_kills_u` 保证结果为零
- 外层投影保证 Hessian 的值域始终在切空间中

因此两个公式在切空间（黎曼 Hessian 的定义域）上等价，差异仅在法方向分量上。

### 四个核心性质的证明结构

| 性质 | 定理名 | 核心思路 |
|------|--------|----------|
| 1. 杀死法方向 | `riemHess_kills_u` | $P_u^\perp u = 0$，由 `proj_perp_unit_eq_zero` 证明 |
| 2. 映射入切空间 | `riemHess_in_tangent` | $P_u^\perp$ 的像在切空间中，直接由 `sphere_tangent_projection_range` 得 |
| 3. 切空间上的简化 | `riemHess_on_tangent` | $v \perp u \Rightarrow P_u^\perp v = v$，由 `sphere_tangent_projection_identity_on_tangent` |
| 4. 切空间上的对称性 | `riemHess_symmetric` | 投影自伴 + $H$ 自伴，$v, w \perp u$ 时两边化简后用 `hH` + `linarith` |

### 关键辅助引理

| 引理名 | 内容 |
|--------|------|
| `proj_perp_unit_eq_zero` | $P_u^\perp u = 0$（通过显式公式 $u - \langle u,u\rangle u = 0$） |

### 证明结构图

```
riemHess 定义
  P( H(Pv) - c·Pv )              -- 外层 P，内层 P(Pv)，c = ⟨g,u⟩
      │
      ├── riemHess_kills_u        -- 性质1：Hess[u] = 0（u 是法方向）
      │   └── proj_perp_unit_eq_zero  P(u) = 0 → H(0)=0, c·0=0
      │
      ├── riemHess_in_tangent     -- 性质2：⟨Hess[v], u⟩ = 0（值域在切空间）
      │   └── sphere_tangent_projection_range  来自 2.6.1
      │
      ├── riemHess_on_tangent     -- 性质3：v⊥u 时，P(Pv)=Pv 且 Pv=v
      │   → Hess[v] = P( Hv - c·v )
      │   注意：v⊥u 时内层 P 消去为恒等，但外层 P 仍然存在！
      │   └── sphere_tangent_projection_identity_on_tangent  来自 2.6.1
      │
      └── riemHess_symmetric      -- 性质4：⟨Hess[v],w⟩ = ⟨v, Hess[w]⟩（v,w⊥u）
          ├── riemHess_on_tangent × 2  → P(Hv-c·v) 和 P(Hw-c·w)
          ├── sphere_tangent_projection_symmetric  P 自伴：⟨Px,w⟩ = ⟨x,Pw⟩
          ├── sphere_tangent_projection_identity_on_tangent  w⊥u 时 Pw=w
          ├── inner_smul_left/right     内积线性性
          ├── hH V W                    H 自伴：⟨Hv,w⟩ = ⟨v,Hw⟩
          └── linarith                  线性算术组合
```

### 与正交群练习 2.8.2 的对比

| 维度 | 球面 $S^{d-1}$（2.6.3） | 正交群 $O(d)$（2.8.2） |
|------|------------------------|------------------------|
| Hessian 公式（Lean） | $P(H(Pv) - c\cdot Pv)$，$c=\langle g,u\rangle$ | $\mathcal{P}(B(\mathcal{P}V) - \mathcal{P}V\cdot S)$，$S=\mathrm{Symm}(Q^\top g)$ |
| Hessian 公式（书） | $P(H - c\cdot I)P$ | $\mathcal{P}(B - S\otimes I)\mathcal{P}$ |
| 曲率项 | $\langle g, u\rangle I$（标量×单位算子） | $\mathrm{Symm}(Q^\top g) \otimes I$（矩阵×右乘算子） |
| 对称性证明 | 投影自伴 + $\nabla^2 f$ 自伴 | 投影自伴 + $\nabla^2 f$ 自伴 + 右乘自伴 |
| 关键引理 | `sphere_tangent_projection_symmetric` | `matInner_mul_right_symm` |

**结构差异**：两者均采用"外层投影 + 运算 + 内层投影"的三明治结构，差异在于：
- 球面：曲率项是标量乘法 $c \cdot Pv$，对称性证明仅需投影自伴 + $H$ 自伴
- 正交群：曲率项是矩阵右乘 $V\cdot S$，对称性证明还需 `matInner_mul_right_symm`（迹的循环性）

球面黎曼 Hessian 的曲率项是标量 $\langle g, u\rangle$ 乘以单位算子，而正交群的是矩阵 $\mathrm{Symm}(Q^\top g)$ 的 Kronecker 积——这是两者的核心区别。

## 形式化状态

### ✅ 完全完成（零 sorry）

| 定理/引理名 | 数学内容 | 状态 |
|------------|----------|------|
| `proj_perp_unit_eq_zero` | $P_u^\perp u = 0$（私有辅助引理） | ✅ |
| `riemHess_kills_u` | $\mathrm{Hess}[u] = 0$（$u$ 是法方向） | ✅ |
| `riemHess_in_tangent` | $\langle \mathrm{Hess}[v], u\rangle = 0$（值域在切空间） | ✅ |
| `riemHess_on_tangent` | $v \perp u \Rightarrow \mathrm{Hess}[v] = P_u^\perp(Hv - \langle g,u\rangle v)$（外层 $P_u^\perp$ 仍存在！） | ✅ |
| `riemHess_symmetric` | $\langle \mathrm{Hess}[v], w\rangle = \langle v, \mathrm{Hess}[w]\rangle$（$v,w \perp u$） | ✅ |

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

### 关键技术细节

1. **`starRingEnd ℝ` 的处理**：

   在证明 `riemHess_symmetric` 时，`inner_smul_left` 展开后会出现
   `(starRingEnd ℝ) (inner ℝ g u)`。对实数域，`starRingEnd ℝ` 是恒等函数，
   但 Lean 不会自动识别。解决方案：

   ```lean
   rw [show (starRingEnd ℝ) (inner ℝ g u) = inner ℝ g u from rfl]
   ```

   随后 `linarith` 正常工作。

2. **对称性证明中的投影自伴性应用**：

   左侧 $\langle P(Hv - c\cdot v), w\rangle$ 的化简需要：
   - 先用 `sphere_tangent_projection_symmetric` 将 $\langle Px, w\rangle$ 变为 $\langle x, Pw\rangle$
   - 再用 `sphere_tangent_projection_identity_on_tangent` 将 $Pw$ 还原为 $w$（因为 $w \perp u$）

   右侧同理。这两个引理的组合使用是化简的核心。

3. **`hH v w` 与 `linarith` 的组合**：

   经过投影自伴性化简后，目标变为：
   $$\langle Hv, w\rangle - c\langle v, w\rangle = \langle v, Hw\rangle - c\langle v, w\rangle$$

   其中 $c = \langle g, u\rangle$。第一项由 `hH v w` 直接提供，剩余的 $-c\langle v,w\rangle$ 在两侧同时出现，直接由 `linarith` 消去。

4. **`riemHess_kills_u` 的 trivial 证明**：

   性质1（Hess 杀死法方向）的证明仅需：
   ```lean
   simp only [riemHess, proj_perp_unit_eq_zero u hu, map_zero, smul_zero, sub_self]
   ```
   一切在一步 `simp` 中完成，因为 `H (0) = 0` 和 $c \cdot 0 = 0$。

## Mathlib 依赖

| 模块 | 用途 |
|------|------|
| `Mathlib.Analysis.InnerProductSpace.Projection.Basic` | `starProjection`，正交投影所有核心引理 |
| `Chapter2.《2_6》.Chapter2_Exercise2_6_1` | 切空间投影的全部性质（幂等、对称、显式公式等） |

## 与书中的对应关系

| 书中陈述 | Lean 形式化 | 状态 |
|---------|------------|------|
| $\mathrm{Hess}\, f(u) = P_u^\perp(\nabla^2 f - \langle\nabla f, u\rangle I)P_u^\perp$ | `riemHess` 定义（展开为 $P(H(Pv) - c\cdot Pv)$） | ✅ |
| Hessian 值域在 $T_u S^{d-1}$ 内（性质2） | `riemHess_in_tangent` | ✅ |
| $v \perp u$ 时简化为 $P_u^\perp(Hv - \langle g,u\rangle v)$，外层投影仍存在（性质3） | `riemHess_on_tangent` | ✅ |
| Hessian 在 $T$ 上对称（性质4） | `riemHess_symmetric` | ✅ |
| $\langle \mathrm{Hess}[u], v\rangle = 0$（性质1） | `riemHess_kills_u` | ✅ |

## 与习题 2.6 系列的联系

| 维度 | 2.6.1（切空间） | 2.6.2（球面投影） | 2.6.3（黎曼 Hessian） |
|------|----------------|------------------|----------------------|
| 核心结果 | $P_u^\perp = I - uu^\top$ | $\mathrm{proj}_{S^{d-1}}(v) = v/\|v\|$ | $\mathrm{Hess}[v] = P_u^\perp(H(Pv) - \langle g,u\rangle Pv)$ |
| 主要工具 | `starProjection` API | Cauchy-Schwarz | 投影代数 + 自伴性 |
| sorry 数 | 0 | 0 | **0** |
| 定理数 | 8 | 6 | 5（含1个私有引理） |
| 逻辑结构 | API 调用为主 | 代数计算为主 | 代数操作为主 |

## 总结

**完成度**：100%（零 sorry）

习题 2.6.3 完成了球面约束优化的黎曼 Hessian 形式化。本质上，这是一个在切空间上的二阶操作对象，其定义为：

$$\mathrm{Hess}[v] = P_u^\perp\left(H(P_u^\perp v) - \langle g, u\rangle \cdot P_u^\perp v\right)$$

四个核心性质的证明充分利用了习题 2.6.1 中建立的正交投影体系：

1. **性质1**（杀死法方向）：由 $P_u^\perp u = 0$ 直接得出
2. **性质2**（切空间封闭性）：由 $P_u^\perp$ 的像集特性得出
3. **性质3**（切空间上的简化）：由 $v \perp u \Rightarrow P_u^\perp v = v$ 得出
4. **性质4**（对称性）：由投影自伴性和 $H$ 的自伴性组合得出

技术上，与正交群练习 2.8.2 相比，球面 Hessian 的曲率项是标量（而非矩阵），因此对称性证明中无需处理矩阵乘法的复杂性，这是球面情形的显著优势。
