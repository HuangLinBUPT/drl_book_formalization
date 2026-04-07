# DRL Formalization

## 项目简介

这是一个业余项目。计划用 Lean4 形式化《深度表征学习》（[Deep Representation Learning](https://github.com/Ma-Lab-Berkeley/deep-representation-learning-book)）
一书中的习题，并且完成证明。目的是，了解当前的 Lean 语言和 MathLib 引理库，对书中的数学知识能支持到什么程度。

主要使用了 [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) 和 [lean4-skills](https://github.com/cameronfreer/lean4-skills)，以及 Claude Code。模型使用了 Opus-4.6，glm-5，minimax-m2.7等。

## 当前进展

**更新时间**: 2026-04-07（习题 2.3.2 完成）

### 第2章：线性与独立结构

| 练习 | 内容 | 状态 | sorries |
|------|------|------|---------|
| 2.1 | PCA 最优性（Ky Fan 最大值原理） | ✅ 完成 | 0 |
| 2.2 | 高斯分布的旋转不变性 | ✅ 完成 | 0 |
| 2.3.1 | GL(d) 对称性 | ✅ 完成 | 0 |
| 2.3.2 | ICA 对称性约简（对角分解） | ✅ 完成 | 0 |
| 2.4.1 | Whitening：秩界限定理 | 🔄 接近完成 | 1 |
| 2.4.2 | Whitening：白化矩阵性质 | 🔄 接近完成 | 1 |
| 2.4.3 | Whitening：SVD 与正交恢复 | 🔄 接近完成 | 3 |
| 2.5.1 | 峰度加法性：kurt(X+Y) = kurt(X) + kurt(Y) | ✅ 完成 | 0 |
| 2.5.2 | 峰度齐次性：kurt(αX) = α⁴·kurt(X) | ✅ 完成 | 0 |
| 2.6.1 | 球面切空间与正交投影：$T_u S^{d-1} = (\mathbb{R}\cdot u)^\perp$，$P_u^\perp = I - uu^\top$ | ✅ 完成 | 0 |
| 2.6.2 | 球面最近点投影：$\operatorname{proj}_{S^{d-1}}(v) = v/\|v\|$ | ✅ 完成 | 0 |
| 2.6.3 | 黎曼 Hessian：$\operatorname{Hess}f(u) = P_u^\perp(\nabla^2 f - \langle\nabla f, u\rangle I)P_u^\perp$ | ✅ 完成 | 0 |
| 2.7.1 | 球面峰度驻点条件：$f(\mathbf{w})\mathbf{w} = \boldsymbol{\kappa}\odot\mathbf{w}^{\odot 3}$ | ✅ 完成 | 0 |
| 2.7.2 | 球面峰度临界点：$\|\mathbf{w}_S\|=1$ 且满足驻点方程 | ✅ 完成 | 0 |
| 2.7.3 | 球面峰度局部极大值：$e_j$（$\kappa_j>0$）处 Hessian 负定 | ✅ 完成 | 0 |
| 2.7.4 | 球面峰度过度紧缩景观：$\forall\kappa_i<0$ 时稠密向量为局部极大 | ✅ 完成 | 0 |
| 2.8.1 | 切空间与正交投影：$T_Q O(d)=\{Q\Omega\mid\Omega^\top=-\Omega\}$，$\mathcal{P}(\Delta)=Q\operatorname{Skew}(Q^\top\Delta)$ | ✅ 完成 | 0 |
| 2.8.2 | 黎曼 Hessian：$\mathrm{Hess}\,f(Q)=\mathcal{P}(\nabla^2 f - \mathrm{Symm}(Q^\top\nabla f)\otimes I)\mathcal{P}$ | ✅ 完成 | 0 |
| 2.8.3.1 | 投影最优性条件（Part 3.1）：$(Q^\top X)^\top=Q^\top X$ 且 $Q^\top X \succeq 0$ | ✅ 完成 | 0 |
| 2.8.3.2 | 矩阵平方根刻画（Part 3.2）：$Q^\top X = (X^\top X)^{1/2}$ | ✅ 完成 | 0 |
| 2.8.3.3 | SVD 投影结论（Part 3.3）：$UV^\top = \operatorname{proj}_{O(d)}(X)$ | ✅ 完成 | 0 |

**总体进展**: 21 个练习，18 个完全完成，3 个接近完成（共 5 个 sorries 待解决）

### 第3-5章

📋 计划中

## 安装与验证

### 环境要求

- Lean 4.28.0
- Mathlib v4.28.0

### 验证命令

```bash
# 进入项目目录
cd lean_formalization

# 获取 Mathlib 缓存
lake exe cache get

# 验证某个文件
lake env lean Chapter2/2_1/Chapter2_Exercise2_1.lean
```

## 相关资料

- [《深度表征学习》原书](https://github.com/Ma-Lab-Berkeley/deep-representation-learning-book)
- [Lean 4 文档](https://lean-lang.org/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)
