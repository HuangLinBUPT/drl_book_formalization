# DRL Formalization

《深度表征学习》（Deep Representation Learning）一书的 Lean 4 形式化证明项目。

## 项目简介

这是一个业余项目，用形式化数学语言验证书中的习题，以了解当前的Lean语言和MathLib引理库，对书中的数学知识能支持到什么程度。

## 当前进展

**更新时间**: 2026-04-02

### 第2章：线性与独立结构

| 练习 | 内容 | 状态 | 备注 |
|------|------|------|------|
| 2.1 | PCA 最优性（Ky Fan 最大值原理） | ✅ 完成 | 0 sorries |
| 2.2 | 高斯分布的旋转不变性 | 🔄 接近完成 | 2 sorries 待解决 |
| 2.3.1 | GL(d) 对称性 | ✅ 完成 | 0 sorries |
| 2.3.2 | ICA 对称性约简（对角分解） | 🔄 接近完成 | 1 sorry 待解决 |
| 2.4.1 | Whitening：秩界限定理 | 🔄 接近完成 | 1 sorry 待解决 |
| 2.4.2 | Whitening：白化矩阵性质 | 🔄 接近完成 | 1 sorry 待解决 |
| 2.4.3 | Whitening：SVD 与正交恢复 | 🔄 接近完成 | 2 sorries 待解决 |

**总体进展**: 7 个练习，2 个完全完成，5 个接近完成（共 7 个 sorries 待解决）

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

# 验证文件
lake env lean Chapter2/2_1/Chapter2_Exercise2_1.lean
```

## 相关资料

- [《深度表征学习》原书](https://github.com/Ma-Lab-Berkeley/deep-representation-learning-book)
- [Lean 4 文档](https://lean-lang.org/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)
