# DRL Formalization

《深度表征学习》（Deep Representation Learning）一书的 Lean 4 形式化证明项目。

## 项目简介

用形式化数学语言验证书中的主要定理和算法的正确性。

## 当前进展

### 第2章：线性与独立结构

| 练习 | 状态 |
|------|------|
| 2.1 PCA 最优性（Ky Fan 最大值原理） | ✅ 完成 |
| 2.2 - 2.4 | 📋 待开始 |

### 第3-5章

计划中

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
