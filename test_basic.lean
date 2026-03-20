-- 简单的Lean语法测试（不需要Mathlib）

-- 基本定义
def myFunction (x : Nat) : Nat := x + 1

-- 简单定理
theorem add_comm (a b : Nat) : a + b = b + a := by
  omega

#check myFunction
#check add_comm

-- 测试成功
#eval myFunction 5
