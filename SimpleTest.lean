/-
  简单的 Lean 证明测试
  测试基本的定理证明功能
-/

-- 简单的自然数定理
theorem add_zero (n : Nat) : n + 0 = n := by
  rfl

-- 简单的等式推理
theorem add_comm_test (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

-- 简单的逻辑推理
theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  exact hpq hp

-- 简单的列表定理
theorem list_length_append (α : Type) (xs ys : List α) :
  (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    simp [ih]
    omega

#check add_zero
#check add_comm_test
#check modus_ponens
#check list_length_append
