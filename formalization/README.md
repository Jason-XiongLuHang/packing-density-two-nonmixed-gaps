# Theorem 2 的 Lean 形式化

Lean 4.19.0；mathlib 固定在 c44e0c8ee63ca166450922a373c7409c5d26b00b（v4.19.0）。

`TwoGap.two_window_staircase` 对任意整数子集 S 证明存在整数 h，使 B ≤ b+kh 且 C ≤ a−mh。
`TwoGap.two_window_ceiling` 给出正文的 C ≤ a−m ceil((B−b)/k)。
变量名 S 在 Lean 中代表正文的避差集 A；`Box` 是正文的禁距集合 M；`SetAvoid` 明确要求任意不同选点的差均不在 Box。
`window S n` 是 S∩[0,n)；`ceilDiv z k = -((-z)/k)`，正分母时的上取整性质由 `ceilDiv_le_iff` 证明。

证明包含普通提升、边界例外、圆周排序、所有提升的求和及整数闭合；没有把关键提升结论作为额外假设。
高度单射性的 Lean 证明直接使用零高度的规范提升，与正文 gcd 证明的路线略有不同。
核验范围为 Theorem 2。最终密度公式、贪心覆盖的极限步骤和原论文的下界构造没有形式化。

在已安装 elan / Lean 的新目录中：

```text
lake update
lake exe cache get
lake build
lake env lean Audit.lean
```

本次实际核验使用上述固定版本的本地 mathlib 项目，运行 `lake env lean -o .lake/build/lib/lean/TwoGap.olean TwoGap.lean`，退出码 0；随后单独编译 Audit.lean。
两个最终定理的依赖均只有 `[propext, Classical.choice, Quot.sound]`，没有 `sorryAx` 或自行声明的公理。
verification.log 保留实际输出，其中少数 tactic 风格警告不影响证明内核核验。
本包只包含源文件和核验记录，不包含运行时或 mathlib 缓存。
