# Holomorphic curves with few inflection points — Lean 4

本目录是把论文 **Holomorphic curves of finite lower order with few
inflection points** 放进 Lean 4 的形式化项目。工具链固定为
`leanprover/lean4:v4.34.0-rc1`，依赖 mathlib 的同一版本。

在 PowerShell 中运行：

```powershell
Set-Location 'E:\Lean 4\FewInflection'
lake build
```

目前 `lake build` 已成功通过。

## 已形式化的内容

`FewInflection/Definitions.lean` 定义了：

* 有限维整曲线、约化表示、线性非退化和带整因子的多项式表示；
* Wronskian（由 `iteratedDeriv` 和矩阵行列式定义）；
* 在局部可微条件下，某点 Wronskian 非零推出坐标函数线性无关；
* 论文中的齐次向量 Cartan–Nevanlinna characteristic（圆周平均
  `log ‖f‖` 减去原点归一项）、Wronskian 的 counting function、阶和下阶；
* 小分歧、慢变和正则变差；
* 单项式曲线的 Wronskian 计算
  \(W(1,z,\ldots,z^n)=\prod_{j=0}^n j!\)；
* 单项式曲线的线性无关性、非零 Wronskian 和带可微无零因子的
  polynomial/rational-normal 表示；
* 用一个显式的对角可逆矩阵把该 Wronskian 归一化为恒等于 `1`，并证明
  归一化曲线仍线性非退化且有零 ramification；
* 常数标量和常数矩阵 gauge 变换下的 Wronskian 恒等式；
* 常数矩阵可逆时上述 Wronskian 仍非零；
* 单项式曲线的 ramification 恒等于零，因此其 `SmallRamification` 由
  mathlib 的 `isLittleO_zero` 直接推出；
* `rpow` 的正则变差、常数函数的慢变性、正则变差指数的唯一性，以及
  growth ratio 的最终非负性；在正值连续性假设下，正则变差除以
  `r^ρ` 得到慢变因子，并得到论文所写的最终等式
  `T(r)=r^ρ*ℓ(r)`。

阶和下阶现在取值于 `EReal`，因此“有限下阶”表示下阶严格小于
`+∞`；主命题还显式要求同一个 `ρ` 等于阶和下阶，避免只写
`order = lowerOrder` 却没有说明其共同值的形式漏洞。

论文的约定 `n ≥ 1` 也写进了五个目标命题。`SlowlyVarying` 使用正值、
正半轴连续和 `[1,2]` 上一致的 ε–R 定义；`RegularlyVarying` 使用任意
紧正比例集上的局部一致 ε–R 定义。

`FewInflection/Results.lean` 给出论文中主定理、sharpness、阶小于 1 的
rational-normal 结论、零阶分歧估计和径向面积推论的 Lean 类型化命题，
并证明了从 `MainConclusion` 或具体 witness 抽取结论的纯逻辑引理；还
用 mathlib 的 filter 极限运算证明了“正则变差 + 面积/特征函数趋于
`ρ` ⇒ 面积比趋于 `c^ρ`”这一径向推论。

## 解析证明边界

论文的主证明依赖完整的 Nevanlinna 理论、Pólya peaks、势论极限、
Karp–Purbhoo 的 universal Plücker 坐标和线性常微分方程渐近积分；这些
理论目前不在 mathlib 中。因此本项目没有把它们伪装成公理：当前工程是
“定义 + 已检查的代数/微积分引理 + 无公理的目标命题”。目标命题本身
仍需要把上述缺失理论逐层加入 mathlib 后才能证明。

为使 `logGrowthRatio` 对当前定义的任意曲线都良定义，形式化使用
`log (max (characteristic f r) 1)`；这是在完整次调和增长理论尚未形式化
时的显式正则化，不是额外的解析公理。

这一区分可用下面的命令审计：

```powershell
lake env lean verification/Audit.lean
```

审计文件会检查这些已证明引理依赖的基础公理，并检查五个目标命题的类型；
工程中没有自定义 `axiom` 或 `sorry`。

原始论文源码保存在 `paper/original.tex`。
