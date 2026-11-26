# 单色模弱 Schur 数的精确公式

[English](README.en.md) · [中文论文](paper/paper-zh.pdf) · [English paper](paper/paper-en.pdf) · [复现指南](REPRODUCE.md)

从 $1,\ldots,n$ 中选取两两不同的 $x_1,\ldots,x_\ell,y$。给定正整数 $m,\ell$，多大的 $n$ 还能保证 $x_1+\cdots+x_\ell\equiv y\pmod m$ 无解？这个最大的 $n$ 记作 $\mathrm{WS}_m(1,\ell)$。本仓库给出对每一对正整数参数都成立的公式，以及直接对这一定义作出的 Lean 4 证明。

## 公式

若 $\ell=1$，答案是 $m$。若 $\ell\ge2$，记

$$
C=\frac{\ell(\ell+1)}2-1,\qquad
B=\{C-\ell+2j:0\le j\le\ell,\ j\in\mathbb Z\}.
$$

若 $B$ 中有 $m$ 的倍数，则 $\mathrm{WS}_m(1,\ell)=\ell$。否则，取 $r=C\bmod m$ 为最小非负余数，有

$$
\mathrm{WS}_m(1,\ell)=
\max\!\left\{\ell+2,\min\!\left\{r+1,\ \ell+
\left\lceil\frac{m-r}{\ell}\right\rceil\right\}\right\}-1.
$$

证明考察所有实际能出现的整数差 $x_1+\cdots+x_\ell-y$。在 $n=\ell+1$ 时，每个数都要用，选择右端 $y$ 后差值就确定，因此得到步长为 2 的集合 $B$。在 $n\ge\ell+2$ 时，差值取遍从 $C-(n-1)$ 到 $C+\ell(n-\ell)$ 的每个整数。区间向两端扩张，首次碰到 $m$ 的倍数就产生第一个同余解。

例如 $\mathrm{WS}_{23}(1,4)=7$。在 $[1,7]$ 上，可能的差是 $3,\ldots,21$。到 $[1,8]$ 时，$5+6+7+8-3=23$ 给出解。

## 证明与数据

| 材料 | 内容 |
| --- | --- |
| [中文 LaTeX](paper/paper-zh.tex) · [English LaTeX](paper/paper-en.tex) · [参考文献](paper/references.bib) | 谱的端点、无缺口的证明和阈值推导 |
| [Lean 最终定理](lean/WeakSchur.lean) · [公理审计](records/lean-audit.txt) | 原命题显式要求左端无重复、右端另选、每个数属于 $[1,n]$，并按余数相等判断同余 |
| [数值脚本](scripts/verify.py) · [运行记录](records/numerical-check.txt) | 直接枚举 212,888 个“支集与右端”组合，独立动态规划核对 8,192 组阈值 |
| [选题与研究记录](records/research.md) | 六个候选、选择理由、证据来源、AI 分工和查新边界 |

```sh
python -X utf8 -B scripts/verify.py value 23 4
```

## 文献范围与贡献

2013 年论文已求出模数 $1,2,3$ 时的结果。2025 年论文的公开摘要报告了 $\ell$ 足够大时的单色情形。本次查新未找到覆盖任意正整数 $m,\ell$ 的相同弱版本公式。我们只取得了 2025 年论文的摘要，首发归属仍待全文及更广泛文献核实。[2013 年论文](https://doi.org/10.37236/2374) · [2025 年论文](https://doi.org/10.1007/s11139-025-01123-5)

用户设定研究目标与预算。AI 完成选题、数学推导、双语写作、形式化与数值实验。主定理通过 Lean 4.19.0 内核检查，报告的依赖为 `propext`、`Classical.choice` 和 `Quot.sound`。本稿尚未经同行评审。
