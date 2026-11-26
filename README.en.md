# An exact formula for the one-colour modular weak Schur number

[中文](README.md) · [English paper](paper/paper-en.pdf) · [中文论文](paper/paper-zh.pdf) · [Reproduction guide](REPRODUCE.md)

Given positive integers $m$ and $\ell$, how far can the initial interval $[1,n]$ grow before it contains pairwise distinct integers $x_1,\ldots,x_\ell,y$ with $x_1+\cdots+x_\ell\equiv y\pmod m$? The largest solution-free $n$ is $\mathrm{WS}_m(1,\ell)$. This repository gives a formula for all positive parameters and a Lean 4 proof of its maximality for the original congruence.

## Formula

For $\ell=1$ the answer is $m$. For $\ell\ge2$ write

$$
C=\frac{\ell(\ell+1)}2-1,\qquad
B=\{C-\ell+2j:0\le j\le\ell,\ j\in\mathbb Z\}.
$$

If $B$ contains a multiple of $m$, then $\mathrm{WS}_m(1,\ell)=\ell$. Otherwise, writing $r=C\bmod m$ for the least nonnegative residue gives

$$
\mathrm{WS}_m(1,\ell)=
\max\!\left\{\ell+2,\min\!\left\{r+1,\ \ell+
\left\lceil\frac{m-r}{\ell}\right\rceil\right\}\right\}-1.
$$

The proof determines the integers attained by $x_1+\cdots+x_\ell-y$. At $n=\ell+1$, choosing $y$ fixes all the summands. This gives the step-two progression $B$. At $n\ge\ell+2$ the attained values fill the entire integer interval from $C-(n-1)$ to $C+\ell(n-\ell)$. Its first encounter with a multiple of $m$ yields the threshold.

For example, $\mathrm{WS}_{23}(1,4)=7$. On $[1,7]$ the possible differences run from 3 to 21. On $[1,8]$ the choice $5+6+7+8-3=23$ gives a modular solution.

## Proofs and reproducibility

| Material | Contents |
| --- | --- |
| [English LaTeX](paper/paper-en.tex) · [Chinese LaTeX](paper/paper-zh.tex) · [bibliography](paper/references.bib) | Extremal differences, the proof of interval coverage and the threshold calculation |
| [Lean theorems](lean/WeakSchur.lean) · [axiom audit](records/lean-audit.txt) | The public statement uses distinct summands, a separate right-hand side, membership in $[1,n]$, and equality of residues |
| [Python verifier](scripts/verify.py) · [run output](records/numerical-check.txt) | Direct enumeration of 212,888 support/right-hand-side pairs and an independent dynamic program for 8,192 thresholds |
| [Research record](records/research.md) | Six candidates, the selection, division of work, sources and scope of the priority search |

```sh
python -X utf8 -B scripts/verify.py value 23 4
```

## Literature and authorship

The 2013 paper covers the moduli $1,2,3$. The public abstract of the 2025 paper reports an exact one-colour result for sufficiently large $\ell$. Our search found no matching weak formula for all positive $m,\ell$. We could consult only the abstract of the 2025 paper. Priority remains unverified. [2013 paper](https://doi.org/10.37236/2374) · [2025 paper](https://doi.org/10.1007/s11139-025-01123-5)

The user set the objective and budget. AI carried out the selection, derivation, writing, implementation and numerical checks. Lean 4.19.0 checked the main theorem with the reported dependencies `propext`, `Classical.choice` and `Quot.sound`. The manuscript has not undergone peer review.
