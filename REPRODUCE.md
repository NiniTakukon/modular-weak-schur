# 复现指南 / Reproduction guide

以下命令从仓库根目录开始。The three command blocks are independent and each starts at the repository root.

## 1. 数值复核 / Numerical checks

用 Python 3.12.2 实测，脚本只导入标准库。The default run enumerates actual supports and right-hand sides, then computes first failures independently using residues.

```sh
python -X utf8 -B scripts/verify.py
python -X utf8 -B scripts/verify.py value 23 4
```

默认应得到 196 个整数谱、212,888 个支集与右端组合，以及 8,192 个阈值全部通过。单例查询应得到 $W(23,4)=7$、首次失败位置 $8$。扩大或缩小范围可用 `check --max-n 14 --max-m 256 --max-l 32`。原始输出保存在[数值记录](records/numerical-check.txt)。

For each prefix, the dynamic program stores attainable residues by the number of selected positions and by whether a right-hand side has been selected. It processes positions once and updates sizes in descending order. Its stopping bound follows by selecting distinct multiples of the modulus. The direct support enumeration checks each attainable integer before reduction modulo $m$.

## 2. Lean 4 内核验证 / Kernel verification

用 Lean 4.19.0 和随附的 Lake 构建。可用 Elan 读取工程的 `lean-toolchain`，也可将官方二进制包的 `bin` 目录加入当前终端的 `PATH`。该工程只使用 Lean 自带的 `Std`。[Lean 4.19.0 官方发布](https://github.com/leanprover/lean4/releases/tag/v4.19.0)

```sh
cd lean
lean --version
lake build
lake env lean Audit.lean
```

The last command prints the definitions of the original modular witness and the computed threshold, the statements of the final theorems, and ten transitive axiom reports. It also checks three concrete evaluations. The main theorem reports `[propext, Classical.choice, Quot.sound]`. An actual build from a source-only copy and its audit are recorded in the [Lean transcript](records/lean-audit.txt).

| 模块 / Module | 数学内容 / Mathematical role |
| --- | --- |
| [Model](lean/WeakSchur/Model.lean) | 逐个处理整数位置，每个位置参与至多一次。定义三角数并证明其闭式。 |
| [Witness](lean/WeakSchur/Witness.lean) | Both directions between the recurrence and an arbitrary duplicate-free list with a distinct right-hand side. |
| [Spectrum](lean/WeakSchur/Spectrum.lean) | 整数谱的空集、步长二、完整区间和 $\ell=1$ 四种情形。 |
| [Threshold](lean/WeakSchur/Threshold.lean) | The neighbouring multiples of $m$, the first failure and the last safe index. |
| [WeakSchur](lean/WeakSchur.lean) | 以 `xs.sum % m = y % m` 表达原始命题，证明公式值无解且为最大值。 |

## 3. 双语论文 / Rebuild the PDFs

两份论文使用相同的公式宏和 BibTeX 数据。实测编译器为 Tectonic 0.17.0，使用官方 `tlextras-2022.0r0` 资源包。首次编译需要访问该资源包。The Chinese source uses `xeCJK` and the bundle's `gbsn00lp.ttf` font. [Tectonic](https://tectonic-typesetting.github.io/) · [Official bundle](https://data1b.fullyjustified.net/tlextras-2022.0r0.tar)

```sh
cd paper
tectonic -X compile --bundle https://data1b.fullyjustified.net/tlextras-2022.0r0.tar paper-en.tex
tectonic -X compile --bundle https://data1b.fullyjustified.net/tlextras-2022.0r0.tar paper-zh.tex
```

Tectonic runs TeX, BibTeX and the PDF backend. Its default output location is beside the input source. The committed PDFs can also be read directly. [English](paper/paper-en.pdf) · [中文](paper/paper-zh.pdf)

若需保存资源以供离线编译，可从 `paper` 目录先联网运行第一行。脚本从同一官方归档按范围下载本稿使用的文件，用仓库中的 SHA-256 清单逐一校验。后两行使用本地资源包。The bundle builder uses the Python standard library. [Builder](paper/rebuild-bundle.py) · [Resource manifest](paper/tex-bundle.sha256)

```sh
python rebuild-bundle.py
tectonic -X compile --only-cached --bundle .tectonic/tlextras-2022.0r0-paper.zip paper-en.tex
tectonic -X compile --only-cached --bundle .tectonic/tlextras-2022.0r0-paper.zip paper-zh.tex
```

The verified resource bundle contains 327 pinned files. The rebuilt ZIP has 20,504,169 bytes and SHA-256 `343e70556e28524d9a4d4b5e40d5db671361988ee941413dfc803eb9c62c1324`.
