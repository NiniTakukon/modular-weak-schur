"""一色模弱 Schur 数的闭式计算、整数谱枚举与独立阈值复核。"""

from __future__ import annotations

import argparse
import sys
from itertools import combinations


def weak_schur(m: int, ell: int) -> int:
    """返回 [1,n] 中尚无互异模解时的最大 n。"""
    if m < 1 or ell < 1:
        raise ValueError("m 和 l 必须为正整数")
    if ell == 1:
        return m

    c = ell * (ell + 1) // 2 - 1
    low, high = c - ell, c + ell
    first_multiple = low + (-low) % m
    # 两个相邻倍数涵盖所有可能的倍数奇偶性。
    for multiple in (first_multiple, first_multiple + m):
        if multiple <= high and (multiple - low) % 2 == 0:
            return ell

    r = c % m
    steps_up = (m - r + ell - 1) // ell
    first_failure = max(ell + 2, min(r + 1, ell + steps_up))
    return first_failure - 1


def signed_supports(n: int, ell: int):
    """枚举 (左端和减右端, 无序支集, 右端)，每个支集有 l+1 种右端。"""
    for support in combinations(range(1, n + 1), ell + 1):
        total = sum(support)
        for rhs in support:
            yield total - 2 * rhs, support, rhs


def expected_spectrum(n: int, ell: int) -> set[int]:
    if n <= ell:
        return set()
    if ell == 1:
        return set(range(1 - n, 0)).union(range(1, n))
    c = ell * (ell + 1) // 2 - 1
    if n == ell + 1:
        return set(range(c - ell, c + ell + 1, 2))
    low = ell * (ell + 1) // 2 - n
    high = ell * (2 * n - ell + 1) // 2 - 1
    return set(range(low, high + 1))


def check_spectra(max_n: int) -> None:
    cases = assignments = 0
    for n in range(1, max_n + 1):
        for ell in range(1, max_n + 1):
            actual = set()
            for difference, _, _ in signed_supports(n, ell):
                actual.add(difference)
                assignments += 1
            expected = expected_spectrum(n, ell)
            if actual != expected:
                raise AssertionError(
                    f"整数谱不符 n={n}, l={ell}, "
                    f"枚举缺少 {sorted(expected - actual)}, "
                    f"枚举多出 {sorted(actual - expected)}"
                )
            cases += 1
    print(f"整数谱通过 {cases} 组 (n,l)，n,l=1..{max_n}，"
          f"共枚举 {assignments} 个（支集，右端）组合")


def first_failures_dp(m: int, max_l: int) -> list[int]:
    """返回 l=1..max_l 各自首次出现互异模解的 n。"""
    mask = (1 << m) - 1

    def rotate(bits: int, shift: int) -> int:
        # 第 j 位表示剩余类 j，循环左移对应模 m 加法。
        return ((bits << shift) & mask) | (bits >> (m - shift))

    # 下标是已选整数总数。positive 全取正号，one_rhs 恰有一个负号。
    positive = [1] + [0] * (max_l + 1)
    one_rhs = [0] * (max_l + 2)
    first = [0] * (max_l + 1)
    remaining = max_l
    # m, 2m, ..., (max_l+1)m 给出独立于闭式的搜索上界。
    for n in range(1, (max_l + 1) * m + 1):
        plus, minus = n % m, (-n) % m
        for size in range(min(n, max_l + 1), 0, -1):
            # 保留旧位即跳过 n。倒序更新使正号与负号分支均只使用一次 n。
            smaller = positive[size - 1]
            one_rhs[size] |= rotate(one_rhs[size - 1], plus) | rotate(smaller, minus)
            positive[size] |= rotate(smaller, plus)
            ell = size - 1
            if ell >= 1 and first[ell] == 0 and one_rhs[size] & 1:
                first[ell] = n
                remaining -= 1
        if remaining == 0:
            return first[1:]
    raise AssertionError(f"DP 搜索达到上界，m={m}，仍有 {remaining} 个阈值未找到")


def check_thresholds(max_m: int, max_l: int) -> None:
    cases = 0
    for m in range(1, max_m + 1):
        for ell, actual in enumerate(first_failures_dp(m, max_l), start=1):
            predicted = weak_schur(m, ell) + 1
            if actual != predicted:
                raise AssertionError(
                    f"首次失败位置不符 m={m}, l={ell}, DP={actual}, 闭式={predicted}"
                )
            cases += 1
    print(f"阈值通过 {cases} 组 (m,l)，m=1..{max_m}，l=1..{max_l}")


def show_example() -> None:
    m, ell = 6, 4
    w = weak_schur(m, ell)
    spectrum = sorted({d for d, _, _ in signed_supports(w, ell)})
    values = ", ".join(map(str, spectrum))
    hits = sum(d % m == 0 for d in spectrum)
    print(f"示例 W({m}, {ell})={w}，首次失败位置 n={w + 1}")
    print(f"  n={w} 的整数谱为 {{{values}}}，其中有 {hits} 个 {m} 的倍数")
    for difference, support, rhs in signed_supports(w + 1, ell):
        if difference % m == 0:
            lhs = " + ".join(str(x) for x in support if x != rhs)
            print(f"  n={w + 1} 时 {lhs} - {rhs} = {difference} = {difference // m} * {m}")
            return
    raise AssertionError("示例中未找到模解")


def positive_int(text: str) -> int:
    value = int(text)
    if value < 1:
        raise argparse.ArgumentTypeError("请输入正整数")
    return value


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, epilog="不带参数运行默认复核。")
    commands = parser.add_subparsers(dest="command", required=True)
    check = commands.add_parser("check", help="枚举整数谱并用 DP 复核阈值",
                                formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    check.add_argument("--max-n", type=positive_int, default=14, help="整数谱枚举的 n 和 l 上限")
    check.add_argument("--max-m", type=positive_int, default=256, help="阈值复核的 m 上限")
    check.add_argument("--max-l", type=positive_int, default=32, help="阈值复核的 l 上限")
    value = commands.add_parser("value", help="计算给定 m,l 的 W 和首次失败位置")
    value.add_argument("m", type=positive_int)
    value.add_argument("ell", metavar="l", type=positive_int)
    args = parser.parse_args(sys.argv[1:] or ["check"])

    if args.command == "value":
        w = weak_schur(args.m, args.ell)
        print(f"W({args.m}, {args.ell})={w}，首次失败位置 n={w + 1}")
    else:
        check_spectra(args.max_n)
        check_thresholds(args.max_m, args.max_l)
        show_example()


if __name__ == "__main__":
    main()
