# StableMatching

Lean 4 と Mathlib で、男女同数かつ選好が完全・厳密な古典的安定結婚問題を形式化するライブラリです。男性 `smp.Man` と女性 `smp.Woman` の型は、問題インスタンス `smp : SMP n` に依存します。

## 形式化の範囲

- [Basic](StableMatching/Basic) は選好、完全マッチング、ブロッキングペア、安定性を定義します。
- [Algorithm](StableMatching/Algorithm) は男性提案型の Gale–Shapley アルゴリズムを実装し、停止と出力の安定性を証明します。
- [Lattice](StableMatching/Lattice) は安定マッチング全体を有限分配束として扱います。順序 `M ≤ N` は、各男性が `M` での相手を `N` での相手と同等以上に好むことを表します。この順序の最小元は男性最適、最大元は女性最適です。
- [Rotation](StableMatching/Rotation) は回転の半順序と、安定マッチングから回転の下方閉集合への Birkhoff 表現を扱います。各男性が参加する回転の集合 `Rotation.manChain m` は鎖です。下方閉集合の差の線形拡張と合法な回転除去列の対応、および除去を逆順に取り消せることも証明しています。

## 利用例

`smp.galeShapley` は安定マッチングを返します。`M.toRotationLowerSet` と `StableMatching.ofRotationLowerSet` で、安定マッチングと回転の下方閉集合を相互に変換できます。

```lean
import StableMatching

open StableMatching
open StableMatching.SMP

example {n : ℕ} (smp : SMP n) : smp.StableMatching :=
  smp.galeShapley

example {n : ℕ} {smp : SMP n} (M : smp.StableMatching) :
    StableMatching.ofRotationLowerSet M.toRotationLowerSet = M := by
  simp
```

## ビルド

Lean 4 と Mathlib はともに v4.22.0 を使用します。バージョンは [lean-toolchain](lean-toolchain) と [lakefile.lean](lakefile.lean) に指定されています。リポジトリのルートで実行します。

```bash
bash ./build.sh
```
