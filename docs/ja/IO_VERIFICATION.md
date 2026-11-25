# IO・副作用を含むプログラムの形式検証

純粋関数に対する証明は書きやすい一方、実務のアプリケーションはユーザー入力の読み取り、出力ストリームへの書き出し、状態更新、外部サービスとの通信といった副作用を伴います。Proof Samurai は、**カーネルに公理を 1 つも追加せず**に実用的な IO プログラムを検証できるよう、**Free モナド（エフェクト木）＋決定論的トレース意味論＋合成可能なホーア論理**の構成を採用しています。

## なぜ不透明な `RealWorld` 公理ではなく Free モナド（エフェクト木）なのか

多くの処理系では `axiom IO : Type => Type` のように IO を不透明なプリミティブとして定義します。しかし不透明な型は証明の中から構造を分解できないため、`bind`・入力・出力の挙動について未検証の公理を追加せざるを得ず、公理のわずかな記述ミスが体系全体の不健全性につながります。

Proof Samurai の `stdlib/IO.samurai` はこれとは逆のアプローチを取ります。

1. **プログラムをデータとして表現する（`IO[Result]` / `Eff[Req, Resp, Result]`）**: 副作用付きプログラムを、エフェクト命令と継続（continuation）からなる帰納的構文木（`Pure`, `PrintNat`, `ReadNat`, `GetState`, `PutState`、および汎用 `Eff.Call`）として定義します。
2. **高階構造帰納法により公理 0 個で法則を証明する**: `IO` は厳格に正な高階帰納型（`ReadNat(cont: Nat => IO[Result])` 等）であり、`induction` タクティクが継続に対して全称量化された帰納法の仮定（`ih : forall (n: Nat) => P(cont(n))`）を自動生成します。これにより `runIOBind`、モナド則 3 種（`ioLeftId`, `ioRightId`, `ioAssoc`）、ホーア論理の合成則をすべて公理 0 個でカーネル検証できます。
3. **決定論的トレース意味論（`runIO`）の上で仕様を証明する**: Proof Samurai 内部では、任意の入力列と初期状態に対する `runIO(prog, inputs, initState)` の入出力トレース仕様やホーア不変条件（`HoareIO`）を証明します。
4. **抽出コードに薄い実ランタイム解釈器を接続して動かす**: Scala 3 / TypeScript / JavaScript / Haskell / OCaml へコード抽出すると、`Prop`・`HoareIO`・定理はすべて 0 バイトに消去され、純粋な `IO` 木だけが残ります。あとはターゲット言語側で 15 行程度の解釈器を 1 つ書けば、実際の標準入出力・可変ストア・ネットワーク・DB と接続して実行できます。

---

## 標準ライブラリ: `stdlib/IO.samurai`

### 基本データ型

```scala
enum IO[Result: Type]: Type {
  case Pure(value: Result)
  case PrintNat(value: Nat, next: IO[Result])
  case ReadNat(cont: Nat => IO[Result])
  case GetState(cont: Nat => IO[Result])
  case PutState(newState: Nat, next: IO[Result])
}

case class IOResult[Result](
  value: Result,
  remainingInputs: List[Nat],
  outputs: List[Nat],
  finalState: Nat
)
```

コンソールや単一状態以外のドメイン固有エフェクト（KV ストア、HTTP リクエスト、ファイル操作、DB クエリ等）向けには、汎用代数的エフェクト木 `Eff` も用意しています。

```scala
enum Eff[Req: Type, Resp: Type, Result: Type]: Type {
  case Done(value: Result)
  case Call(request: Req, cont: Resp => Eff[Req, Resp, Result])
}
```

### モナディックな `do { ... }` 構文

カーネルを変更せずに読みやすい手続き風 IO コードを書けるよう、軽量な `do { ... }` 構文をサポートしています（`do` は文脈依存のため、`do { ... }` 以外では通常の識別子としても使えます）。

```scala
def readAndPrintSum: IO[Nat] = {
  do {
    val first <- readNat
    val second <- readNat
    val total = first + second
    printNat(total)
    pure[Nat](total)
  }
}
```

`do { ... }` ブロック内で使える文は以下の通りです。
- `val x <- action` — モナディック束縛（`bind(action, x => rest)` へ脱糖）
- `val x = expr` — 純粋なローカル束縛（`{ val x = expr; rest }`）
- `action` — 戻り値を使わない副作用の逐次実行（`bind(action, _ => rest)`）
- 末尾の式 — ブロック全体の戻り値となる `IO[A]` アクション

注意: `if (...) { ... } else { ... }` の分岐内で複数ステップの IO アクションを並べる場合は、通常の純粋ブロックとして途中アクションが捨てられないよう、各分岐の中も `do { ... }` で囲んでください。

### 組み込みの検証済み定理（`stdlib/IO.samurai`、公理 0 個）

| 定理・定義 | 内容 |
|---|---|
| `runIOBind` | `runIO(bind(act, cont), inputs, st)` が、`act` を先に実行して得られた `value`・`remainingInputs`・`finalState` を `cont` に渡し、出力ログを連結（`r1.outputs ++ r2.outputs`）した結果と一致すること。 |
| `IOEquiv(p, q)` | 観測同値性: `forall inputs, initState => runIO(p, inputs, initState) === runIO(q, inputs, initState)`。 |
| `ioLeftId`, `ioRightId`, `ioAssoc` | `IOEquiv` に関するモナド則 3 種すべて。 |
| `runIOPrintList` | `printList(xs)` が入力と状態を変えずに `xs` をそのまま出力すること。 |
| `runIOReadN` | `items ++ rest` に対する `readN(length(items))` が `items` を消費して返し、`rest` を残すこと。 |
| `HoareIO(Pre, prog, Post)` | 入力ストリーム・出力ログ・戻り値・状態に対する合成可能なホーア三つ組。 |
| `hoarePure`, `hoarePrintNat`, `hoareGetState`, `hoarePutState`, `hoareConseq`, `hoareBind` | モジュール的に IO 仕様を組み立てるための健全なホーア論理コンビネータ。 |

---

## 実践例（`examples/VerifiedIO.samurai`）

### 1. 状態付き IO における残高保存則と上限不変条件

`withdrawSafe` は残高を確認してから出金し、成功時に `1`、拒否時に `0` を出力します。

```scala
def withdrawSafe(amount: Nat): IO[Bool] = {
  do {
    val balance <- getState
    if (amount <= balance) {
      do {
        putState(balance - amount)
        printNat(1)
        pure[Bool](true)
      }
    } else {
      do {
        printNat(0)
        pure[Bool](false)
      }
    }
  }
}
```

これに対して、成功時の厳密な残高保存（`finalState + amount === initBalance`）と出力 `1`、および残高不足時の状態非変更と出力 `0` を証明しています。

```scala
theorem withdrawSafeSuccessSpec(
  amount: Nat,
  inputs: List[Nat],
  initBalance: Nat,
  hEnough: ble(amount, initBalance) === true
):
  (runIO[Bool](withdrawSafe(amount), inputs, initBalance).value === true) /\
  (runIO[Bool](withdrawSafe(amount), inputs, initBalance).outputs === [1]) /\
  (runIO[Bool](withdrawSafe(amount), inputs, initBalance).finalState + amount === initBalance) = by {
  ...
}
```

また、入力ストリームから入金額を読み取る `depositWithCap(cap)` では、`HoareIO`・`by_cases`・`omega` を使い、「初期残高が `cap` 以下ならば、**どんな入力ストリームが来ても**（空入力を含む）終了時残高が `cap` 以下に保たれる」安全性不変条件を証明しています。

```scala
theorem depositWithCapPreservesInvariant(cap: Nat):
  HoareIO[Bool](
    (inputs: List[Nat], bal: Nat) => Le(bal, cap),
    depositWithCap(cap),
    (ok: Bool, rem: List[Nat], out: List[Nat], finalBal: Nat) => Le(finalBal, cap)
  ) = by {
  unfold(HoareIO)
  intros(inputs, initBal, hInv)
  cases(inputs) {
    case Nil => {
      unfold(depositWithCap); simp
      by_cases(ble(initBal, cap), cmp) <;> { simp; omega }
    }
    case Cons(amt, rest) => {
      unfold(depositWithCap); simp
      by_cases(ble(initBal + amt, cap), cmp) <;> { simp; omega }
    }
  }
}
```

### 2. IO パイプライン全体のエンドツーエンド検証（入力 -> ソート -> 出力）

`stdlib/IO.samurai` と `stdlib/Sorting.samurai` を組み合わせ、`readSortAndPrint(count)` は入力ストリームから `count` 個の数値を読み取り、`insertionSort` で整列した結果を出力ストリームに書き出します。

```scala
def readSortAndPrint(count: Nat): IO[List[Nat]] = {
  do {
    val items <- readN(count)
    val sorted = insertionSort(items)
    printList(sorted)
    pure[List[Nat]](sorted)
  }
}
```

定理 `readSortAndPrintOutputIsVerified` は、任意の入力リスト `items`・後続入力 `rest`・初期状態 `initState` に対して、**実際に出力ストリームへ書き出された列 `outputs`** が `IsSortedPermutation(items, outputs)`（昇順かつ要素多重集合の保存）を満たすことを公理 0 個で証明しています。

---

## 抽出したコードを実ランタイムへ接続する

`examples/VerifiedIO.samurai` は 5 つのターゲットすべてへ抽出できます。

```bash
sbt "run extract examples/VerifiedIO.samurai --target scala3 --module ExtractedVerifiedIO --strict --total"
sbt "run extract examples/VerifiedIO.samurai --target ts --module ExtractedVerifiedIO --strict --total"
sbt "run extract examples/VerifiedIO.samurai --target haskell --module VerifiedIO --strict --total"
sbt "run extract examples/VerifiedIO.samurai --target ocaml --module verified_io --strict --total"
```

`HoareIO`・`IOEquiv`・`Sorted`・`Le` および全定理は完全に消去されます。各ターゲット言語での実ランタイム解釈器は次の通りです。

### Scala 3 ランタイム解釈器

```scala
import ExtractedVerifiedIO.*

def runRealIO[A](
  prog: IO[A],
  readInt: () => Int,
  printInt: Int => Unit,
  getStore: () => Int,
  putStore: Int => Unit
): A = {
  var cur: IO[A] = prog
  while (true) {
    cur match {
      case IO.Pure(v) => return v
      case IO.PrintNat(v, next) =>
        printInt(fromNat(v))
        cur = next
      case IO.ReadNat(k) =>
        cur = k(toNat(readInt()))
      case IO.GetState(k) =>
        cur = k(toNat(getStore()))
      case IO.PutState(s, next) =>
        putStore(fromNat(s))
        cur = next
    }
  }
  throw new AssertionError("unreachable")
}
```

（`ExtractionSuite` の自動テストでは、抽出した Scala 3 コードとこの解釈器を `dotc` でコンパイルし、実際に JVM 上で実行して副作用の結果を検証しています。）

### TypeScript / JavaScript ランタイム解釈器

```ts
export function runRealIO<A>(
  prog: IO<A>,
  readInt: () => number,
  printInt: (n: number) => void,
  getStore: () => number,
  putStore: (s: number) => void
): A {
  let cur: IO<A> = prog;
  while (true) {
    switch (cur.tag) {
      case "Pure":     return cur.value;
      case "PrintNat": printInt(fromNat(cur.value)); cur = cur.next; break;
      case "ReadNat":  cur = cur.cont(toNat(readInt())); break;
      case "GetState": cur = cur.cont(toNat(getStore())); break;
      case "PutState": putStore(fromNat(cur.newState)); cur = cur.next; break;
    }
  }
}
```

### Haskell ランタイム解釈器（`P.IO`）

```haskell
import Data.IORef (IORef, readIORef, writeIORef)
import qualified Prelude as P
import VerifiedIO

runRealIO :: IORef P.Int -> IO a -> P.IO a
runRealIO stateRef prog = case prog of
  IO_Pure v          -> P.pure v
  IO_PrintNat v next -> P.print (fromNat v) P.>> runRealIO stateRef next
  IO_ReadNat k       -> P.readLn P.>>= \n -> runRealIO stateRef (k (toNat n))
  IO_GetState k      -> readIORef stateRef P.>>= \s -> runRealIO stateRef (k (toNat s))
  IO_PutState s next -> writeIORef stateRef (fromNat s) P.>> runRealIO stateRef next
```

### OCaml ランタイム解釈器

```ocaml
let rec run_real_io (state_ref : int ref) (prog : 'a Verified_io.iO) : 'a =
  match prog with
  | IO_Pure v -> v
  | IO_PrintNat (v, next) ->
      Printf.printf "%d\n%!" (from_nat v);
      run_real_io state_ref next
  | IO_ReadNat k ->
      let n = try int_of_string (read_line ()) with _ -> 0 in
      run_real_io state_ref (k (to_nat n))
  | IO_GetState k ->
      run_real_io state_ref (k (to_nat !state_ref))
  | IO_PutState (s, next) ->
      state_ref := from_nat s;
      run_real_io state_ref next
```

---

## 検証コマンド

```bash
sbt "run check stdlib/IO.samurai --strict"
sbt "run check examples/VerifiedIO.samurai --strict"
```
