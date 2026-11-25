# Verifying Effectful & IO Programs

Pure functions are easy to prove, but real applications read user input, print output streams, update mutable state, and talk to external services. Proof Samurai supports formal verification of practical IO programs **without adding a single axiom to the kernel** by using the **Free Monad (Effect Tree) + Trace Semantics + Compositional Hoare Logic** architecture.

## Why Free Monad / Effect Trees Instead of an Opaque `RealWorld` Axiom?

Many systems model `IO` as an opaque primitive `axiom IO : Type => Type`. While simple, an opaque `IO` type cannot be inspected inside proofs, forcing you to add unchecked axioms about `bind`, `read`, or `write` — any one of which can quietly introduce unsoundness.

Proof Samurai takes the opposite approach (`stdlib/IO.samurai`):

1. **Programs are data (`IO[Result]` / `Eff[Req, Resp, Result]`):** An effectful program is an inductive syntax tree of effect commands and continuations (`Pure`, `PrintNat`, `ReadNat`, `GetState`, `PutState`, or custom `Eff.Call`).
2. **Higher-order structural induction proves laws with 0 axioms:** Because `IO` is a strictly positive higher-order inductive (`ReadNat(cont: Nat => IO[Result])`), Proof Samurai's `induction` tactic automatically generates universal induction hypotheses (`ih : forall (n: Nat) => P(cont(n))`), allowing `runIOBind`, all three monad laws (`ioLeftId`, `ioRightId`, `ioAssoc`), and Hoare rules to be verified 100% axiom-free.
3. **Deterministic trace semantics (`runIO`) for proofs:** Inside Proof Samurai, you prove trace specifications and Hoare invariants (`HoareIO`) about `runIO(prog, inputs, initState)` over *all possible* input streams and initial states.
4. **Extract once, interpret against a real runtime:** When extracted to Scala 3, TypeScript, JavaScript, Haskell, or OCaml, every `Prop`, `HoareIO`, and theorem is completely erased (0 bytes), leaving a clean algebraic `IO` tree that a ~15-line host interpreter connects to real stdin, stdout, sockets, or databases.

---

## Standard Library: `stdlib/IO.samurai`

### Core Types

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

For domain-specific side effects beyond console/state (e.g., key-value stores, HTTP requests, file descriptors, database queries), `stdlib/IO.samurai` also provides the generic algebraic effect tree `Eff`:

```scala
enum Eff[Req: Type, Resp: Type, Result: Type]: Type {
  case Done(value: Result)
  case Call(request: Req, cont: Resp => Eff[Req, Resp, Result])
}
```

### Monadic `do { ... }` Syntax

Proof Samurai provides lightweight `do { ... }` notation that desugars directly to `bind` calls with zero kernel changes (`do` is contextual, so identifiers named `do` remain valid outside `do { ... }`):

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

Supported statements inside `do { ... }`:
- `val x <- action` — monadic bind (`bind(action, x => rest)`)
- `val x = expr` — pure local binding (`{ val x = expr; rest }`)
- `action` — sequencing a side-effecting action whose result is ignored (`bind(action, _ => rest)`)
- Final expression — the resulting `IO[A]` action

Note: When writing multi-step branches inside `if (...) { ... } else { ... }`, wrap each multi-step branch in `do { ... }` so every effect step is chained via `bind` rather than discarded as a pure block expression.

### Built-In Verified Laws (`stdlib/IO.samurai`, 0 Axioms)

| Theorem / Definition | Meaning |
|---|---|
| `runIOBind` | `runIO(bind(act, cont), inputs, st)` equals running `act` first and feeding its `value`, `remainingInputs`, and `finalState` into `cont`, concatenating `outputs` (`r1.outputs ++ r2.outputs`). |
| `IOEquiv(p, q)` | Observational equivalence: `forall inputs, initState => runIO(p, inputs, initState) === runIO(q, inputs, initState)`. |
| `ioLeftId`, `ioRightId`, `ioAssoc` | All three monad laws proved with respect to `IOEquiv`. |
| `runIOPrintList` | `printList(xs)` outputs exactly `xs` without touching `inputs` or `state`. |
| `runIOReadN` | `readN(length(items))` on `items ++ rest` consumes `items`, returns `items`, and leaves `rest`. |
| `HoareIO(Pre, prog, Post)` | Compositional Hoare triple over input streams, output logs, return values, and state. |
| `hoarePure`, `hoarePrintNat`, `hoareGetState`, `hoarePutState`, `hoareConseq`, `hoareBind` | Sound Hoare-logic combinators for modular IO verification. |

---

## Practical Examples (`examples/VerifiedIO.samurai`)

### 1. Exact Conservation & Safety Invariants in Stateful IO

`withdrawSafe` checks the current balance before mutating state and prints status code `1` (accepted) or `0` (rejected):

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

We prove both exact conservation on success (`finalState + amount === initBalance`) and non-mutation on rejection:

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

For `depositWithCap(cap)`, we prove a **Hoare safety invariant** using `HoareIO`, `by_cases`, and `omega`: if `initBalance <= cap`, then for *every* possible user input stream (even empty stdin), `finalBalance <= cap` is preserved:

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

### 2. End-to-End IO Sorting Pipeline

Combining `stdlib/IO.samurai` with `stdlib/Sorting.samurai`, `readSortAndPrint(count)` reads `count` numbers from the input stream, sorts them with `insertionSort`, and writes the sorted sequence to the output stream:

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

`readSortAndPrintOutputIsVerified` proves that **the actual output stream** emitted by `readSortAndPrint` satisfies `IsSortedPermutation(items, outputs)` (both ascending `Sorted` and multiset-count preservation) for every input list `items`, trailing stream `rest`, and initial state `initState` — with 0 axioms.

---

## Connecting Extracted Code to a Real Runtime

Extract `examples/VerifiedIO.samurai` to any of the 5 supported targets:

```bash
sbt "run extract examples/VerifiedIO.samurai --target scala3 --module ExtractedVerifiedIO --strict --total"
sbt "run extract examples/VerifiedIO.samurai --target ts --module ExtractedVerifiedIO --strict --total"
sbt "run extract examples/VerifiedIO.samurai --target haskell --module VerifiedIO --strict --total"
sbt "run extract examples/VerifiedIO.samurai --target ocaml --module verified_io --strict --total"
```

All `HoareIO`, `IOEquiv`, `Sorted`, `Le`, and theorem definitions are completely erased. Below are thin real-world runtime interpreters for each target language.

### Scala 3 Runtime Interpreter

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

*(Note: `ExtractionSuite` compiles the extracted `VerifiedIO` Scala 3 module with `dotc` and executes this exact interpreter on the JVM in CI.)*

### TypeScript / JavaScript Runtime Interpreter

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

### Haskell Runtime Interpreter (`P.IO`)

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

### OCaml Runtime Interpreter

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

## Verification Command

```bash
sbt "run check stdlib/IO.samurai --strict"
sbt "run check examples/VerifiedIO.samurai --strict"
```
