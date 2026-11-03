# zed-testgen

Branch coverage and dead-code proofs for [Zed](https://github.com/zedlanguage/zed) programs, from Zed's own backward solver.

For every arm of every `if` in a function, `zed-testgen` either finds an input that reaches the arm, or proves that no integer input can. It then runs the function on each input it found and prints `test { … }` rows ready to paste into the source.

It writes no constraint solving of its own. Zed's compiler already contains a backward solver (intervals, congruences, a Presburger decision procedure and exact branch-and-prune search) that it uses for type checking. This tool asks that solver one question per branch and checks its answers.

## Quickstart

### 1. Write some Zed

[`quickstart.zed`](quickstart.zed) holds two functions. Every arm of `fizz` is reachable; `classify` has an arm that never can be, because its inner guard contradicts the outer one:

```zed
fizz(positional n: int) =
  if n mod 15 == 0 { "FizzBuzz" }
  else if n mod 3 == 0 { "Fizz" }
  else if n mod 5 == 0 { "Buzz" }
  else { n };

classify(positional x: int) =
  if x > 5 { if x < 3 { "impossible" } else { "big" } } else { "small" };
```

### 2. Run zed-testgen on it

```bash
cargo run --release -- quickstart.zed
```

```
fizz  (int) -> int | "Buzz" | "Fizz" | "FizzBuzz"  (6 arms)
  when  ((n mod 15) == 0)
        reached by 0 -> "FizzBuzz"   [confirmed]
  when  not (((n mod 15) == 0))
        reached by 1 -> 1   [confirmed]
  when  not (((n mod 15) == 0))  and  ((n mod 3) == 0)
        reached by 3 -> "Fizz"   [confirmed]
  when  not (((n mod 15) == 0))  and  not (((n mod 3) == 0))
        reached by 1 -> 1   [confirmed]
  when  not (((n mod 15) == 0))  and  not (((n mod 3) == 0))  and  ((n mod 5) == 0)
        reached by 5 -> "Buzz"   [confirmed]
  when  not (((n mod 15) == 0))  and  not (((n mod 3) == 0))  and  not (((n mod 5) == 0))
        reached by 1 -> 1   [confirmed]
  generated:  test { 0 -> "FizzBuzz", 1 -> 1, 3 -> "Fizz", 5 -> "Buzz" }

classify  (int) -> "big" | "impossible" | "small"  (4 arms)
  when  (x > 5)
        reached by 6 -> "big"   [confirmed]
  when  (x > 5)  and  (x < 3)
        DEAD for every integer input   [no input in ±2000 reaches it]
  when  (x > 5)  and  not ((x < 3))
        reached by 6 -> "big"   [confirmed]
  when  not ((x > 5))
        reached by 0 -> "small"   [confirmed]
  generated:  test { 6 -> "big", 0 -> "small" }

10 arms: 9 reached, 1 dead, 0 other; 0 witnesses not confirmed, 0 dead claims refuted
```

How to read it:

- Each function is listed with the signature Zed's checker inferred, then one entry per arm.
- `when …` is the arm's path condition: the guards that lead to it.
- `reached by 3 -> "Fizz"` means input `3` reaches the arm and the function returns `"Fizz"` there. `[confirmed]` means the arm was independently checked to run on that input (see below).
- `DEAD for every integer input` is a proof from Zed's solver that no integer reaches the arm: here `x > 5` and `x < 3` can't both hold. The bracket notes that brute force over `±2000` agrees.
- `generated:` collects one test row per distinct input.
- The last line totals the run. The exit status is 0 when every answer is confirmed.

### 3. Turn the rows into tests

`attach.py` writes each `generated:` block onto the function it belongs to:

```bash
cargo run --release -- quickstart.zed | python3 -I attach.py quickstart.zed > quickstart.tested.zed
```

```zed
fizz(positional n: int) =
  if n mod 15 == 0 { "FizzBuzz" }
  else if n mod 3 == 0 { "Fizz" }
  else if n mod 5 == 0 { "Buzz" }
  else { n }
  test { 0 -> "FizzBuzz", 1 -> 1, 3 -> "Fizz", 5 -> "Buzz" }

classify(positional x: int) =
  if x > 5 { if x < 3 { "impossible" } else { "big" } } else { "small" }
  test { 6 -> "big", 0 -> "small" }
```

Then run them with Zed's own test runner:

```bash
zedc test quickstart.tested.zed
```

```
6 passed, 0 failed
```

`attach.py` expects each function to end with `;` at the end of a line, as in the examples. (A Zed definition followed by a `test` block takes no `;`.)

## What it can prove

[`examples.zed`](examples.zed) has ten functions. On them the tool reaches 41 arms and proves 5 dead, each by a different part of the solver:

| function | dead arm | proved by |
|---|---|---|
| `classify` | `x > 5`, then `x < 3` | intervals |
| `half` | `x * 2 == 7` | exact inversion of `* 2` |
| `order` | `a > b`, then `b > a` | linear relations between inputs |
| `zone` | `clamp(x) > 10` | reading through a helper's own branches |
| `root2` | `x * x == 2` | nonlinear arithmetic |

The `order` case needs `a > b` and `b > a` at once. No interval for `a` or `b` alone rules that out; the solver's linear-relation domain does.

It also finds `x = 3` as the only integer with `x³ - x = 24`, and small, readable inputs for a shipping-fee rule, such as `(5001, 501) -> 4500`. Attached and run, the generated rows for `examples.zed` give `28 passed, 0 failed`.

## How it works

Each arm of an `if` has a **path condition**: the guards that must hold to reach it, each negated where the path took `else`. For each arm:

1. **Dead?** Zed's `preimage` runs the condition backwards over unbounded integer inputs. Its result is a box guaranteed to contain every input that reaches the arm. If the box is empty and the solver reports nowhere it had to stop, no integer input reaches the arm.
2. **Reached by what?** Zed's `witness` searches boxes growing outward from zero, from `[0, 10]` up to `±1,000,000`, for one input that meets the condition. Small boxes come first, so the tests use small numbers.
3. **Expected value.** The function is run on the witness by Zed's reference evaluator, and the result becomes the test row.

## How the answers are checked

The solver's answers are not taken on trust:

- **Every witness is confirmed independently of the path conditions.** The arm is replaced in the compiled term by a unique marker value, the function is run on the witness, and the marker must appear in the result. The check is one-sided: it can raise a false alarm (if later code discards the marker), never a false confirmation.
- **Every dead arm is cross-checked by brute force** over a small box (±2000 for one input, ±60 for two, ±12 for three). This can refute the solver but cannot prove it; the proof is the solver's.
- **`--knockout`** deliberately builds every `else` guard without its negation. On `examples.zed` it gives 17 unconfirmed witnesses and 15 refuted dead claims, and the tool exits with status 2. A check that cannot fail would show nothing here.

Exit status: 0 when every answer is confirmed, 2 when any witness is unconfirmed or any dead claim is refuted.

## Limits

- Only functions whose parameters are all `int`. Others are listed as skipped.
- Only `if` arms. Zed's `match` arrives at a later layer of the language.
- A "dead" result is a proof only when the solver reported no stops. Arms it cannot decide are reported as undecided, or as unreached within the largest search box, which is not a proof.
- It calls Zed's internal solver modules, which are not a stable public API. `Cargo.toml` pins Zed to the commit it was built and checked against, `a3c52bf`.

## Building

Needs Rust 1.99.1, selected by [`rust-toolchain.toml`](rust-toolchain.toml); Zed's compiler uses `if let` match guards. Cargo fetches Zed itself from GitHub at the pinned commit.

`zedc`, Zed's compiler, is only needed to run the generated tests. To install it at the same commit:

```bash
cargo +1.99.1 install --git https://github.com/zedlanguage/zed --rev a3c52bf6c6d03f51bef01c6fea8f518dd3c6b570 zedc
```

## Things Zed's semantics make visible

Two behaviours of Zed that the tool surfaced, both documented upstream:

- A failure inside an equality test is compared, not propagated: `0 mod 0 == 0` is `false`, so `if n mod d == 0 { … } else { … }` takes `else` when `d` is 0.
- `div` and `mod` are Euclidean, so a decimal formatter built on them is wrong for negative numbers unless it handles the sign.
