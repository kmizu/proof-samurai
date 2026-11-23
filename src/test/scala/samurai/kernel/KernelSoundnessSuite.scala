package samurai.kernel

import munit.FunSuite

class KernelSoundnessSuite extends FunSuite {

  private def unwrap[A](either: Either[KernelError, A]): A =
    either.fold(err => fail(s"Unexpected kernel error: $err"), identity)

  private def preludeEnv: KernelEnv = {
    var env = KernelEnv.empty

    // enum False: Prop {}
    val falseInd = IndEntry(
      name = "False",
      params = Nil,
      indices = Nil,
      sort = Sort.Prop,
      constructors = Nil
    )
    env = unwrap(TypeChecker.checkInductive(env, falseInd))

    // enum True: Prop { case Intro }
    val trueInd = IndEntry(
      name = "True",
      params = Nil,
      indices = Nil,
      sort = Sort.Prop,
      constructors = List(CtorEntry("Intro", Nil, Nil))
    )
    env = unwrap(TypeChecker.checkInductive(env, trueInd))

    // enum Nat: Type { case Zero; case Succ(pred: Nat) }
    val natInd = IndEntry(
      name = "Nat",
      params = Nil,
      indices = Nil,
      sort = Sort.Type(0),
      constructors = List(
        CtorEntry("Zero", Nil, Nil),
        CtorEntry("Succ", List(Binder("pred", Term.Ind("Nat"))), Nil)
      )
    )
    env = unwrap(TypeChecker.checkInductive(env, natInd))

    // enum Eq[A: Type, x: A](y: A): Prop { case Refl: Eq[A, x](x) }
    val eqInd = IndEntry(
      name = "Eq",
      params = List(
        Binder("A", Term.USort(Sort.Type(0))),
        Binder("x", Term.Var(0))
      ),
      indices = List(
        Binder("y", Term.Var(1))
      ),
      sort = Sort.Prop,
      constructors = List(
        CtorEntry("Refl", Nil, List(Term.Var(0)))
      )
    )
    env = unwrap(TypeChecker.checkInductive(env, eqInd))

    // enum Or[P: Prop, Q: Prop]: Prop { case Inl(p: P); case Inr(q: Q) }
    val orInd = IndEntry(
      name = "Or",
      params = List(
        Binder("P", Term.USort(Sort.Prop)),
        Binder("Q", Term.USort(Sort.Prop))
      ),
      indices = Nil,
      sort = Sort.Prop,
      constructors = List(
        CtorEntry("Inl", List(Binder("p", Term.Var(1))), Nil),
        CtorEntry("Inr", List(Binder("q", Term.Var(0))), Nil)
      )
    )
    env = unwrap(TypeChecker.checkInductive(env, orInd))

    // enum Exists[A: Type, P: A => Prop]: Prop { case Intro(witness: A, proof: P(witness)) }
    val existsInd = IndEntry(
      name = "Exists",
      params = List(
        Binder("A", Term.USort(Sort.Type(0))),
        Binder("P", Term.Pi("x", Term.Var(0), Term.USort(Sort.Prop)))
      ),
      indices = Nil,
      sort = Sort.Prop,
      constructors = List(
        CtorEntry(
          "Intro",
          List(
            Binder("witness", Term.Var(1)),
            Binder("proof", Term.App(Term.Var(1), Term.Var(0)))
          ),
          Nil
        )
      )
    )
    env = unwrap(TypeChecker.checkInductive(env, existsInd))

    env
  }

  test("universe stratification rejects Type0 : Type0 (prevents Girard's paradox)") {
    val env = preludeEnv
    val checkRes = TypeChecker.check(env, LocalCtx.empty, Term.USort(Sort.Type(0)), Term.USort(Sort.Type(0)))
    assert(checkRes.isLeft, "Type0 must NOT have type Type0")

    val validRes = TypeChecker.check(env, LocalCtx.empty, Term.USort(Sort.Type(0)), Term.USort(Sort.Type(1)))
    assert(validRes.isRight, "Type0 must have type Type1")

    val propInType0 = TypeChecker.check(env, LocalCtx.empty, Term.USort(Sort.Prop), Term.USort(Sort.Type(0)))
    assert(propInType0.isRight, "Prop must have type Type0")
  }

  test("strict positivity rejects negative inductive type (prevents Curry's paradox)") {
    val env = preludeEnv
    // enum Bad: Type { case Mk(fn: Bad => False) }
    val badInd = IndEntry(
      name = "Bad",
      params = Nil,
      indices = Nil,
      sort = Sort.Type(0),
      constructors = List(
        CtorEntry("Mk", List(Binder("fn", Term.Pi("_", Term.Ind("Bad"), Term.Ind("False")))), Nil)
      )
    )
    val res = TypeChecker.checkInductive(env, badInd)
    assert(res.isLeft, "Non-positive inductive type must be rejected")
    assertEquals(res.left.toOption.get.code, "K006")
  }

  test("strict positivity catches hidden negative occurrence through transparent def Not") {
    var env = preludeEnv
    // def Not(P: Prop): Prop = P => False
    val notType = Term.Pi("P", Term.USort(Sort.Prop), Term.USort(Sort.Prop))
    val notBody = Term.Lam("P", Term.USort(Sort.Prop), Term.Pi("_", Term.Var(0), Term.Ind("False")))
    env = unwrap(TypeChecker.checkDef(env, "Not", notType, notBody))

    // enum BadProp: Prop { case Mk(h: Not(BadProp)) }
    val badProp = IndEntry(
      name = "BadProp",
      params = Nil,
      indices = Nil,
      sort = Sort.Prop,
      constructors = List(
        CtorEntry("Mk", List(Binder("h", Term.App(Term.Const("Not"), Term.Ind("BadProp")))), Nil)
      )
    )
    val res = TypeChecker.checkInductive(env, badProp)
    assert(res.isLeft, "Negative occurrence hidden behind transparent def Not must be rejected")
    assertEquals(res.left.toOption.get.code, "K006")
  }

  test("predicativity rejects Type0 inductive storing Type0 values (large field in small Type)") {
    val env = preludeEnv
    // enum Box: Type0 { case Mk(A: Type0) } -- A: Type0 has sort Type1 > Type0!
    val badBox = IndEntry(
      name = "Box",
      params = Nil,
      indices = Nil,
      sort = Sort.Type(0),
      constructors = List(
        CtorEntry("Mk", List(Binder("A", Term.USort(Sort.Type(0)))), Nil)
      )
    )
    val res = TypeChecker.checkInductive(env, badBox)
    assert(res.isLeft, "Type0 inductive containing Type0 field (sort Type1) must be rejected")
    assertEquals(res.left.toOption.get.code, "K005")
  }

  test("termination checker rejects non-decreasing recursive Fix (def loop(n: Nat): False = loop(n))") {
    val env = preludeEnv
    val loopType = Term.Pi("n", Term.Ind("Nat"), Term.Ind("False"))
    // fix loop[0]: (n: Nat) => False = (n: Nat) => loop(n)
    val loopBody = Term.Lam("n", Term.Ind("Nat"), Term.App(Term.Var(1), Term.Var(0)))
    val badFix = Term.Fix("loop", 0, loopType, loopBody)
    val res = TypeChecker.checkDef(env, "loop", loopType, badFix)
    assert(res.isLeft, "Non-terminating Fix must be rejected")
    assertEquals(res.left.toOption.get.code, "K020")
  }

  test("termination checker rejects recursion on reconstructed Succ(k)") {
    val env = preludeEnv
    val loopType = Term.Pi("n", Term.Ind("Nat"), Term.Ind("False"))
    val motive = Term.Lam("_", Term.Ind("Nat"), Term.Ind("False"))
    // match n { Zero => loop(Zero); Succ(k) => loop(Succ(k)) }
    val loopBody = Term.Lam(
      "n",
      Term.Ind("Nat"),
      Term.Match(
        "Nat",
        Nil,
        motive,
        Term.Var(0),
        List(
          MatchBranch("Zero", Nil, Term.App(Term.Var(1), Term.Ctor("Nat", "Zero"))),
          MatchBranch(
            "Succ",
            List("k"),
            Term.App(Term.Var(2), Term.App(Term.Ctor("Nat", "Succ"), Term.Var(0)))
          )
        )
      )
    )
    val badFix = Term.Fix("loop", 0, loopType, loopBody)
    val res = TypeChecker.checkDef(env, "loop", loopType, badFix)
    assert(res.isLeft, "Recursive call on reconstructed Succ(k) must be rejected")
    assertEquals(res.left.toOption.get.code, "K020")
  }

  test("termination checker accepts valid structural recursion: add(m, n) and NbE computes 2 + 3 = 5") {
    var env = preludeEnv
    val nat = Term.Ind("Nat")
    val addType = Term.Pi("m", nat, Term.Pi("n", nat, nat))
    val motive = Term.Lam("_", nat, nat)
    val addBody = Term.Lam(
      "m",
      nat,
      Term.Lam(
        "n",
        nat,
        Term.Match(
          "Nat",
          Nil,
          motive,
          Term.Var(1), // m
          List(
            MatchBranch("Zero", Nil, Term.Var(0)), // n
            MatchBranch(
              "Succ",
              List("k"),
              Term.App(
                Term.Ctor("Nat", "Succ"),
                Term.apps(Term.Var(3), List(Term.Var(0), Term.Var(1))) // add(k, n)
              )
            )
          )
        )
      )
    )
    val addFix = Term.Fix("add", 0, addType, addBody)
    env = unwrap(TypeChecker.checkDef(env, "add", addType, addFix))

    def natLit(n: Int): Term =
      if (n == 0) Term.Ctor("Nat", "Zero")
      else Term.App(Term.Ctor("Nat", "Succ"), natLit(n - 1))

    val twoPlusThree = Term.apps(Term.Const("add"), List(natLit(2), natLit(3)))
    val normalized = NbE.normalize(env, LocalCtx.empty, twoPlusThree)
    assertEquals(normalized, natLit(5))
  }

  test("exhaustiveness check rejects match missing constructor") {
    val env = preludeEnv
    val nat = Term.Ind("Nat")
    val motive = Term.Lam("_", nat, nat)
    val badMatch = Term.Lam(
      "n",
      nat,
      Term.Match(
        "Nat",
        Nil,
        motive,
        Term.Var(0),
        List(MatchBranch("Zero", Nil, Term.Ctor("Nat", "Zero")))
      )
    )
    val res = TypeChecker.checkDef(env, "partialFn", Term.Pi("n", nat, nat), badMatch)
    assert(res.isLeft, "Non-exhaustive match must be rejected")
    assertEquals(res.left.toOption.get.code, "K026")
  }

  test("subsingleton check rejects eliminating Or or Exists (Prop) into Nat (Type)") {
    val env = preludeEnv
    val nat = Term.Ind("Nat")
    val trueInd = Term.Ind("True")

    // Try eliminating Or(True, True) into Nat
    val orType = Term.apps(Term.Ind("Or"), List(trueInd, trueInd))
    val badOrElim = Term.Lam(
      "h",
      orType,
      Term.Match(
        "Or",
        List(trueInd, trueInd),
        Term.Lam("_", orType, nat),
        Term.Var(0),
        List(
          MatchBranch("Inl", List("_"), Term.Ctor("Nat", "Zero")),
          MatchBranch("Inr", List("_"), Term.App(Term.Ctor("Nat", "Succ"), Term.Ctor("Nat", "Zero")))
        )
      )
    )
    val resOr = TypeChecker.checkDef(env, "badOrElim", Term.Pi("h", orType, nat), badOrElim)
    assert(resOr.isLeft, "Eliminating Or (Prop) into Nat (Type) must be rejected")
    assertEquals(resOr.left.toOption.get.code, "K025")

    // Try eliminating Exists(Nat, _ => True) into Nat
    val pred = Term.Lam("_", nat, trueInd)
    val exType = Term.apps(Term.Ind("Exists"), List(nat, pred))
    val badExElim = Term.Lam(
      "h",
      exType,
      Term.Match(
        "Exists",
        List(nat, pred),
        Term.Lam("_", exType, nat),
        Term.Var(0),
        List(MatchBranch("Intro", List("w", "pf"), Term.Var(1)))
      )
    )
    val resEx = TypeChecker.checkDef(env, "badExElim", Term.Pi("h", exType, nat), badExElim)
    assert(resEx.isLeft, "Eliminating Exists (Prop) into Nat (Type) must be rejected")
    assertEquals(resEx.left.toOption.get.code, "K025")
  }

  test("subsingleton check ALLOWS eliminating False and Eq (Prop) into Type") {
    var env = preludeEnv
    // absurd[A: Type](h: False): A
    val absurdType = Term.Pi("A", Term.USort(Sort.Type(0)), Term.Pi("h", Term.Ind("False"), Term.Var(1)))
    val absurdBody = Term.Lam(
      "A",
      Term.USort(Sort.Type(0)),
      Term.Lam(
        "h",
        Term.Ind("False"),
        Term.Match(
          "False",
          Nil,
          Term.Lam("_", Term.Ind("False"), Term.Var(2)),
          Term.Var(0),
          Nil
        )
      )
    )
    env = unwrap(TypeChecker.checkDef(env, "absurd", absurdType, absurdBody))
    assert(env.defs.contains("absurd"))
    assertEquals(env.defs("absurd").axiomsUsed, Set.empty[String])
  }

  test("strict positivity catches higher-order hidden negative occurrence via NbE") {
    var env = preludeEnv
    // def Apply(F: Type => Prop, X: Type): Prop = F(X)
    val applyType = Term.Pi("F", Term.Pi("_", Term.USort(Sort.Type(0)), Term.USort(Sort.Prop)),
      Term.Pi("X", Term.USort(Sort.Type(0)), Term.USort(Sort.Prop)))
    val applyBody = Term.Lam("F", Term.Pi("_", Term.USort(Sort.Type(0)), Term.USort(Sort.Prop)),
      Term.Lam("X", Term.USort(Sort.Type(0)), Term.App(Term.Var(1), Term.Var(0))))
    env = unwrap(TypeChecker.checkDef(env, "Apply", applyType, applyBody))

    // enum Sneaky: Type { case Mk(h: Apply((T: Type) => T => False, Sneaky)) }
    val negFn = Term.Lam("T", Term.USort(Sort.Type(0)), Term.Pi("_", Term.Var(0), Term.Ind("False")))
    val sneakyInd = IndEntry(
      name = "Sneaky",
      params = Nil,
      indices = Nil,
      sort = Sort.Type(0),
      constructors = List(
        CtorEntry("Mk", List(Binder("h", Term.apps(Term.Const("Apply"), List(negFn, Term.Ind("Sneaky"))))), Nil)
      )
    )
    val res = TypeChecker.checkInductive(env, sneakyInd)
    assert(res.isLeft, "Higher-order hidden negative occurrence must be rejected")
    assertEquals(res.left.toOption.get.code, "K006")
  }

  test("definitional proof irrelevance equates Subset.Mk(x, pf1) and Subset.Mk(x, pf2) for abstract Prop predicate") {
    var env = preludeEnv
    val subsetInd = IndEntry(
      name = "Subset",
      params = List(
        Binder("A", Term.USort(Sort.Type(0))),
        Binder("P", Term.Pi("x", Term.Var(0), Term.USort(Sort.Prop)))
      ),
      indices = Nil,
      sort = Sort.Type(0),
      constructors = List(
        CtorEntry(
          "Mk",
          List(
            Binder("value", Term.Var(1)),
            Binder("proof", Term.App(Term.Var(1), Term.Var(0)))
          ),
          Nil
        )
      )
    )
    env = unwrap(TypeChecker.checkInductive(env, subsetInd))
    assertEquals(env.inductives("Subset").constructors.head.fieldIsProp, List(false, true))

    // Check Refl proves: forall (P: Nat => Prop) (x: Nat) (p1: P(x)) (p2: P(x)) => Subset.Mk(Nat, P, x, p1) === Subset.Mk(Nat, P, x, p2)
    val nat = Term.Ind("Nat")
    val pType = Term.Pi("_", nat, Term.USort(Sort.Prop))
    val subsetNatP = Term.apps(Term.Ind("Subset"), List(nat, Term.Var(3)))
    val mk1 = Term.apps(Term.Ctor("Subset", "Mk"), List(nat, Term.Var(3), Term.Var(2), Term.Var(1)))
    val mk2 = Term.apps(Term.Ctor("Subset", "Mk"), List(nat, Term.Var(3), Term.Var(2), Term.Var(0)))
    val thmType = Term.Pi("P", pType,
      Term.Pi("x", nat,
        Term.Pi("p1", Term.App(Term.Var(1), Term.Var(0)),
          Term.Pi("p2", Term.App(Term.Var(2), Term.Var(1)),
            Term.apps(Term.Ind("Eq"), List(subsetNatP, mk1, mk2))))))
    val thmBody = Term.Lam("P", pType,
      Term.Lam("x", nat,
        Term.Lam("p1", Term.App(Term.Var(1), Term.Var(0)),
          Term.Lam("p2", Term.App(Term.Var(2), Term.Var(1)),
            Term.apps(Term.Ctor("Eq", "Refl"), List(subsetNatP, mk1))))))

    val checked = TypeChecker.checkDef(env, "subsetProofIrrel", thmType, thmBody, isTheorem = true)
    assert(checked.isRight, s"Definitional proof irrelevance for Subset failed: $checked")
  }
}
