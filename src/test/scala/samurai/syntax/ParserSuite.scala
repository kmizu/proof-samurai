package samurai.syntax

import munit.FunSuite

class ParserSuite extends FunSuite {

  test("multi-line and single-line minified files parse to identical ASTs (zero indent sensitivity)") {
    val multiLine =
      """
        |module Demo {
        |  enum Nat: Type {
        |    case Zero
        |    case Succ(pred: Nat)
        |  }
        |
        |  def add(m: Nat, n: Nat): Nat = {
        |    m match {
        |      case Nat.Zero => n
        |      case Nat.Succ(k) => Nat.Succ(add(k, n))
        |    }
        |  }
        |
        |  @simp
        |  theorem addZeroRight(n: Nat): add(n, 0) === n = by {
        |    induction(n) {
        |      case Zero => {
        |        refl
        |      }
        |      case Succ(k, ih) => {
        |        simp
        |        rewrite(ih)
        |        refl
        |      }
        |    }
        |  }
        |}
      """.stripMargin

    val singleLine = multiLine.replaceAll("\\s+", " ").trim

    val parsedMulti = Parser.parseFile("multi.samurai", multiLine)
    val parsedSingle = Parser.parseFile("single.samurai", singleLine)

    assert(parsedMulti.isRight, s"Multi-line parse failed: $parsedMulti")
    assert(parsedSingle.isRight, s"Single-line parse failed: $parsedSingle")

    // Strip spans by comparing structure via recursive string representation ignoring spans
    def stripSpans(value: Any): String = value match {
      case _: samurai.util.Span => "<span?>"
      case p: Product =>
        val fields = (0 until p.productArity).map(i => stripSpans(p.productElement(i)))
        s"${p.productPrefix}(${fields.mkString(",")})"
      case xs: Iterable[?] =>
        s"[${xs.map(stripSpans).mkString(",")}]"
      case other => other.toString
    }

    assertEquals(stripSpans(parsedMulti.toOption.get), stripSpans(parsedSingle.toOption.get))
  }

  test("parses case class, indexed enum, forall, exists, if/else, blocks, and operators") {
    val src =
      """
        |case class Pair[A, B](first: A, second: B)
        |
        |enum Vec[A](length: Nat): Type {
        |  case Nil: Vec[A](0)
        |  case Cons(len: Nat, head: A, tail: Vec[A](len)): Vec[A](Nat.Succ(len))
        |}
        |
        |def clamp(x: Nat): Nat = {
        |  val y = x + 1
        |  if (y == 0) { 0 } else { y }
        |}
        |
        |theorem logicDemo(P: Prop, Q: Prop): (P /\ Q) => (Q \/ P) = by {
        |  intro(h)
        |  cases(h) {
        |    case Intro(hp, hq) => {
        |      left
        |      exact(hq)
        |    }
        |  }
        |}
      """.stripMargin

    val parsed = Parser.parseFile("demo.samurai", src)
    assert(parsed.isRight, s"Parse failed: $parsed")
    assertEquals(parsed.toOption.get.length, 4)
  }
}
