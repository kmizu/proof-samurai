package samurai.kernel

import scala.util.boundary
import scala.util.boundary.break

/**
 * Human- and AI-friendly pretty-printer for Core Kernel Terms.
 *
 * Renders terms in idiomatic Scala 3 brace syntax:
 * - Folds `Fix(name, ...)` to `name` so goals & errors stay compact and readable
 * - Renders closed `Nat` literals (`0`, `1`, `2`), `Bool` (`true`, `false`), and `List` (`[1, 2]`, `h :: t`)
 * - Uses infix notation for `+`, `*`, `-`, `++`, `===`, `/\`, `\/`, `<=`, `<`, `==`, `&&`, `||`, `=>`
 * - Hides redundant leading type arguments on polymorphic functions
 *
 * Use `showFull` when inspecting the full underlying kernel term (e.g. `#print` or debugging).
 */
object Pretty {

  def show(term: Term, ctxNames: List[String] = Nil): String =
    showPrec(term, ctxNames, prec = 0, expandFix = false)

  def showFull(term: Term, ctxNames: List[String] = Nil): String =
    showPrec(term, ctxNames, prec = 0, expandFix = true)

  private val PolymorphicDropTypeArgs: Map[String, Int] = Map(
    "length"    -> 1,
    "append"    -> 1,
    "reverse"   -> 1,
    "map"       -> 2,
    "filter"    -> 1,
    "foldLeft"  -> 2,
    "treeSize"  -> 1,
    "mirror"    -> 1,
    "flatten"   -> 1,
    "vecHead"   -> 1,
    "vecMap"    -> 2,
    "vecAppend" -> 1,
    "swap"      -> 2,
    "enqueue"   -> 1,
    "dequeue"   -> 1,
    "peek"      -> 1,
    "toList"    -> 1
  )

  private def freshName(base: String, used: List[String]): String = {
    val clean = if (base.isEmpty || base == "_") "_" else base
    if (clean == "_" || !used.contains(clean)) clean
    else {
      var counter = 1
      while (used.contains(s"$clean$counter")) counter += 1
      s"$clean$counter"
    }
  }

  private def parensIf(cond: Boolean, text: String): String =
    if (cond) s"($text)" else text

  private def tryNatLiteral(term: Term): Option[Int] = term match {
    case Term.Ctor("Nat", "Zero")                 => Some(0)
    case Term.App(Term.Ctor("Nat", "Succ"), rest) => tryNatLiteral(rest).map(_ + 1)
    case _                                        => None
  }

  private def tryListLiteral(term: Term): Option[List[Term]] = {
    val (head, args) = Term.splitApps(term)
    head match {
      case Term.Ctor("List", "Nil") if args.length == 1 => Some(Nil)
      case Term.Ctor("List", "Cons") if args.length == 3 =>
        tryListLiteral(args(2)).map(args(1) :: _)
      case _ => None
    }
  }

  private def headFunctionName(term: Term): Option[String] = term match {
    case Term.Const(name)        => Some(name)
    case Term.Fix(name, _, _, _) => Some(name)
    case Term.MutualFix(defs, sel) if sel >= 0 && sel < defs.length => Some(defs(sel).name)
    case _                       => None
  }

  private def showPrec(term: Term, names: List[String], prec: Int, expandFix: Boolean): String = boundary {
    if (!expandFix) {
      tryNatLiteral(term).foreach(n => break(n.toString))
      tryListLiteral(term).foreach { elems =>
        break("[" + elems.map(showPrec(_, names, 0, expandFix)).mkString(", ") + "]")
      }
    }

    term match {
      case Term.USort(sort) => sort.toString

      case Term.Var(index) =>
        if (index >= 0 && index < names.length) names(index)
        else s"#v$index"

      case Term.Const(name) => name
      case Term.Ind(name)   => name

      case Term.Ctor("Bool", "True") if !expandFix  => "true"
      case Term.Ctor("Bool", "False") if !expandFix => "false"
      case Term.Ctor(ind, ctor)                     => s"$ind.$ctor"

      case Term.Pi(binderName, domain, codomain) =>
        val usedInCod = Term.freeVarOccurs(codomain, 0)
        val rendered =
          if (!usedInCod) {
            s"${showPrec(domain, names, 2, expandFix)} => ${showPrec(codomain, "_" :: names, 1, expandFix)}"
          } else {
            val clean = freshName(binderName, names)
            s"($clean: ${showPrec(domain, names, 0, expandFix)}) => ${showPrec(codomain, clean :: names, 1, expandFix)}"
          }
        parensIf(prec > 1, rendered)

      case Term.Lam(binderName, domain, body) =>
        val clean = freshName(binderName, names)
        val rendered = s"($clean: ${showPrec(domain, names, 0, expandFix)}) => ${showPrec(body, clean :: names, 1, expandFix)}"
        parensIf(prec > 1, rendered)

      case app @ Term.App(_, _) =>
        showApp(app, names, prec, expandFix)

      case Term.Let(binderName, declaredType, value, body) =>
        val clean = freshName(binderName, names)
        val rendered =
          s"{ val $clean: ${showPrec(declaredType, names, 0, expandFix)} = ${showPrec(value, names, 0, expandFix)}; ${showPrec(body, clean :: names, 0, expandFix)} }"
        parensIf(prec > 0, rendered)

      case Term.Match(ind, _, _, scrutinee, branches) =>
        val branchStrings = branches.map { br =>
          val boundNames = br.fieldNames.foldLeft(names)((ns, f) => freshName(f, ns) :: ns)
          val patFields = boundNames.take(br.arity).reverse
          val pat =
            if (patFields.isEmpty) s"$ind.${br.ctorName}"
            else s"$ind.${br.ctorName}(${patFields.mkString(", ")})"
          s"case $pat => ${showPrec(br.body, boundNames, 0, expandFix)}"
        }.mkString("; ")
        val rendered = s"${showPrec(scrutinee, names, 8, expandFix)} match { $branchStrings }"
        parensIf(prec > 0, rendered)

      case Term.Fix(fixName, recIdx, fixType, body) =>
        if (!expandFix) {
          fixName
        } else {
          val clean = freshName(fixName, names)
          s"fix $clean[$recIdx]: ${showPrec(fixType, names, 0, expandFix)} = ${showPrec(body, clean :: names, 0, expandFix)}"
        }

      case Term.MutualFix(defs, sel) =>
        val selected = if (sel >= 0 && sel < defs.length) defs(sel).name else s"mutual#$sel"
        if (!expandFix) {
          selected
        } else {
          val boundNames = defs.foldLeft(names)((ns, d) => freshName(d.name, ns) :: ns)
          val parts = defs.map { d =>
            s"${d.name}[${d.recArgIdx}]: ${showPrec(d.ty, names, 0, expandFix)} = ${showPrec(d.body, boundNames, 0, expandFix)}"
          }.mkString("; ")
          s"mutual { $parts }.$selected"
        }
    }
  }

  private def showApp(app: Term.App, names: List[String], prec: Int, expandFix: Boolean): String = boundary {
    val (head, args) = Term.splitApps(app)

    if (!expandFix) {
      head match {
        case Term.Ind("Eq") if args.length == 3 =>
          val s = s"${showPrec(args(1), names, 5, expandFix)} === ${showPrec(args(2), names, 5, expandFix)}"
          break(parensIf(prec > 4, s))
        case Term.Ind("And") if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 4, expandFix)} /\\ ${showPrec(args(1), names, 3, expandFix)}"
          break(parensIf(prec > 3, s))
        case Term.Ind("Or") if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 3, expandFix)} \\/ ${showPrec(args(1), names, 2, expandFix)}"
          break(parensIf(prec > 2, s))
        case Term.Const("Not") if args.length == 1 =>
          break(parensIf(prec > 7, s"~${showPrec(args(0), names, 7, expandFix)}"))
        case Term.Ctor("List", "Cons") if args.length == 3 =>
          val s = s"${showPrec(args(1), names, 6, expandFix)} :: ${showPrec(args(2), names, 5, expandFix)}"
          break(parensIf(prec > 5, s))
        case Term.Ctor("List", "Nil") if args.length == 1 =>
          break("[]")
        case Term.Ind("List") if args.length == 1 =>
          break(s"List[${showPrec(args(0), names, 0, expandFix)}]")
        case Term.Ind("Option") if args.length == 1 =>
          break(s"Option[${showPrec(args(0), names, 0, expandFix)}]")
        case Term.Ind("Tree") if args.length == 1 =>
          break(s"Tree[${showPrec(args(0), names, 0, expandFix)}]")
        case Term.Ind("Pair") if args.length == 2 =>
          break(s"Pair[${showPrec(args(0), names, 0, expandFix)}, ${showPrec(args(1), names, 0, expandFix)}]")
        case Term.Ind("Vec") if args.length == 2 =>
          break(s"Vec[${showPrec(args(0), names, 0, expandFix)}](${showPrec(args(1), names, 0, expandFix)})")
        case _ => ()
      }

      headFunctionName(head).foreach {
        case "add" if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 6, expandFix)} + ${showPrec(args(1), names, 7, expandFix)}"
          break(parensIf(prec > 6, s))
        case "sub" if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 6, expandFix)} - ${showPrec(args(1), names, 7, expandFix)}"
          break(parensIf(prec > 6, s))
        case "mul" if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 7, expandFix)} * ${showPrec(args(1), names, 8, expandFix)}"
          break(parensIf(prec > 7, s))
        case "append" if args.length == 3 =>
          val s = s"${showPrec(args(1), names, 6, expandFix)} ++ ${showPrec(args(2), names, 5, expandFix)}"
          break(parensIf(prec > 5, s))
        case "ble" if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 5, expandFix)} <= ${showPrec(args(1), names, 5, expandFix)}"
          break(parensIf(prec > 4, s))
        case "blt" if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 5, expandFix)} < ${showPrec(args(1), names, 5, expandFix)}"
          break(parensIf(prec > 4, s))
        case "beq" if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 5, expandFix)} == ${showPrec(args(1), names, 5, expandFix)}"
          break(parensIf(prec > 4, s))
        case "andBool" if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 4, expandFix)} && ${showPrec(args(1), names, 4, expandFix)}"
          break(parensIf(prec > 3, s))
        case "orBool" if args.length == 2 =>
          val s = s"${showPrec(args(0), names, 3, expandFix)} || ${showPrec(args(1), names, 2, expandFix)}"
          break(parensIf(prec > 2, s))
        case "notBool" if args.length == 1 =>
          break(parensIf(prec > 7, s"!${showPrec(args(0), names, 7, expandFix)}"))
        case fnName if PolymorphicDropTypeArgs.contains(fnName) =>
          val dropCount = PolymorphicDropTypeArgs(fnName)
          if (args.length > dropCount) {
            val visibleArgs = args.drop(dropCount).map(showPrec(_, names, 0, expandFix)).mkString(", ")
            break(parensIf(prec > 8, s"$fnName($visibleArgs)"))
          }
        case _ => ()
      }
    }

    val headStr = showPrec(head, names, 9, expandFix)
    val argsStr = args.map(showPrec(_, names, 0, expandFix)).mkString(", ")
    parensIf(prec > 8, s"$headStr($argsStr)")
  }
}
