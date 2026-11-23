package samurai.kernel

object Pretty {
  def show(t: Term, ctxNames: List[String] = Nil): String =
    showPrec(t, ctxNames, 0)

  private def freshName(base: String, used: List[String]): String = {
    val clean = if (base.isEmpty || base == "_") "_" else base
    if (clean == "_" || !used.contains(clean)) clean
    else {
      var i = 1
      while (used.contains(s"$clean$i")) i += 1
      s"$clean$i"
    }
  }

  private def parensIf(cond: Boolean, s: String): String =
    if (cond) s"($s)" else s

  private def showPrec(t: Term, names: List[String], prec: Int): String = t match {
    case Term.USort(s) => s.toString
    case Term.Var(idx) =>
      if (idx >= 0 && idx < names.length) names(idx)
      else s"#v$idx"
    case Term.Const(n) => n
    case Term.Ind(n)   => n
    case Term.Ctor(ind, c) => s"$ind.$c"

    case Term.Pi(n, dom, cod) =>
      val usedInCod = Term.freeVarOccurs(cod, 0)
      val s = if (!usedInCod) {
        s"${showPrec(dom, names, 2)} => ${showPrec(cod, "_" :: names, 1)}"
      } else {
        val fn = freshName(n, names)
        s"($fn: ${showPrec(dom, names, 0)}) => ${showPrec(cod, fn :: names, 1)}"
      }
      parensIf(prec > 1, s)

    case Term.Lam(n, dom, body) =>
      val fn = freshName(n, names)
      val s = s"($fn: ${showPrec(dom, names, 0)}) => ${showPrec(body, fn :: names, 1)}"
      parensIf(prec > 1, s)

    case app @ Term.App(_, _) =>
      val (head, args) = Term.splitApps(app)
      // Sugar for Eq[A, x](y) -> x === y
      head match {
        case Term.Ind("Eq") if args.length == 3 =>
          val s = s"${showPrec(args(1), names, 3)} === ${showPrec(args(2), names, 3)}"
          parensIf(prec > 2, s)
        case _ =>
          val hStr = showPrec(head, names, 4)
          val aStr = args.map(showPrec(_, names, 0)).mkString(", ")
          parensIf(prec > 3, s"$hStr($aStr)")
      }

    case Term.Let(n, ty, v, b) =>
      val fn = freshName(n, names)
      val s = s"{ val $fn: ${showPrec(ty, names, 0)} = ${showPrec(v, names, 0)}; ${showPrec(b, fn :: names, 0)} }"
      parensIf(prec > 0, s)

    case Term.Match(ind, _, _, scrut, branches) =>
      val brStr = branches.map { br =>
        val boundNames = br.fieldNames.foldLeft(names)((ns, f) => freshName(f, ns) :: ns)
        val patFields = boundNames.take(br.arity).reverse
        val pat =
          if (patFields.isEmpty) s"$ind.${br.ctorName}"
          else s"$ind.${br.ctorName}(${patFields.mkString(", ")})"
        s"case $pat => ${showPrec(br.body, boundNames, 0)}"
      }.mkString("; ")
      val s = s"${showPrec(scrut, names, 4)} match { $brStr }"
      parensIf(prec > 0, s)

    case Term.Fix(n, recIdx, ty, body) =>
      val fn = freshName(n, names)
      s"fix $fn[$recIdx]: ${showPrec(ty, names, 0)} = ${showPrec(body, fn :: names, 0)}"
  }
}
