package samurai.kernel

enum Sort {
  case Prop
  case Type(level: Int)

  def succ: Sort = this match {
    case Sort.Prop    => Sort.Type(0)
    case Sort.Type(i) => Sort.Type(i + 1)
  }

  def piSort(codSort: Sort): Sort = (this, codSort) match {
    case (_, Sort.Prop)             => Sort.Prop // Impredicative Prop
    case (Sort.Prop, Sort.Type(j))  => Sort.Type(j)
    case (Sort.Type(i), Sort.Type(j)) => Sort.Type(math.max(i, j))
  }

  def leq(other: Sort): Boolean = (this, other) match {
    case (Sort.Prop, Sort.Prop)       => true
    case (Sort.Type(i), Sort.Type(j)) => i <= j
    case _                            => false
  }

  override def toString: String = this match {
    case Sort.Prop    => "Prop"
    case Sort.Type(0) => "Type"
    case Sort.Type(i) => s"Type$i"
  }
}

final case class Binder(name: String, ty: Term)

final case class MatchBranch(ctorName: String, fieldNames: List[String], body: Term) {
  def arity: Int = fieldNames.length
}

/**
 * Core De Bruijn-indexed terms of the Proof Samurai Trusted Kernel.
 *
 * Every term accepted by the kernel is guaranteed to obey:
 * - Universe stratification (Prop : Type0 : Type1 : ...)
 * - Strict positivity of inductive types
 * - Subsingleton elimination for Prop -> Type
 * - Structural decreasing guard condition for recursive Fix definitions
 * - Complete constructor coverage in Match expressions
 */
enum Term {
  case USort(sort: Sort)
  case Var(idx: Int)
  case Const(name: String)
  case Ind(name: String)
  case Ctor(indName: String, ctorName: String)
  case Pi(name: String, domain: Term, codomain: Term)
  case Lam(name: String, domain: Term, body: Term)
  case App(fn: Term, arg: Term)
  case Let(name: String, ty: Term, value: Term, body: Term)
  case Match(
    indName: String,
    params: List[Term],
    motive: Term,
    scrutinee: Term,
    branches: List[MatchBranch]
  )
  case Fix(name: String, recArgIdx: Int, ty: Term, body: Term)
}

object Term {
  def apps(fn: Term, args: List[Term]): Term =
    args.foldLeft(fn)(Term.App(_, _))

  /** Alpha-equivalence of De Bruijn terms (ignores display binder names). */
  def alphaEq(left: Term, right: Term): Boolean = (left, right) match {
    case (Term.USort(s1), Term.USort(s2))               => s1 == s2
    case (Term.Var(i1), Term.Var(i2))                   => i1 == i2
    case (Term.Const(c1), Term.Const(c2))               => c1 == c2
    case (Term.Ind(i1), Term.Ind(i2))                   => i1 == i2
    case (Term.Ctor(i1, c1), Term.Ctor(i2, c2))         => i1 == i2 && c1 == c2
    case (Term.Pi(_, d1, c1), Term.Pi(_, d2, c2))       => alphaEq(d1, d2) && alphaEq(c1, c2)
    case (Term.Lam(_, d1, b1), Term.Lam(_, d2, b2))     => alphaEq(d1, d2) && alphaEq(b1, b2)
    case (Term.App(f1, a1), Term.App(f2, a2))           => alphaEq(f1, f2) && alphaEq(a1, a2)
    case (Term.Let(_, t1, v1, b1), Term.Let(_, t2, v2, b2)) =>
      alphaEq(t1, t2) && alphaEq(v1, v2) && alphaEq(b1, b2)
    case (Term.Match(i1, ps1, m1, s1, brs1), Term.Match(i2, ps2, m2, s2, brs2)) =>
      i1 == i2 &&
        ps1.length == ps2.length && ps1.zip(ps2).forall { case (a, b) => alphaEq(a, b) } &&
        alphaEq(m1, m2) && alphaEq(s1, s2) &&
        brs1.length == brs2.length && brs1.zip(brs2).forall { case (b1, b2) =>
          b1.ctorName == b2.ctorName && b1.arity == b2.arity && alphaEq(b1.body, b2.body)
        }
    case (Term.Fix(_, r1, t1, b1), Term.Fix(_, r2, t2, b2)) =>
      r1 == r2 && alphaEq(t1, t2) && alphaEq(b1, b2)
    case _ => false
  }

  def splitApps(t: Term): (Term, List[Term]) = {
    def loop(cur: Term, acc: List[Term]): (Term, List[Term]) = cur match {
      case Term.App(f, a) => loop(f, a :: acc)
      case other          => (other, acc)
    }
    loop(t, Nil)
  }

  def pis(binders: List[Binder], body: Term): Term =
    binders.foldRight(body)((b, acc) => Term.Pi(b.name, b.ty, acc))

  def lams(binders: List[Binder], body: Term): Term =
    binders.foldRight(body)((b, acc) => Term.Lam(b.name, b.ty, acc))

  /** Shift all free variables with idx >= cutoff by delta. */
  def shift(t: Term, delta: Int, cutoff: Int = 0): Term = {
    if (delta == 0) return t
    t match {
      case Term.USort(_) | Term.Const(_) | Term.Ind(_) | Term.Ctor(_, _) => t
      case Term.Var(i) =>
        if (i >= cutoff) Term.Var(i + delta) else t
      case Term.Pi(n, dom, cod) =>
        Term.Pi(n, shift(dom, delta, cutoff), shift(cod, delta, cutoff + 1))
      case Term.Lam(n, dom, body) =>
        Term.Lam(n, shift(dom, delta, cutoff), shift(body, delta, cutoff + 1))
      case Term.App(f, a) =>
        Term.App(shift(f, delta, cutoff), shift(a, delta, cutoff))
      case Term.Let(n, ty, v, b) =>
        Term.Let(n, shift(ty, delta, cutoff), shift(v, delta, cutoff), shift(b, delta, cutoff + 1))
      case Term.Match(ind, params, motive, scrut, branches) =>
        Term.Match(
          ind,
          params.map(shift(_, delta, cutoff)),
          shift(motive, delta, cutoff),
          shift(scrut, delta, cutoff),
          branches.map(br => br.copy(body = shift(br.body, delta, cutoff + br.arity)))
        )
      case Term.Fix(n, recIdx, ty, body) =>
        Term.Fix(n, recIdx, shift(ty, delta, cutoff), shift(body, delta, cutoff + 1))
    }
  }

  /**
   * Substitute `replacement` for variable `idx` in `t`, shifting variables > idx down by 1.
   * Standard capture-avoiding De Bruijn substitution.
   */
  def subst(t: Term, idx: Int, replacement: Term): Term = t match {
    case Term.USort(_) | Term.Const(_) | Term.Ind(_) | Term.Ctor(_, _) => t
    case Term.Var(i) =>
      if (i == idx) shift(replacement, idx, 0)
      else if (i > idx) Term.Var(i - 1)
      else t
    case Term.Pi(n, dom, cod) =>
      Term.Pi(n, subst(dom, idx, replacement), subst(cod, idx + 1, replacement))
    case Term.Lam(n, dom, body) =>
      Term.Lam(n, subst(dom, idx, replacement), subst(body, idx + 1, replacement))
    case Term.App(f, a) =>
      Term.App(subst(f, idx, replacement), subst(a, idx, replacement))
    case Term.Let(n, ty, v, b) =>
      Term.Let(
        n,
        subst(ty, idx, replacement),
        subst(v, idx, replacement),
        subst(b, idx + 1, replacement)
      )
    case Term.Match(ind, params, motive, scrut, branches) =>
      Term.Match(
        ind,
        params.map(subst(_, idx, replacement)),
        subst(motive, idx, replacement),
        subst(scrut, idx, replacement),
        branches.map(br => br.copy(body = subst(br.body, idx + br.arity, replacement)))
      )
    case Term.Fix(n, recIdx, ty, body) =>
      Term.Fix(n, recIdx, subst(ty, idx, replacement), subst(body, idx + 1, replacement))
  }

  /** Substitute a list of arguments [a_0, a_1, ..., a_{k-1}] for variables [k-1, ..., 0]. */
  def substMany(t: Term, args: List[Term]): Term =
    substAtDepth(t, args, 0)

  /**
   * Substitute a list of arguments [a_0, ..., a_{k-1}] for variables [depth+k-1, ..., depth],
   * leaving variables < depth untouched and shifting variables >= depth+k down by k.
   */
  def substAtDepth(t: Term, args: List[Term], depth: Int): Term = {
    val k = args.length
    if (k == 0) return t
    t match {
      case Term.USort(_) | Term.Const(_) | Term.Ind(_) | Term.Ctor(_, _) => t
      case Term.Var(i) =>
        if (i < depth) t
        else if (i < depth + k) {
          val argIdx = k - 1 - (i - depth)
          shift(args(argIdx), depth, 0)
        } else {
          Term.Var(i - k)
        }
      case Term.Pi(n, dom, cod) =>
        Term.Pi(n, substAtDepth(dom, args, depth), substAtDepth(cod, args, depth + 1))
      case Term.Lam(n, dom, body) =>
        Term.Lam(n, substAtDepth(dom, args, depth), substAtDepth(body, args, depth + 1))
      case Term.App(f, a) =>
        Term.App(substAtDepth(f, args, depth), substAtDepth(a, args, depth))
      case Term.Let(n, ty, v, b) =>
        Term.Let(
          n,
          substAtDepth(ty, args, depth),
          substAtDepth(v, args, depth),
          substAtDepth(b, args, depth + 1)
        )
      case Term.Match(ind, params, motive, scrut, branches) =>
        Term.Match(
          ind,
          params.map(substAtDepth(_, args, depth)),
          substAtDepth(motive, args, depth),
          substAtDepth(scrut, args, depth),
          branches.map(br => br.copy(body = substAtDepth(br.body, args, depth + br.arity)))
        )
      case Term.Fix(n, recIdx, ty, body) =>
        Term.Fix(n, recIdx, substAtDepth(ty, args, depth), substAtDepth(body, args, depth + 1))
    }
  }

  def mentionsInd(t: Term, indName: String): Boolean = t match {
    case Term.Ind(n) => n == indName
    case Term.Ctor(n, _) => n == indName
    case Term.USort(_) | Term.Var(_) | Term.Const(_) => false
    case Term.Pi(_, d, c) => mentionsInd(d, indName) || mentionsInd(c, indName)
    case Term.Lam(_, d, b) => mentionsInd(d, indName) || mentionsInd(b, indName)
    case Term.App(f, a) => mentionsInd(f, indName) || mentionsInd(a, indName)
    case Term.Let(_, ty, v, b) => mentionsInd(ty, indName) || mentionsInd(v, indName) || mentionsInd(b, indName)
    case Term.Match(n, ps, m, s, brs) =>
      n == indName || ps.exists(mentionsInd(_, indName)) || mentionsInd(m, indName) ||
        mentionsInd(s, indName) || brs.exists(br => mentionsInd(br.body, indName))
    case Term.Fix(_, _, ty, b) => mentionsInd(ty, indName) || mentionsInd(b, indName)
  }

  def freeVarOccurs(t: Term, idx: Int): Boolean = t match {
    case Term.Var(i) => i == idx
    case Term.USort(_) | Term.Const(_) | Term.Ind(_) | Term.Ctor(_, _) => false
    case Term.Pi(_, d, c) => freeVarOccurs(d, idx) || freeVarOccurs(c, idx + 1)
    case Term.Lam(_, d, b) => freeVarOccurs(d, idx) || freeVarOccurs(b, idx + 1)
    case Term.App(f, a) => freeVarOccurs(f, idx) || freeVarOccurs(a, idx)
    case Term.Let(_, ty, v, b) => freeVarOccurs(ty, idx) || freeVarOccurs(v, idx) || freeVarOccurs(b, idx + 1)
    case Term.Match(_, ps, m, s, brs) =>
      ps.exists(freeVarOccurs(_, idx)) || freeVarOccurs(m, idx) || freeVarOccurs(s, idx) ||
        brs.exists(br => freeVarOccurs(br.body, idx + br.arity))
    case Term.Fix(_, _, ty, b) => freeVarOccurs(ty, idx) || freeVarOccurs(b, idx + 1)
  }

  def referencedConsts(t: Term): Set[String] = {
    val buf = Set.newBuilder[String]
    def go(cur: Term): Unit = cur match {
      case Term.Const(n) => buf += n
      case Term.USort(_) | Term.Var(_) | Term.Ind(_) | Term.Ctor(_, _) => ()
      case Term.Pi(_, d, c) => go(d); go(c)
      case Term.Lam(_, d, b) => go(d); go(b)
      case Term.App(f, a) => go(f); go(a)
      case Term.Let(_, ty, v, b) => go(ty); go(v); go(b)
      case Term.Match(_, ps, m, s, brs) =>
        ps.foreach(go); go(m); go(s); brs.foreach(br => go(br.body))
      case Term.Fix(_, _, ty, b) => go(ty); go(b)
    }
    go(t)
    buf.result()
  }
}
