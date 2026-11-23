package samurai.elab

import scala.collection.mutable
import scala.util.boundary
import scala.util.boundary.break
import samurai.kernel.*

final case class MetaEntry(
  id: Int,
  creationDepth: Int,
  expectedType: Term,
  nameHint: Option[String],
  var solution: Option[Term] = None
)

/**
 * Metavariable store and pattern/first-order unification solver for the Elaborator.
 *
 * Metavariables are represented transiently as `Term.Const("$meta_<id>")` during elaboration,
 * and MUST be completely zonked (eliminated) before terms are passed to the Trusted Kernel.
 */
final class MetaContext {
  private var nextId: Int = 0
  private val entries: mutable.Map[Int, MetaEntry] = mutable.LinkedHashMap.empty

  def freshMeta(creationDepth: Int, expectedType: Term, nameHint: Option[String] = None): Term = {
    val id = nextId
    nextId += 1
    entries(id) = MetaEntry(id, creationDepth, expectedType, nameHint)
    Term.Const(MetaContext.metaName(id))
  }

  def isSolved(id: Int): Boolean =
    entries.get(id).exists(_.solution.isDefined)

  def snapshot(): Map[Int, Option[Term]] =
    entries.map { case (k, v) => k -> v.solution }.toMap

  def restore(snap: Map[Int, Option[Term]]): Unit = {
    for ((k, v) <- entries) {
      v.solution = snap.getOrElse(k, None)
    }
  }

  def unsolvedEntries: List[MetaEntry] =
    entries.values.filter(_.solution.isEmpty).toList

  def getEntry(id: Int): Option[MetaEntry] = entries.get(id)

  /** Replace all solved metavariables in `term` (at `currentDepth`) with their solutions. */
  def zonk(term: Term, currentDepth: Int): Term = term match {
    case Term.Const(name) =>
      MetaContext.parseMetaId(name) match {
        case Some(id) =>
          entries.get(id).flatMap(_.solution) match {
            case Some(sol) =>
              val shiftDelta = currentDepth - entries(id).creationDepth
              val shifted = if (shiftDelta >= 0) Term.shift(sol, shiftDelta) else sol
              zonk(shifted, currentDepth)
            case None => term
          }
        case None => term
      }
    case Term.USort(_) | Term.Var(_) | Term.Ind(_) | Term.Ctor(_, _) => term
    case Term.Pi(n, dom, cod) =>
      Term.Pi(n, zonk(dom, currentDepth), zonk(cod, currentDepth + 1))
    case Term.Lam(n, dom, body) =>
      Term.Lam(n, zonk(dom, currentDepth), zonk(body, currentDepth + 1))
    case Term.App(fn, arg) =>
      Term.App(zonk(fn, currentDepth), zonk(arg, currentDepth))
    case Term.Let(n, ty, value, body) =>
      Term.Let(n, zonk(ty, currentDepth), zonk(value, currentDepth), zonk(body, currentDepth + 1))
    case Term.Match(ind, params, motive, scrut, branches) =>
      Term.Match(
        ind,
        params.map(zonk(_, currentDepth)),
        zonk(motive, currentDepth),
        zonk(scrut, currentDepth),
        branches.map(br => br.copy(body = zonk(br.body, currentDepth + br.arity)))
      )
    case Term.Fix(n, recIdx, ty, body) =>
      Term.Fix(n, recIdx, zonk(ty, currentDepth), zonk(body, currentDepth + 1))
    case Term.MutualFix(defs, sel) =>
      val k = defs.length
      Term.MutualFix(
        defs.map(d => d.copy(ty = zonk(d.ty, currentDepth), body = zonk(d.body, currentDepth + k))),
        sel
      )
  }

  /**
   * Unify two terms in `(kernelEnv, localCtx)`, solving metavariables when possible.
   * When `allowSubtyping` is true, allows cumulative `Type(i) <= Type(j)`.
   */
  def unify(
    kernelEnv: KernelEnv,
    localCtx: LocalCtx,
    leftRaw: Term,
    rightRaw: Term,
    allowSubtyping: Boolean = false
  ): Either[String, Unit] = {
    val depth = localCtx.depth
    val leftZonked = zonk(leftRaw, depth)
    val rightZonked = zonk(rightRaw, depth)

    // Fast syntactic / same-head check BEFORE normalizing (preserves folded transparent definitions like Lt, blt, ble, length!)
    if (leftZonked == rightZonked) return Right(())

    val (lHead, lArgs) = Term.splitApps(leftZonked)
    val (rHead, rArgs) = Term.splitApps(rightZonked)
    def sameFoldedHead(a: Term, b: Term): Boolean = (a, b) match {
      case _ if a == b => true
      case (Term.Const(n), fx: Term.Fix) if fx.name == n =>
        kernelEnv.defs.get(n).exists(_.transparent) && {
          val f = new NbE.Fuel()
          val ev = NbE.buildEvalEnv(kernelEnv, localCtx, f)
          NbE.areConvertible(kernelEnv, depth, NbE.evaluate(kernelEnv, ev, a, f), NbE.evaluate(kernelEnv, ev, b, f), f)
        }
      case (fx: Term.Fix, Term.Const(n)) if fx.name == n =>
        kernelEnv.defs.get(n).exists(_.transparent) && {
          val f = new NbE.Fuel()
          val ev = NbE.buildEvalEnv(kernelEnv, localCtx, f)
          NbE.areConvertible(kernelEnv, depth, NbE.evaluate(kernelEnv, ev, a, f), NbE.evaluate(kernelEnv, ev, b, f), f)
        }
      case (Term.Const(n), mf: Term.MutualFix) if mf.selectedIndex >= 0 && mf.selectedIndex < mf.defs.length && mf.defs(mf.selectedIndex).name == n =>
        kernelEnv.defs.get(n).exists(_.transparent) && {
          val f = new NbE.Fuel()
          val ev = NbE.buildEvalEnv(kernelEnv, localCtx, f)
          NbE.areConvertible(kernelEnv, depth, NbE.evaluate(kernelEnv, ev, a, f), NbE.evaluate(kernelEnv, ev, b, f), f)
        }
      case (mf: Term.MutualFix, Term.Const(n)) if mf.selectedIndex >= 0 && mf.selectedIndex < mf.defs.length && mf.defs(mf.selectedIndex).name == n =>
        kernelEnv.defs.get(n).exists(_.transparent) && {
          val f = new NbE.Fuel()
          val ev = NbE.buildEvalEnv(kernelEnv, localCtx, f)
          NbE.areConvertible(kernelEnv, depth, NbE.evaluate(kernelEnv, ev, a, f), NbE.evaluate(kernelEnv, ev, b, f), f)
        }
      case _ => false
    }
    if (lArgs.nonEmpty && lArgs.length == rArgs.length && sameFoldedHead(lHead, rHead)) {
      val snap = snapshot()
      val allMatched = boundary {
        for ((la, ra) <- lArgs.zip(rArgs)) {
          unify(kernelEnv, localCtx, la, ra, allowSubtyping = false) match {
            case Right(()) => ()
            case Left(_)   => break(false)
          }
        }
        true
      }
      if (allMatched) return Right(())
      else restore(snap)
    }

    val fuel = new NbE.Fuel()
    val evalEnv = NbE.buildEvalEnv(kernelEnv, localCtx, fuel)
    val leftVal = NbE.evaluate(kernelEnv, evalEnv, leftZonked, fuel)
    val rightVal = NbE.evaluate(kernelEnv, evalEnv, rightZonked, fuel)

    unifyValues(kernelEnv, depth, leftVal, rightVal, allowSubtyping, fuel)
  }

  private def unifyValues(
    kernelEnv: KernelEnv,
    depth: Int,
    left: Value,
    right: Value,
    allowSubtyping: Boolean,
    fuel: NbE.Fuel
  ): Either[String, Unit] = {
    // Check if either side is a bare unsolved metavariable
    (left, right) match {
      case (Value.VNeutral(NeutralHead.NConst(metaName), Nil), other) if MetaContext.isMeta(metaName) =>
        val id = MetaContext.parseMetaId(metaName).get
        entries.get(id).flatMap(_.solution) match {
          case Some(_) =>
            // Already solved in meantime; re-check via quoted
            val qLeft = zonk(Term.Const(metaName), depth)
            val qRight = zonk(NbE.quote(kernelEnv, depth, other, fuel), depth)
            unifyQuoted(kernelEnv, depth, qLeft, qRight, allowSubtyping, fuel)
          case None =>
            solveMeta(id, depth, NbE.quote(kernelEnv, depth, other, fuel))
        }

      case (other, Value.VNeutral(NeutralHead.NConst(metaName), Nil)) if MetaContext.isMeta(metaName) =>
        val id = MetaContext.parseMetaId(metaName).get
        entries.get(id).flatMap(_.solution) match {
          case Some(_) =>
            val qLeft = zonk(NbE.quote(kernelEnv, depth, other, fuel), depth)
            val qRight = zonk(Term.Const(metaName), depth)
            unifyQuoted(kernelEnv, depth, qLeft, qRight, allowSubtyping, fuel)
          case None =>
            solveMeta(id, depth, NbE.quote(kernelEnv, depth, other, fuel))
        }

      case (Value.VSort(s1), Value.VSort(s2)) =>
        if (s1 == s2 || (allowSubtyping && s1.leq(s2))) Right(())
        else Left(s"Sort mismatch: $s1 vs $s2")

      case (Value.VPi(_, dom1, cod1), Value.VPi(_, dom2, cod2)) =>
        for {
          _ <- unifyValues(kernelEnv, depth, dom1, dom2, allowSubtyping = false, fuel)
          freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
          _ <- unifyValues(
            kernelEnv,
            depth + 1,
            NbE.applyClosure(kernelEnv, cod1, freshVar, fuel),
            NbE.applyClosure(kernelEnv, cod2, freshVar, fuel),
            allowSubtyping = allowSubtyping,
            fuel
          )
        } yield ()

      case (Value.VLam(_, _, body1), Value.VLam(_, _, body2)) =>
        val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
        unifyValues(
          kernelEnv,
          depth + 1,
          NbE.applyClosure(kernelEnv, body1, freshVar, fuel),
          NbE.applyClosure(kernelEnv, body2, freshVar, fuel),
          allowSubtyping = false,
          fuel
        )

      case (Value.VLam(_, _, body1), other) =>
        val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
        unifyValues(
          kernelEnv,
          depth + 1,
          NbE.applyClosure(kernelEnv, body1, freshVar, fuel),
          NbE.applyValue(kernelEnv, other, freshVar, fuel),
          allowSubtyping = false,
          fuel
        )

      case (other, Value.VLam(_, _, body2)) =>
        val freshVar = Value.VNeutral(NeutralHead.NVar(depth), Nil)
        unifyValues(
          kernelEnv,
          depth + 1,
          NbE.applyValue(kernelEnv, other, freshVar, fuel),
          NbE.applyClosure(kernelEnv, body2, freshVar, fuel),
          allowSubtyping = false,
          fuel
        )

      case (Value.VInd(n1, args1), Value.VInd(n2, args2)) if n1 == n2 && args1.length == args2.length =>
        unifyValueLists(kernelEnv, depth, args1, args2, fuel)

      case (Value.VCtor(i1, c1, args1), Value.VCtor(i2, c2, args2))
          if i1 == i2 && c1 == c2 && args1.length == args2.length =>
        if (kernelEnv.inductives.get(i1).exists(_.sort == Sort.Prop)) Right(())
        else unifyValueLists(kernelEnv, depth, args1, args2, fuel)

      case (Value.VNeutral(h1, sp1), Value.VNeutral(h2, sp2))
          if sp1.length == sp2.length && sameHead(kernelEnv, depth, h1, h2, fuel) =>
        unifySpines(kernelEnv, depth, sp1, sp2, fuel) match {
          case Right(()) => Right(())
          case Left(innerErr) =>
            if (NbE.areConvertible(kernelEnv, depth, left, right, fuel)) Right(())
            else Left(s"Neutral spine mismatch: $innerErr")
        }

      case _ =>
        if (
          if (allowSubtyping) NbE.isSubtype(kernelEnv, depth, left, right, fuel)
          else NbE.areConvertible(kernelEnv, depth, left, right, fuel)
        ) Right(())
        else {
          val q1 = NbE.quote(kernelEnv, depth, left, fuel)
          val q2 = NbE.quote(kernelEnv, depth, right, fuel)
          Left(s"Cannot unify '${Pretty.show(q1)}' with '${Pretty.show(q2)}'")
        }
    }
  }

  private def unifyQuoted(
    kernelEnv: KernelEnv,
    depth: Int,
    left: Term,
    right: Term,
    allowSubtyping: Boolean,
    fuel: NbE.Fuel
  ): Either[String, Unit] = {
    val evalEnv = (0 until depth).toList.reverse.map(lvl => Value.VNeutral(NeutralHead.NVar(lvl), Nil))
    val v1 = NbE.evaluate(kernelEnv, evalEnv, left, fuel)
    val v2 = NbE.evaluate(kernelEnv, evalEnv, right, fuel)
    unifyValues(kernelEnv, depth, v1, v2, allowSubtyping, fuel)
  }

  private def sameHead(
    kernelEnv: KernelEnv,
    depth: Int,
    h1: NeutralHead,
    h2: NeutralHead,
    fuel: NbE.Fuel
  ): Boolean = (h1, h2) match {
    case (NeutralHead.NVar(a), NeutralHead.NVar(b))     => a == b
    case (NeutralHead.NConst(a), NeutralHead.NConst(b)) => a == b
    case (NeutralHead.NFix(_, i1, _, _), NeutralHead.NFix(_, i2, _, _)) =>
      i1 == i2 && NbE.areConvertible(kernelEnv, depth, Value.VNeutral(h1, Nil), Value.VNeutral(h2, Nil), fuel)
    case (NeutralHead.NMutualFix(_, s1), NeutralHead.NMutualFix(_, s2)) =>
      s1 == s2 && NbE.areConvertible(kernelEnv, depth, Value.VNeutral(h1, Nil), Value.VNeutral(h2, Nil), fuel)
    case _ => false
  }

  private def unifyValueLists(
    kernelEnv: KernelEnv,
    depth: Int,
    lefts: List[Value],
    rights: List[Value],
    fuel: NbE.Fuel
  ): Either[String, Unit] = boundary {
    for ((l, r) <- lefts.zip(rights)) {
      unifyValues(kernelEnv, depth, l, r, allowSubtyping = false, fuel) match {
        case Left(err) => break(Left(err))
        case Right(()) => ()
      }
    }
    Right(())
  }

  private def unifySpines(
    kernelEnv: KernelEnv,
    depth: Int,
    sp1: List[Eliminator],
    sp2: List[Eliminator],
    fuel: NbE.Fuel
  ): Either[String, Unit] = boundary {
    for ((e1, e2) <- sp1.zip(sp2)) {
      (e1, e2) match {
        case (Eliminator.EApp(a1), Eliminator.EApp(a2)) =>
          unifyValues(kernelEnv, depth, a1, a2, allowSubtyping = false, fuel) match {
            case Left(err) => break(Left(err))
            case Right(()) => ()
          }
        case _ =>
          break(Left("Cannot unify match eliminators"))
      }
    }
    Right(())
  }

  private def solveMeta(id: Int, currentDepth: Int, rhsRaw: Term): Either[String, Unit] = {
    val rhs = zonk(rhsRaw, currentDepth)
    val metaName = MetaContext.metaName(id)
    if (rhs == Term.Const(metaName)) return Right(())
    if (Term.referencedConsts(rhs).contains(metaName)) {
      return Left(s"Occurs check failed for metavariable ?$id in '${Pretty.show(rhs)}'")
    }
    val entry = entries(id)
    val delta = currentDepth - entry.creationDepth
    if (delta < 0) {
      return Left(s"Metavariable ?$id escaped its scope")
    }
    if (delta > 0) {
      // Ensure rhs does not reference local variables bound inside `delta` (indices 0 .. delta - 1)
      if ((0 until delta).exists(i => Term.freeVarOccurs(rhs, i))) {
        return Left(s"Scope escape: cannot solve ?$id with term '${Pretty.show(rhs)}' referencing inner binders")
      }
      entry.solution = Some(Term.shift(rhs, -delta, delta))
    } else {
      entry.solution = Some(rhs)
    }
    Right(())
  }
}

object MetaContext {
  private val Prefix = "$meta_"

  def metaName(id: Int): String = s"$Prefix$id"

  def isMeta(name: String): Boolean = name.startsWith(Prefix)

  def parseMetaId(name: String): Option[Int] =
    if (name.startsWith(Prefix)) name.substring(Prefix.length).toIntOption
    else None
}
