package samurai.syntax

import samurai.util.Span

final case class SurfaceAnnotation(name: String, args: List[SurfaceExpr], span: Span)

final case class ParamBinder(name: String, typeAnnotation: Option[SurfaceExpr], span: Span)

final case class EnumCaseDecl(
  name: String,
  fields: List[ParamBinder],
  resultType: Option[SurfaceExpr],
  span: Span
)

enum ImportSelector {
  case Wildcard
  case Single(name: String)
  case Multiple(names: List[String])
}

enum TopDecl {
  case ModuleDecl(name: String, declarations: List[TopDecl], span: Span)
  case ImportDecl(moduleName: String, selector: ImportSelector, span: Span)
  case EnumDecl(
    annotations: List[SurfaceAnnotation],
    name: String,
    typeParams: List[ParamBinder],
    indexParams: List[ParamBinder],
    sortAnnotation: Option[SurfaceExpr],
    cases: List[EnumCaseDecl],
    span: Span
  )
  case CaseClassDecl(
    annotations: List[SurfaceAnnotation],
    name: String,
    typeParams: List[ParamBinder],
    fields: List[ParamBinder],
    sortAnnotation: Option[SurfaceExpr],
    span: Span
  )
  case DefDecl(
    annotations: List[SurfaceAnnotation],
    name: String,
    typeParams: List[ParamBinder],
    valueParams: List[ParamBinder],
    returnType: Option[SurfaceExpr],
    body: SurfaceExpr,
    isTheorem: Boolean,
    span: Span
  )
  case ValDecl(
    annotations: List[SurfaceAnnotation],
    name: String,
    typeAnnotation: Option[SurfaceExpr],
    value: SurfaceExpr,
    span: Span
  )
  case AxiomDecl(
    annotations: List[SurfaceAnnotation],
    name: String,
    typeParams: List[ParamBinder],
    valueParams: List[ParamBinder],
    returnType: SurfaceExpr,
    span: Span
  )
  case DirectiveDecl(name: String, target: SurfaceExpr, span: Span)
}

enum Pattern {
  def span: Span
  case Wildcard(span: Span)
  case Var(name: String, span: Span)
  case Ctor(qualifier: Option[String], name: String, args: List[Pattern], span: Span)
  case NatLit(value: Int, span: Span)
  case BoolLit(value: Boolean, span: Span)
  case Cons(head: Pattern, tail: Pattern, span: Span)
  case ListLit(elements: List[Pattern], span: Span)
}

final case class MatchCase(pattern: Pattern, body: SurfaceExpr, span: Span)

final case class CalcStep(rhs: SurfaceExpr, proof: SurfaceExpr, span: Span)

enum BlockStatement {
  case LocalVal(name: String, typeAnnotation: Option[SurfaceExpr], value: SurfaceExpr, span: Span)
  case ExprStmt(expr: SurfaceExpr)
}

enum SurfaceExpr {
  def span: Span

  case SortExpr(isProp: Boolean, level: Int, span: Span)
  case VarExpr(name: String, span: Span)
  case IntLitExpr(value: Int, span: Span)
  case BoolLitExpr(value: Boolean, span: Span)
  case ListLitExpr(elements: List[SurfaceExpr], span: Span)
  case CalcExpr(start: SurfaceExpr, steps: List[CalcStep], span: Span)
  case HoleExpr(name: Option[String], span: Span)
  case SorryExpr(span: Span)
  case SelectExpr(receiver: SurfaceExpr, member: String, span: Span)
  case TypeAppExpr(callee: SurfaceExpr, typeArgs: List[SurfaceExpr], span: Span)
  case CallExpr(callee: SurfaceExpr, args: List[SurfaceExpr], span: Span)
  case UnaryOpExpr(op: String, operand: SurfaceExpr, span: Span)
  case BinaryOpExpr(op: String, left: SurfaceExpr, right: SurfaceExpr, span: Span)

  /**
   * Arrow expression `(x: A, y: B) => body` or `A => B`.
   * `alwaysPi` is true for `forall (...) => ...` and `(...) -> ...`.
   * Otherwise elaborated bidirectionally: Pi in type position, Lam in term position!
   */
  case ArrowExpr(
    params: List[ParamBinder],
    body: SurfaceExpr,
    alwaysPi: Boolean,
    span: Span
  )

  case ExistsExpr(params: List[ParamBinder], body: SurfaceExpr, span: Span)
  case BlockExpr(statements: List[BlockStatement], result: SurfaceExpr, span: Span)
  case IfExpr(condition: SurfaceExpr, thenBranch: SurfaceExpr, elseBranch: SurfaceExpr, span: Span)
  case MatchExpr(
    scrutinee: SurfaceExpr,
    motive: Option[SurfaceExpr],
    cases: List[MatchCase],
    span: Span
  )
  case TacticBlockExpr(tactics: List[TacticStmt], span: Span)
  case AscribeExpr(expr: SurfaceExpr, expectedType: SurfaceExpr, span: Span)
}

final case class TacticCaseBranch(
  ctorName: String,
  binders: List[String],
  body: List[TacticStmt],
  span: Span
)

enum TacticStmt {
  def span: Span

  case Intro(names: List[String], span: Span)
  case Exact(term: SurfaceExpr, span: Span)
  case Apply(term: SurfaceExpr, span: Span)
  case Refl(span: Span)
  case Symmetry(span: Span)
  case Trans(middle: SurfaceExpr, span: Span)
  case Rewrite(lemmas: List[SurfaceExpr], reverse: Boolean, span: Span)
  case Congr(span: Span)
  case Induction(target: SurfaceExpr, cases: List[TacticCaseBranch], span: Span)
  case Cases(target: SurfaceExpr, eqName: Option[String], cases: List[TacticCaseBranch], span: Span)
  case Revert(names: List[String], span: Span)
  case Exfalso(span: Span)
  case Subst(hypothesis: SurfaceExpr, span: Span)
  case Specialize(hypName: String, args: List[SurfaceExpr], span: Span)
  case Split(span: Span)
  case LeftBranch(span: Span)
  case RightBranch(span: Span)
  case ExistsWitness(witness: SurfaceExpr, span: Span)
  case Contradiction(span: Span)
  case Discriminate(hypothesis: Option[SurfaceExpr], span: Span)
  case Injection(hypothesis: SurfaceExpr, names: List[String], span: Span)
  case Have(name: String, propType: SurfaceExpr, proof: List[TacticStmt], span: Span)
  case Unfold(name: String, span: Span)
  case Simp(extraLemmas: List[SurfaceExpr], includeLocalHyps: Boolean, span: Span)
  case Arith(span: Span)
  case Trivial(span: Span)
  case Auto(maxDepth: Option[Int], span: Span)
  case Decide(span: Span)
  case Assumption(span: Span)
  case Sorry(span: Span)
  case Hole(name: Option[String], span: Span)
}
