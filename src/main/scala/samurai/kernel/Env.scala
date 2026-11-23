package samurai.kernel

final case class CtorEntry(
  name: String,
  fields: List[Binder],
  resultIndices: List[Term],
  fieldIsProp: List[Boolean] = Nil
) {
  def arity: Int = fields.length
}

final case class IndEntry(
  name: String,
  params: List[Binder],
  indices: List[Binder],
  sort: Sort,
  constructors: List[CtorEntry],
  isSubsingleton: Boolean = false
) {
  def numParams: Int = params.length
  def numIndices: Int = indices.length

  def ctor(ctorName: String): Option[CtorEntry] =
    constructors.find(_.name == ctorName)

  /** Full type of the inductive type former: Pi(params, Pi(indices, Sort(sort))) */
  def fullType: Term =
    Term.pis(params, Term.pis(indices, Term.USort(sort)))

  /** Full type of constructor: Pi(params, Pi(fields, Ind(name, paramsVars ++ resultIndices))) */
  def ctorType(c: CtorEntry): Term = {
    val p = numParams
    val r = c.arity
    val paramVars = (0 until p).toList.map(j => Term.Var(r + p - 1 - j))
    val ret = Term.apps(Term.Ind(name), paramVars ++ c.resultIndices)
    Term.pis(params, Term.pis(c.fields, ret))
  }

  /** Instantiate the index binders with concrete `paramVals` in the current scope. */
  def instantiateIndices(paramVals: List[Term]): List[Binder] =
    indices.zipWithIndex.map { case (b, j) =>
      Binder(b.name, Term.substAtDepth(b.ty, paramVals, j))
    }

  /** Instantiate constructor field binders with concrete `paramVals` in the current scope. */
  def instantiateFields(c: CtorEntry, paramVals: List[Term]): List[Binder] =
    c.fields.zipWithIndex.map { case (b, k) =>
      Binder(b.name, Term.substAtDepth(b.ty, paramVals, k))
    }

  /** Instantiate constructor result indices under `ctx ++ instFields`. */
  def instantiateResultIndices(c: CtorEntry, paramVals: List[Term]): List[Term] = {
    val r = c.arity
    c.resultIndices.map(ri => Term.substAtDepth(ri, paramVals, r))
  }

  /** Expected type of a match motive: Pi(indices[paramVals], Pi(s: Ind(paramVals, idxVars), targetSort)) */
  def motiveType(paramVals: List[Term], targetSort: Sort): Term = {
    val instIdx = instantiateIndices(paramVals)
    val m = numIndices
    val idxVars = (0 until m).toList.map(j => Term.Var(m - 1 - j))
    val scrutTy = Term.apps(Term.Ind(name), paramVals.map(Term.shift(_, m)) ++ idxVars)
    Term.pis(instIdx, Term.Pi("_scrut", scrutTy, Term.USort(targetSort)))
  }

  /**
   * Expected type of a match branch body under `ctx ++ instantiateFields(c, paramVals)`:
   * `shift(motive, r)(resultIndices[paramVals], Ctor(name, c.name, shift(paramVals, r) ++ fieldVars))`
   */
  def branchBodyType(c: CtorEntry, paramVals: List[Term], motive: Term): Term = {
    val r = c.arity
    val instResIdx = instantiateResultIndices(c, paramVals)
    val fieldVars = (0 until r).toList.map(k => Term.Var(r - 1 - k))
    val ctorApp = Term.apps(
      Term.Ctor(name, c.name),
      paramVals.map(Term.shift(_, r)) ++ fieldVars
    )
    Term.apps(Term.shift(motive, r), instResIdx :+ ctorApp)
  }
}

final case class DefEntry(
  name: String,
  ty: Term,
  body: Term,
  transparent: Boolean,
  isTheorem: Boolean,
  axiomsUsed: Set[String]
)

final case class AxiomEntry(
  name: String,
  ty: Term
)

/**
 * Immutable trusted kernel environment.
 * Entries should ONLY be added via TypeChecker.checkInductive / checkDef / checkAxiom.
 */
final case class KernelEnv(
  inductives: Map[String, IndEntry] = Map.empty,
  defs: Map[String, DefEntry] = Map.empty,
  axioms: Map[String, AxiomEntry] = Map.empty,
  declOrder: List[String] = Nil
) {
  def contains(name: String): Boolean =
    inductives.contains(name) || defs.contains(name) || axioms.contains(name)

  def addInductive(ind: IndEntry): KernelEnv =
    copy(inductives = inductives + (ind.name -> ind), declOrder = declOrder :+ ind.name)

  def addDef(entry: DefEntry): KernelEnv =
    copy(defs = defs + (entry.name -> entry), declOrder = declOrder :+ entry.name)

  def addAxiom(entry: AxiomEntry): KernelEnv =
    copy(axioms = axioms + (entry.name -> entry), declOrder = declOrder :+ entry.name)

  def lookupConstType(name: String): Option[Term] =
    defs.get(name).map(_.ty).orElse(axioms.get(name).map(_.ty))

  def collectAxioms(t: Term): Set[String] = {
    val refs = Term.referencedConsts(t)
    refs.flatMap { c =>
      if (axioms.contains(c)) Set(c)
      else defs.get(c).map(_.axiomsUsed).getOrElse(Set.empty)
    }
  }

  def allAxiomsUsed: Set[String] = axioms.keySet
}

object KernelEnv {
  val empty: KernelEnv = KernelEnv()
}

final case class LocalEntry(name: String, ty: Term, value: Option[Term] = None)

/**
 * Local typing context (De Bruijn stack: index 0 is the head of `entries`).
 */
final case class LocalCtx(entries: List[LocalEntry] = Nil) {
  def depth: Int = entries.length

  def push(name: String, ty: Term, value: Option[Term] = None): LocalCtx =
    LocalCtx(LocalEntry(name, ty, value) :: entries)

  def pushBinders(binders: List[Binder]): LocalCtx =
    binders.foldLeft(this)((ctx, b) => ctx.push(b.name, b.ty))

  /** Look up type of De Bruijn index `idx`, shifted into the current context. */
  def lookupType(idx: Int): Option[Term] =
    if (idx < 0 || idx >= entries.length) None
    else Some(Term.shift(entries(idx).ty, idx + 1))

  /** Look up optional let-bound value of De Bruijn index `idx`, shifted into current context. */
  def lookupValue(idx: Int): Option[Term] =
    if (idx < 0 || idx >= entries.length) None
    else entries(idx).value.map(Term.shift(_, idx + 1))

  def names: List[String] = entries.map(_.name)
}

object LocalCtx {
  val empty: LocalCtx = LocalCtx()
}
