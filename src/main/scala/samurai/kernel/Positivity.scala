package samurai.kernel

import scala.util.boundary
import scala.util.boundary.break

/**
 * Strict positivity checker for inductive type declarations.
 *
 * Guarantees that no inductive type `I` can occur in a negative position (to the left of
 * an arrow `->`), nor inside an index or arbitrary application argument, preventing
 * Curry's paradox and non-terminating inhabitants of False.
 */
object Positivity {

  /**
   * Verify that all constructors of `inductive` satisfy strict positivity.
   * Normalizes every field type with NbE (expanding transparent defs, beta, iota, zeta)
   * so hidden negative occurrences through higher-order type aliases are always caught.
   */
  def checkInductive(kernelEnv: KernelEnv, inductive: IndEntry): Either[String, Unit] = boundary {
    val indName = inductive.name
    val paramCtx = LocalCtx.empty.pushBinders(inductive.params)

    for (constructor <- inductive.constructors) {
      var fieldCtx = paramCtx
      for (field <- constructor.fields) {
        val normalizedFieldType = NbE.normalize(kernelEnv, fieldCtx, field.ty)
        checkStrictlyPositive(indName, normalizedFieldType) match {
          case Left(reason) =>
            break(
              Left(
                s"Strict positivity violation in constructor '${indName}.${constructor.name}', " +
                  s"field '${field.name}': $reason"
              )
            )
          case Right(()) => ()
        }
        fieldCtx = fieldCtx.push(field.name, field.ty)
      }
      for ((resultIndex, position) <- constructor.resultIndices.zipWithIndex) {
        val normalizedIndex = NbE.normalize(kernelEnv, fieldCtx, resultIndex)
        if (Term.mentionsInd(normalizedIndex, indName)) {
          break(
            Left(
              s"Inductive type '$indName' cannot appear in result index #$position of constructor '${indName}.${constructor.name}'"
            )
          )
        }
      }
    }
    Right(())
  }

  /**
   * A type T is strictly positive in `indName` iff:
   * 1. `indName` does not occur in T at all; OR
   * 2. T is `Pi(x: A, B)` where `indName` does NOT occur in A, and B is strictly positive in `indName`; OR
   * 3. T is `Ind(indName)(args...)` where `indName` does NOT occur in any of `args`.
   */
  def checkStrictlyPositive(indName: String, fieldType: Term): Either[String, Unit] = {
    if (!Term.mentionsInd(fieldType, indName)) {
      return Right(())
    }
    fieldType match {
      case Term.Pi(_, domain, codomain) =>
        if (Term.mentionsInd(domain, indName)) {
          Left(s"inductive type '$indName' occurs in a negative position (to the left of '=>')")
        } else {
          checkStrictlyPositive(indName, codomain)
        }

      case other =>
        val (head, args) = Term.splitApps(other)
        head match {
          case Term.Ind(name) if name == indName =>
            if (args.exists(Term.mentionsInd(_, indName))) {
              Left(s"inductive type '$indName' occurs inside its own type arguments")
            } else {
              Right(())
            }
          case _ =>
            Left(s"inductive type '$indName' occurs in a non-strictly-positive position inside '$other'")
        }
    }
  }
}
