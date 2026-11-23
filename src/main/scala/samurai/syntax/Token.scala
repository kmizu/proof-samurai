package samurai.syntax

import samurai.util.Span

enum TokenKind {
  // Keywords
  case KwModule
  case KwImport
  case KwEnum
  case KwCase
  case KwClass
  case KwDef
  case KwPartial
  case KwMutual
  case KwTerminationBy
  case KwDecreasingBy
  case KwVal
  case KwTheorem
  case KwLemma
  case KwAxiom
  case KwMatch
  case KwIf
  case KwElse
  case KwBy
  case KwCalc
  case KwForall
  case KwExists
  case KwReturning
  case KwSorry
  case KwTrue
  case KwFalse
  case KwProp
  case KwType

  // Identifiers & Literals
  case Ident(name: String)
  case TypeLevel(level: Int) // Type0, Type1, Type2, ...
  case IntLit(value: Int)
  case Hole(name: Option[String]) // ? or ?goalName
  case Directive(name: String) // #check, #eval, #print, #axioms
  case Annotation(name: String) // @simp, @hint, @decreasing, ...

  // Delimiters
  case LParen     // (
  case RParen     // )
  case LBrace     // {
  case RBrace     // }
  case LBracket   // [
  case RBracket   // ]
  case Comma      // ,
  case Semi       // ;
  case Dot        // .
  case Colon      // :
  case Underscore // _

  // Operators
  case FatArrow   // =>
  case ThinArrow  // ->
  case Eq         // =
  case EqEqEq     // ===
  case BangEqEq   // !==
  case EqEq       // ==
  case BangEq     // !=
  case LtEq       // <=
  case Lt         // <
  case GtEq       // >=
  case Gt         // >
  case LogicAnd   // /\
  case LogicOr    // \/
  case AmpAmp     // &&
  case PipePipe   // ||
  case ColonColon // ::
  case PlusPlus   // ++
  case Plus       // +
  case Minus      // -
  case Star       // *
  case Bang       // !
  case Tilde      // ~

  case Eof
}

final case class Token(kind: TokenKind, span: Span) {
  def text: String = kind.toString
}
