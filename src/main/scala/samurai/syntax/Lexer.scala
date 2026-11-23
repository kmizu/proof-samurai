package samurai.syntax

import samurai.util.{Diagnostic, Pos, Span}

/**
 * Completely whitespace- and indentation-insensitive lexer for Proof Samurai's
 * Scala 3 brace-delimited syntax.
 */
object Lexer {

  private val Keywords: Map[String, TokenKind] = Map(
    "module"    -> TokenKind.KwModule,
    "import"    -> TokenKind.KwImport,
    "enum"      -> TokenKind.KwEnum,
    "case"      -> TokenKind.KwCase,
    "class"     -> TokenKind.KwClass,
    "def"       -> TokenKind.KwDef,
    "val"       -> TokenKind.KwVal,
    "theorem"   -> TokenKind.KwTheorem,
    "lemma"     -> TokenKind.KwLemma,
    "axiom"     -> TokenKind.KwAxiom,
    "match"     -> TokenKind.KwMatch,
    "if"        -> TokenKind.KwIf,
    "else"      -> TokenKind.KwElse,
    "by"        -> TokenKind.KwBy,
    "calc"      -> TokenKind.KwCalc,
    "forall"    -> TokenKind.KwForall,
    "exists"    -> TokenKind.KwExists,
    "returning" -> TokenKind.KwReturning,
    "sorry"     -> TokenKind.KwSorry,
    "true"      -> TokenKind.KwTrue,
    "false"     -> TokenKind.KwFalse,
    "Prop"      -> TokenKind.KwProp,
    "Type"      -> TokenKind.KwType
  )

  def tokenize(file: String, source: String): Either[Diagnostic, Vector[Token]] = {
    val tokens = Vector.newBuilder[Token]
    val length = source.length
    var offset = 0
    var line = 1
    var col = 1

    def currentPos: Pos = Pos(line, col, offset)

    def advance(): Char = {
      val ch = source.charAt(offset)
      offset += 1
      if (ch == '\n') {
        line += 1
        col = 1
      } else {
        col += 1
      }
      ch
    }

    def peek(delta: Int = 0): Char =
      if (offset + delta < length) source.charAt(offset + delta) else '\u0000'

    def matches(str: String): Boolean =
      source.startsWith(str, offset)

    def skipWhitespaceAndComments(): Either[Diagnostic, Unit] = {
      var continuing = true
      while (continuing && offset < length) {
        val ch = peek()
        if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n') {
          advance()
        } else if (matches("//")) {
          while (offset < length && peek() != '\n') advance()
        } else if (matches("/*")) {
          val commentStart = currentPos
          advance(); advance()
          var nesting = 1
          while (offset < length && nesting > 0) {
            if (matches("/*")) {
              advance(); advance(); nesting += 1
            } else if (matches("*/")) {
              advance(); advance(); nesting -= 1
            } else {
              advance()
            }
          }
          if (nesting > 0) {
            return Left(
              Diagnostic(
                Diagnostic.Severity.Error,
                "L001",
                "Unterminated block comment",
                Span(file, commentStart, currentPos)
              )
            )
          }
        } else {
          continuing = false
        }
      }
      Right(())
    }

    def isIdentStart(ch: Char): Boolean = ch.isLetter || ch == '_'
    def isIdentPart(ch: Char): Boolean = ch.isLetterOrDigit || ch == '_' || ch == '\''

    while (offset < length) {
      skipWhitespaceAndComments() match {
        case Left(err) => return Left(err)
        case Right(()) => ()
      }
      if (offset < length) {
        val startPos = currentPos
        val ch = peek()

        val kindOpt: Either[Diagnostic, TokenKind] =
          if (matches("===")) { advance(); advance(); advance(); Right(TokenKind.EqEqEq) }
          else if (matches("!==")) { advance(); advance(); advance(); Right(TokenKind.BangEqEq) }
          else if (matches("=>")) { advance(); advance(); Right(TokenKind.FatArrow) }
          else if (matches("->")) { advance(); advance(); Right(TokenKind.ThinArrow) }
          else if (matches("==")) { advance(); advance(); Right(TokenKind.EqEq) }
          else if (matches("!=")) { advance(); advance(); Right(TokenKind.BangEq) }
          else if (matches("<=")) { advance(); advance(); Right(TokenKind.LtEq) }
          else if (matches(">=")) { advance(); advance(); Right(TokenKind.GtEq) }
          else if (matches("/\\")) { advance(); advance(); Right(TokenKind.LogicAnd) }
          else if (matches("\\/")) { advance(); advance(); Right(TokenKind.LogicOr) }
          else if (matches("&&")) { advance(); advance(); Right(TokenKind.AmpAmp) }
          else if (matches("||")) { advance(); advance(); Right(TokenKind.PipePipe) }
          else if (matches("::")) { advance(); advance(); Right(TokenKind.ColonColon) }
          else if (matches("++")) { advance(); advance(); Right(TokenKind.PlusPlus) }
          else if (ch == '(') { advance(); Right(TokenKind.LParen) }
          else if (ch == ')') { advance(); Right(TokenKind.RParen) }
          else if (ch == '{') { advance(); Right(TokenKind.LBrace) }
          else if (ch == '}') { advance(); Right(TokenKind.RBrace) }
          else if (ch == '[') { advance(); Right(TokenKind.LBracket) }
          else if (ch == ']') { advance(); Right(TokenKind.RBracket) }
          else if (ch == ',') { advance(); Right(TokenKind.Comma) }
          else if (ch == ';') { advance(); Right(TokenKind.Semi) }
          else if (ch == '.') { advance(); Right(TokenKind.Dot) }
          else if (ch == ':') { advance(); Right(TokenKind.Colon) }
          else if (ch == '=') { advance(); Right(TokenKind.Eq) }
          else if (ch == '<') { advance(); Right(TokenKind.Lt) }
          else if (ch == '>') { advance(); Right(TokenKind.Gt) }
          else if (ch == '+') { advance(); Right(TokenKind.Plus) }
          else if (ch == '-') { advance(); Right(TokenKind.Minus) }
          else if (ch == '*') { advance(); Right(TokenKind.Star) }
          else if (ch == '!') { advance(); Right(TokenKind.Bang) }
          else if (ch == '~') { advance(); Right(TokenKind.Tilde) }
          else if (ch == '?') {
            advance()
            if (offset < length && isIdentStart(peek())) {
              val sb = new StringBuilder
              while (offset < length && isIdentPart(peek())) sb.append(advance())
              Right(TokenKind.Hole(Some(sb.toString)))
            } else {
              Right(TokenKind.Hole(None))
            }
          } else if (ch == '#') {
            advance()
            val sb = new StringBuilder
            while (offset < length && isIdentPart(peek())) sb.append(advance())
            if (sb.isEmpty) {
              Left(Diagnostic(Diagnostic.Severity.Error, "L002", "Expected directive name after '#'", Span(file, startPos, currentPos)))
            } else {
              Right(TokenKind.Directive(sb.toString))
            }
          } else if (ch == '@') {
            advance()
            val sb = new StringBuilder
            while (offset < length && isIdentPart(peek())) sb.append(advance())
            if (sb.isEmpty) {
              Left(Diagnostic(Diagnostic.Severity.Error, "L003", "Expected annotation name after '@'", Span(file, startPos, currentPos)))
            } else {
              Right(TokenKind.Annotation(sb.toString))
            }
          } else if (ch.isDigit) {
            val sb = new StringBuilder
            while (offset < length && peek().isDigit) sb.append(advance())
            sb.toString.toIntOption match {
              case Some(num) => Right(TokenKind.IntLit(num))
              case None =>
                Left(Diagnostic(Diagnostic.Severity.Error, "L004", s"Integer literal out of range: '$sb'", Span(file, startPos, currentPos)))
            }
          } else if (isIdentStart(ch)) {
            val sb = new StringBuilder
            while (offset < length && isIdentPart(peek())) sb.append(advance())
            val word = sb.toString
            if (word == "_") {
              Right(TokenKind.Underscore)
            } else if (word.startsWith("Type") && word.length > 4 && word.substring(4).forall(_.isDigit)) {
              word.substring(4).toIntOption match {
                case Some(level) => Right(TokenKind.TypeLevel(level))
                case None => Right(TokenKind.Ident(word))
              }
            } else {
              Right(Keywords.getOrElse(word, TokenKind.Ident(word)))
            }
          } else {
            advance()
            Left(
              Diagnostic(
                Diagnostic.Severity.Error,
                "L005",
                s"Unexpected character '$ch'",
                Span(file, startPos, currentPos)
              )
            )
          }

        kindOpt match {
          case Left(err)   => return Left(err)
          case Right(kind) => tokens += Token(kind, Span(file, startPos, currentPos))
        }
      }
    }

    val eofPos = currentPos
    tokens += Token(TokenKind.Eof, Span(file, eofPos, eofPos))
    Right(tokens.result())
  }
}
