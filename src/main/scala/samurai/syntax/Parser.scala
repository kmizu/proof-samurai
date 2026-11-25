package samurai.syntax

import samurai.util.{Diagnostic, Span}

/**
 * Recursive-descent + precedence-climbing parser for Proof Samurai.
 *
 * Strictly Scala 3 brace-delimited syntax (no indentation-sensitive rules).
 * A file formatted across multiple lines or minified onto a single line parses identically.
 */
object Parser {

  def parseFile(file: String, source: String): Either[Diagnostic, List[TopDecl]] =
    Lexer.tokenize(file, source).flatMap { tokens =>
      val state = new ParserState(tokens)
      state.parseTopDecls()
    }

  def parseExprString(file: String, source: String): Either[Diagnostic, SurfaceExpr] =
    Lexer.tokenize(file, source).flatMap { tokens =>
      val state = new ParserState(tokens)
      for {
        expr <- state.parseExpr()
        _    <- state.expectEof()
      } yield expr
    }

  def parseTacticString(file: String, source: String): Either[Diagnostic, List[TacticStmt]] =
    Lexer.tokenize(file, source).flatMap { tokens =>
      val state = new ParserState(tokens)
      state.parseTacticListUntil(TokenKind.Eof)
    }

  private final class ParseAbort(val diagnostic: Diagnostic) extends RuntimeException(diagnostic.message)

  private final class ParserState(tokens: Vector[Token]) {
    private var position: Int = 0

    private def current: Token =
      if (position < tokens.length) tokens(position) else tokens.last

    private def peek(offset: Int): Token =
      if (position + offset < tokens.length) tokens(position + offset) else tokens.last

    private def advance(): Token = {
      val tok = current
      if (position < tokens.length - 1) position += 1
      tok
    }

    private def fail(code: String, message: String, span: Span = current.span): Nothing =
      throw new ParseAbort(Diagnostic(Diagnostic.Severity.Error, code, message, span))

    private def expect(kind: TokenKind, label: String): Token = {
      if (current.kind == kind) advance()
      else fail("P001", s"Expected $label, found ${current.kind}")
    }

    private def expectIdent(context: String): (String, Span) = current.kind match {
      case TokenKind.Ident(name) =>
        val tok = advance()
        (name, tok.span)
      case TokenKind.Underscore =>
        val tok = advance()
        ("_", tok.span)
      case other =>
        fail("P002", s"Expected identifier for $context, found $other")
    }

    private def skipSemis(): Unit = {
      while (current.kind == TokenKind.Semi) advance()
    }

    def expectEof(): Either[Diagnostic, Unit] =
      if (current.kind == TokenKind.Eof) Right(())
      else Left(Diagnostic(Diagnostic.Severity.Error, "P003", s"Unexpected trailing token ${current.kind}", current.span))

    def parseTopDecls(): Either[Diagnostic, List[TopDecl]] = {
      try {
        val decls = List.newBuilder[TopDecl]
        skipSemis()
        while (current.kind != TokenKind.Eof) {
          decls += parseTopDecl()
          skipSemis()
        }
        Right(decls.result())
      } catch {
        case abort: ParseAbort => Left(abort.diagnostic)
      }
    }

    def parseExpr(): Either[Diagnostic, SurfaceExpr] = {
      try {
        Right(expr())
      } catch {
        case abort: ParseAbort => Left(abort.diagnostic)
      }
    }

    def parseTacticListUntil(endToken: TokenKind): Either[Diagnostic, List[TacticStmt]] = {
      try {
        val stmts = parseTacticsUntil(endToken)
        Right(stmts)
      } catch {
        case abort: ParseAbort => Left(abort.diagnostic)
      }
    }

    private def parseAnnotations(): List[SurfaceAnnotation] = {
      val anns = List.newBuilder[SurfaceAnnotation]
      while (current.kind.isInstanceOf[TokenKind.Annotation]) {
        val tok = advance()
        val annName = tok.kind.asInstanceOf[TokenKind.Annotation].name
        val args =
          if (current.kind == TokenKind.LParen) parseParenExprList()
          else Nil
        anns += SurfaceAnnotation(annName, args, tok.span)
      }
      anns.result()
    }

    private def parseTopDecl(): TopDecl = {
      val annotations = parseAnnotations()
      current.kind match {
        case TokenKind.KwModule =>
          if (annotations.nonEmpty) fail("P004", "Annotations are not supported on module declarations")
          parseModuleDecl()
        case TokenKind.KwImport =>
          if (annotations.nonEmpty) fail("P004", "Annotations are not supported on import declarations")
          parseImportDecl()
        case TokenKind.KwEnum =>
          parseEnumDecl(annotations)
        case TokenKind.KwCase =>
          parseCaseClassDecl(annotations)
        case TokenKind.KwDef =>
          parseDefDecl(annotations, isTheorem = false, isPartial = false)
        case TokenKind.KwPartial =>
          val partialTok = advance()
          current.kind match {
            case TokenKind.KwDef =>
              parseDefDecl(annotations, isTheorem = false, isPartial = true, startOverride = Some(partialTok.span))
            case _ =>
              fail("P007", "Only 'def' declarations can be marked 'partial' (theorems and lemmas must be total)", partialTok.span)
          }
        case TokenKind.KwMutual =>
          if (annotations.nonEmpty) fail("P004", "Annotations are not supported directly on 'mutual' blocks; place them on individual 'def's")
          parseMutualDecl()
        case TokenKind.KwTheorem | TokenKind.KwLemma =>
          parseDefDecl(annotations, isTheorem = true, isPartial = false)
        case TokenKind.KwVal =>
          parseValDecl(annotations)
        case TokenKind.KwAxiom =>
          parseAxiomDecl(annotations)
        case TokenKind.Directive(dirName) =>
          val startTok = advance()
          val target = expr()
          TopDecl.DirectiveDecl(dirName, target, startTok.span.merge(target.span))
        case other =>
          fail("P005", s"Expected top-level declaration, found $other")
      }
    }

    private def parseModuleDecl(): TopDecl.ModuleDecl = {
      val start = expect(TokenKind.KwModule, "'module'")
      val (moduleName, _) = expectIdent("module name")
      expect(TokenKind.LBrace, "'{' to open module body")
      val decls = List.newBuilder[TopDecl]
      skipSemis()
      while (current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
        decls += parseTopDecl()
        skipSemis()
      }
      val end = expect(TokenKind.RBrace, "'}' to close module body")
      TopDecl.ModuleDecl(moduleName, decls.result(), start.span.merge(end.span))
    }

    private def parseImportDecl(): TopDecl.ImportDecl = {
      val start = expect(TokenKind.KwImport, "'import'")
      val (moduleName, modSpan) = expectIdent("module name")
      if (current.kind == TokenKind.Dot) {
        advance()
        current.kind match {
          case TokenKind.Star =>
            val end = advance()
            TopDecl.ImportDecl(moduleName, ImportSelector.Wildcard, start.span.merge(end.span))
          case TokenKind.LBrace =>
            advance()
            val names = List.newBuilder[String]
            while (current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
              val (n, _) = expectIdent("imported symbol")
              names += n
              if (current.kind == TokenKind.Comma) advance()
            }
            val end = expect(TokenKind.RBrace, "'}' in import selector")
            TopDecl.ImportDecl(moduleName, ImportSelector.Multiple(names.result()), start.span.merge(end.span))
          case TokenKind.Ident(sym) =>
            val end = advance()
            TopDecl.ImportDecl(moduleName, ImportSelector.Single(sym), start.span.merge(end.span))
          case other =>
            fail("P006", s"Expected '*', identifier, or '{...}' after 'import $moduleName.', found $other")
        }
      } else {
        TopDecl.ImportDecl(moduleName, ImportSelector.Wildcard, start.span.merge(modSpan))
      }
    }

    private def parseEnumDecl(annotations: List[SurfaceAnnotation]): TopDecl.EnumDecl = {
      val start = expect(TokenKind.KwEnum, "'enum'")
      val (enumName, _) = expectIdent("enum name")
      val typeParams = if (current.kind == TokenKind.LBracket) parseBracketBinders() else Nil
      val indexParams = if (current.kind == TokenKind.LParen) parseParenBinders() else Nil
      val sortAnn =
        if (current.kind == TokenKind.Colon) {
          advance()
          Some(expr())
        } else None

      expect(TokenKind.LBrace, "'{' to open enum body")
      val cases = List.newBuilder[EnumCaseDecl]
      skipSemis()
      while (current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
        cases += parseEnumCase()
        skipSemis()
      }
      val end = expect(TokenKind.RBrace, "'}' to close enum body")
      TopDecl.EnumDecl(annotations, enumName, typeParams, indexParams, sortAnn, cases.result(), start.span.merge(end.span))
    }

    private def parseEnumCase(): EnumCaseDecl = {
      val start = expect(TokenKind.KwCase, "'case'")
      val (ctorName, nameSpan) = expectIdent("constructor name")
      val fields = if (current.kind == TokenKind.LParen) parseParenBinders() else Nil
      val (resultType, endSpan) =
        if (current.kind == TokenKind.Colon) {
          advance()
          val ret = expr()
          (Some(ret), ret.span)
        } else {
          (None, fields.lastOption.map(_.span).getOrElse(nameSpan))
        }
      EnumCaseDecl(ctorName, fields, resultType, start.span.merge(endSpan))
    }

    private def parseCaseClassDecl(annotations: List[SurfaceAnnotation]): TopDecl.CaseClassDecl = {
      val start = expect(TokenKind.KwCase, "'case'")
      expect(TokenKind.KwClass, "'class'")
      val (className, nameSpan) = expectIdent("case class name")
      val typeParams = if (current.kind == TokenKind.LBracket) parseBracketBinders() else Nil
      val fields = if (current.kind == TokenKind.LParen) parseParenBinders() else Nil
      val (sortAnn, endSpan) =
        if (current.kind == TokenKind.Colon) {
          advance()
          val s = expr()
          (Some(s), s.span)
        } else {
          (None, fields.lastOption.map(_.span).getOrElse(nameSpan))
        }
      TopDecl.CaseClassDecl(annotations, className, typeParams, fields, sortAnn, start.span.merge(endSpan))
    }

    private def parseMutualDecl(): TopDecl.MutualDecl = {
      val start = expect(TokenKind.KwMutual, "'mutual'")
      expect(TokenKind.LBrace, "'{' to open mutual block")
      val defs = List.newBuilder[TopDecl.DefDecl]
      skipSemis()
      while (current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
        val annotations = parseAnnotations()
        current.kind match {
          case TokenKind.KwDef =>
            defs += parseDefDecl(annotations, isTheorem = false, isPartial = false)
          case TokenKind.KwPartial =>
            val partialTok = advance()
            if (current.kind != TokenKind.KwDef) {
              fail("P007", "Only 'def' declarations can be marked 'partial' inside 'mutual'", partialTok.span)
            }
            defs += parseDefDecl(annotations, isTheorem = false, isPartial = true, startOverride = Some(partialTok.span))
          case other =>
            fail("P008", s"Expected 'def' or 'partial def' inside 'mutual { ... }', found $other")
        }
        skipSemis()
      }
      val end = expect(TokenKind.RBrace, "'}' to close mutual block")
      TopDecl.MutualDecl(defs.result(), start.span.merge(end.span))
    }

    private def parseDefDecl(
      annotations: List[SurfaceAnnotation],
      isTheorem: Boolean,
      isPartial: Boolean,
      startOverride: Option[Span] = None
    ): TopDecl.DefDecl = {
      val start = advance() // def | theorem | lemma
      val declStart = startOverride.getOrElse(start.span)
      val (defName, _) = expectIdent(if (isTheorem) "theorem name" else "function name")
      val typeParams = if (current.kind == TokenKind.LBracket) parseBracketBinders() else Nil
      val valueParams = parseRepeatedParenBinders()
      val returnType =
        if (current.kind == TokenKind.Colon) {
          advance()
          Some(expr())
        } else None
      expect(TokenKind.Eq, "'='")
      val body = expr()
      var endSpan = body.span

      val terminationBy =
        if (current.kind == TokenKind.KwTerminationBy) {
          advance()
          expect(TokenKind.LBrace, "'{' after 'termination_by'")
          val measureExpr = expr()
          val closeBrace = expect(TokenKind.RBrace, "'}' after termination_by measure")
          endSpan = closeBrace.span
          Some(measureExpr)
        } else None

      val decreasingBy =
        if (current.kind == TokenKind.KwDecreasingBy) {
          advance()
          expect(TokenKind.LBrace, "'{' after 'decreasing_by'")
          val tactics = parseTacticsUntil(TokenKind.RBrace)
          val closeBrace = expect(TokenKind.RBrace, "'}' after decreasing_by tactics")
          endSpan = closeBrace.span
          Some(tactics)
        } else None

      new TopDecl.DefDecl(
        annotations = annotations,
        name = defName,
        typeParams = typeParams,
        valueParams = valueParams,
        returnType = returnType,
        body = body,
        isTheorem = isTheorem,
        span = declStart.merge(endSpan),
        isPartial = isPartial,
        terminationBy = terminationBy,
        decreasingBy = decreasingBy
      )
    }

    private def parseValDecl(annotations: List[SurfaceAnnotation]): TopDecl.ValDecl = {
      val start = expect(TokenKind.KwVal, "'val'")
      val (valName, _) = expectIdent("val name")
      val typeAnn =
        if (current.kind == TokenKind.Colon) {
          advance()
          Some(expr())
        } else None
      expect(TokenKind.Eq, "'='")
      val value = expr()
      TopDecl.ValDecl(annotations, valName, typeAnn, value, start.span.merge(value.span))
    }

    private def parseAxiomDecl(annotations: List[SurfaceAnnotation]): TopDecl.AxiomDecl = {
      val start = expect(TokenKind.KwAxiom, "'axiom'")
      val (axiomName, _) = expectIdent("axiom name")
      val typeParams = if (current.kind == TokenKind.LBracket) parseBracketBinders() else Nil
      val valueParams = parseRepeatedParenBinders()
      expect(TokenKind.Colon, "':' and axiom type")
      val returnType = expr()
      TopDecl.AxiomDecl(annotations, axiomName, typeParams, valueParams, returnType, start.span.merge(returnType.span))
    }

    private def parseBracketBinders(): List[ParamBinder] = {
      expect(TokenKind.LBracket, "'['")
      val binders = List.newBuilder[ParamBinder]
      if (current.kind != TokenKind.RBracket) {
        var more = true
        while (more) {
          val (name, nameSpan) = expectIdent("type parameter")
          val (typeAnn, endSpan) =
            if (current.kind == TokenKind.Colon) {
              advance()
              val t = expr()
              (Some(t), t.span)
            } else (None, nameSpan)
          binders += ParamBinder(name, typeAnn, nameSpan.merge(endSpan))
          if (current.kind == TokenKind.Comma) advance()
          else more = false
        }
      }
      expect(TokenKind.RBracket, "']'")
      binders.result()
    }

    private def parseRepeatedParenBinders(): List[ParamBinder] = {
      val all = List.newBuilder[ParamBinder]
      while (current.kind == TokenKind.LParen) {
        all ++= parseParenBinders()
      }
      all.result()
    }

    private def parseParenBinders(): List[ParamBinder] = {
      expect(TokenKind.LParen, "'('")
      val binders = List.newBuilder[ParamBinder]
      if (current.kind != TokenKind.RParen) {
        var more = true
        while (more) {
          val (name, nameSpan) = expectIdent("parameter name")
          val (typeAnn, endSpan) =
            if (current.kind == TokenKind.Colon) {
              advance()
              val t = expr()
              (Some(t), t.span)
            } else (None, nameSpan)
          binders += ParamBinder(name, typeAnn, nameSpan.merge(endSpan))
          if (current.kind == TokenKind.Comma) advance()
          else more = false
        }
      }
      expect(TokenKind.RParen, "')'")
      binders.result()
    }

    private def parseParenExprList(): List[SurfaceExpr] = {
      expect(TokenKind.LParen, "'('")
      val args = List.newBuilder[SurfaceExpr]
      if (current.kind != TokenKind.RParen) {
        var more = true
        while (more) {
          args += expr()
          if (current.kind == TokenKind.Comma) advance()
          else more = false
        }
      }
      expect(TokenKind.RParen, "')'")
      args.result()
    }

    private def parseBracketExprList(): List[SurfaceExpr] = {
      expect(TokenKind.LBracket, "'['")
      val args = List.newBuilder[SurfaceExpr]
      if (current.kind != TokenKind.RBracket) {
        var more = true
        while (more) {
          args += expr()
          if (current.kind == TokenKind.Comma) advance()
          else more = false
        }
      }
      expect(TokenKind.RBracket, "']'")
      args.result()
    }

    // =========================================================================
    // Expression Grammar (Precedence Climbing, 100% Brace-Delimited)
    // =========================================================================

    private def expr(): SurfaceExpr = parseArrow()

    private def parseArrow(): SurfaceExpr = {
      // Check for `forall (x: A, ...) => body` or `forall [A] (x: A) => body`
      if (current.kind == TokenKind.KwForall) {
        val start = advance()
        val typeBinders = if (current.kind == TokenKind.LBracket) parseBracketBinders() else Nil
        val valueBinders = parseRepeatedParenBinders()
        val allBinders = typeBinders ++ valueBinders
        if (allBinders.isEmpty) {
          fail("P007", "Expected parameter list after 'forall'")
        }
        if (current.kind == TokenKind.FatArrow || current.kind == TokenKind.ThinArrow || current.kind == TokenKind.Comma) {
          advance()
        } else {
          fail("P008", "Expected '=>' or '->' after forall binders")
        }
        val body = parseArrow()
        return SurfaceExpr.ArrowExpr(allBinders, body, alwaysPi = true, start.span.merge(body.span))
      }

      // Check for `exists (x: A, ...) => body`
      if (current.kind == TokenKind.KwExists) {
        val start = advance()
        val binders = parseRepeatedParenBinders()
        if (binders.isEmpty) fail("P009", "Expected parameter list after 'exists'")
        if (current.kind == TokenKind.FatArrow || current.kind == TokenKind.Comma) advance()
        else fail("P010", "Expected '=>' after exists binders")
        val body = parseArrow()
        return SurfaceExpr.ExistsExpr(binders, body, start.span.merge(body.span))
      }

      // Check for parenthesized binder list `(x: A, y: B) => body` or `(x, y) => body` or `(x: A) -> body`
      if (current.kind == TokenKind.LParen && looksLikeArrowParamList()) {
        val start = current.span
        val binders = parseParenBinders()
        val arrowTok = advance() // FatArrow or ThinArrow
        val alwaysPi = arrowTok.kind == TokenKind.ThinArrow
        val body = parseArrow()
        return SurfaceExpr.ArrowExpr(binders, body, alwaysPi, start.merge(body.span))
      }

      val left = parseLogicOr()
      current.kind match {
        case TokenKind.FatArrow =>
          advance()
          val right = parseArrow()
          SurfaceExpr.ArrowExpr(
            List(ParamBinder("_", Some(left), left.span, isBareArrowLeft = true)),
            right,
            alwaysPi = false,
            left.span.merge(right.span)
          )
        case TokenKind.ThinArrow =>
          advance()
          val right = parseArrow()
          SurfaceExpr.ArrowExpr(
            List(ParamBinder("_", Some(left), left.span)),
            right,
            alwaysPi = true,
            left.span.merge(right.span)
          )
        case _ =>
          left
      }
    }

    /**
     * Speculatively checks if current `(` starts a lambda/pi parameter list followed by `=>` or `->`.
     */
    private def looksLikeArrowParamList(): Boolean = {
      val saved = position
      try {
        if (current.kind != TokenKind.LParen) return false
        advance()
        if (current.kind == TokenKind.RParen) {
          advance()
          return current.kind == TokenKind.FatArrow || current.kind == TokenKind.ThinArrow
        }
        var valid = true
        var more = true
        while (more && valid) {
          current.kind match {
            case TokenKind.Ident(_) | TokenKind.Underscore =>
              advance()
              if (current.kind == TokenKind.Colon) {
                advance()
                // Skip balanced tokens until ',' or ')' at depth 0
                var depth = 0
                while (
                  current.kind != TokenKind.Eof &&
                  !(depth == 0 && (current.kind == TokenKind.Comma || current.kind == TokenKind.RParen))
                ) {
                  current.kind match {
                    case TokenKind.LParen | TokenKind.LBracket | TokenKind.LBrace => depth += 1
                    case TokenKind.RParen | TokenKind.RBracket | TokenKind.RBrace => depth -= 1
                    case _ => ()
                  }
                  advance()
                }
              }
              if (current.kind == TokenKind.Comma) advance()
              else if (current.kind == TokenKind.RParen) {
                advance()
                more = false
              } else {
                valid = false
              }
            case _ =>
              valid = false
          }
        }
        valid && (current.kind == TokenKind.FatArrow || current.kind == TokenKind.ThinArrow)
      } finally {
        position = saved
      }
    }

    private def parseLogicOr(): SurfaceExpr = {
      var left = parseLogicAnd()
      while (current.kind == TokenKind.LogicOr) {
        advance()
        val right = parseLogicOr()
        left = SurfaceExpr.BinaryOpExpr("\\/", left, right, left.span.merge(right.span))
      }
      left
    }

    private def parseLogicAnd(): SurfaceExpr = {
      var left = parseBoolOr()
      while (current.kind == TokenKind.LogicAnd) {
        advance()
        val right = parseLogicAnd()
        left = SurfaceExpr.BinaryOpExpr("/\\", left, right, left.span.merge(right.span))
      }
      left
    }

    private def parseBoolOr(): SurfaceExpr = {
      var left = parseBoolAnd()
      while (current.kind == TokenKind.PipePipe) {
        advance()
        val right = parseBoolAnd()
        left = SurfaceExpr.BinaryOpExpr("||", left, right, left.span.merge(right.span))
      }
      left
    }

    private def parseBoolAnd(): SurfaceExpr = {
      var left = parsePropEquality()
      while (current.kind == TokenKind.AmpAmp) {
        advance()
        val right = parsePropEquality()
        left = SurfaceExpr.BinaryOpExpr("&&", left, right, left.span.merge(right.span))
      }
      left
    }

    private def parsePropEquality(): SurfaceExpr = {
      var left = parseComparison()
      while (current.kind == TokenKind.EqEqEq || current.kind == TokenKind.BangEqEq) {
        val op = if (advance().kind == TokenKind.EqEqEq) "===" else "!=="
        val right = parseComparison()
        left = SurfaceExpr.BinaryOpExpr(op, left, right, left.span.merge(right.span))
      }
      left
    }

    private def parseComparison(): SurfaceExpr = {
      var left = parseCons()
      while (
        current.kind == TokenKind.EqEq || current.kind == TokenKind.BangEq ||
        current.kind == TokenKind.LtEq || current.kind == TokenKind.Lt ||
        current.kind == TokenKind.GtEq || current.kind == TokenKind.Gt
      ) {
        val op = advance().kind match {
          case TokenKind.EqEq   => "=="
          case TokenKind.BangEq => "!="
          case TokenKind.LtEq   => "<="
          case TokenKind.Lt     => "<"
          case TokenKind.GtEq   => ">="
          case _                => ">"
        }
        val right = parseCons()
        left = SurfaceExpr.BinaryOpExpr(op, left, right, left.span.merge(right.span))
      }
      left
    }

    private def parseCons(): SurfaceExpr = {
      val left = parseAdditive()
      current.kind match {
        case TokenKind.ColonColon =>
          advance()
          val right = parseCons() // right-associative
          SurfaceExpr.BinaryOpExpr("::", left, right, left.span.merge(right.span))
        case TokenKind.PlusPlus =>
          advance()
          val right = parseCons() // right-associative
          SurfaceExpr.BinaryOpExpr("++", left, right, left.span.merge(right.span))
        case _ =>
          left
      }
    }

    private def parseAdditive(): SurfaceExpr = {
      var left = parseMultiplicative()
      while (current.kind == TokenKind.Plus || current.kind == TokenKind.Minus) {
        val op = if (advance().kind == TokenKind.Plus) "+" else "-"
        val right = parseMultiplicative()
        left = SurfaceExpr.BinaryOpExpr(op, left, right, left.span.merge(right.span))
      }
      left
    }

    private def parseMultiplicative(): SurfaceExpr = {
      var left = parseUnary()
      while (current.kind == TokenKind.Star) {
        advance()
        val right = parseUnary()
        left = SurfaceExpr.BinaryOpExpr("*", left, right, left.span.merge(right.span))
      }
      left
    }

    private def parseUnary(): SurfaceExpr = current.kind match {
      case TokenKind.Bang =>
        val tok = advance()
        val operand = parseUnary()
        SurfaceExpr.UnaryOpExpr("!", operand, tok.span.merge(operand.span))
      case TokenKind.Tilde =>
        val tok = advance()
        val operand = parseUnary()
        SurfaceExpr.UnaryOpExpr("~", operand, tok.span.merge(operand.span))
      case _ =>
        parsePostfix()
    }

    private def parsePostfix(): SurfaceExpr = {
      var currentExpr = parseAtom()
      var continuing = true
      while (continuing) {
        current.kind match {
          case TokenKind.Dot =>
            advance()
            val (member, memSpan) = expectIdent("member name")
            currentExpr = SurfaceExpr.SelectExpr(currentExpr, member, currentExpr.span.merge(memSpan))
          case TokenKind.LBracket =>
            val typeArgs = parseBracketExprList()
            val endSpan = peek(-1).span
            currentExpr = SurfaceExpr.TypeAppExpr(currentExpr, typeArgs, currentExpr.span.merge(endSpan))
          case TokenKind.LParen =>
            val args = parseParenExprList()
            val endSpan = peek(-1).span
            currentExpr = SurfaceExpr.CallExpr(currentExpr, args, currentExpr.span.merge(endSpan))
          case TokenKind.KwMatch =>
            currentExpr = parseMatchSuffix(currentExpr)
          case _ =>
            continuing = false
        }
      }
      currentExpr
    }

    private def parseMatchSuffix(scrutinee: SurfaceExpr): SurfaceExpr.MatchExpr = {
      expect(TokenKind.KwMatch, "'match'")
      val motive =
        if (current.kind == TokenKind.KwReturning) {
          advance()
          Some(expr())
        } else None
      expect(TokenKind.LBrace, "'{' to open match expression")
      val cases = List.newBuilder[MatchCase]
      skipSemis()
      while (current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
        cases += parseMatchCase()
        skipSemis()
      }
      val end = expect(TokenKind.RBrace, "'}' to close match expression")
      SurfaceExpr.MatchExpr(scrutinee, motive, cases.result(), scrutinee.span.merge(end.span))
    }

    private def parseMatchCase(): MatchCase = {
      val start = expect(TokenKind.KwCase, "'case'")
      val pattern = parsePattern()
      expect(TokenKind.FatArrow, "'=>' in match case")
      val body = expr()
      MatchCase(pattern, body, start.span.merge(body.span))
    }

    private def parsePattern(): Pattern = {
      val left = parseAtomicPattern()
      if (current.kind == TokenKind.ColonColon) {
        advance()
        val right = parsePattern()
        Pattern.Cons(left, right, left.span.merge(right.span))
      } else {
        left
      }
    }

    private def parseAtomicPattern(): Pattern = current.kind match {
      case TokenKind.Underscore =>
        val tok = advance()
        Pattern.Wildcard(tok.span)
      case TokenKind.IntLit(v) =>
        val tok = advance()
        Pattern.NatLit(v, tok.span)
      case TokenKind.KwTrue =>
        val tok = advance()
        Pattern.BoolLit(true, tok.span)
      case TokenKind.KwFalse =>
        val tok = advance()
        Pattern.BoolLit(false, tok.span)
      case TokenKind.LParen =>
        advance()
        val inner = parsePattern()
        expect(TokenKind.RParen, "')' in pattern")
        inner
      case TokenKind.LBracket =>
        val start = advance()
        val elems = List.newBuilder[Pattern]
        if (current.kind != TokenKind.RBracket) {
          var more = true
          while (more) {
            elems += parsePattern()
            if (current.kind == TokenKind.Comma) advance()
            else more = false
          }
        }
        val end = expect(TokenKind.RBracket, "']' in list pattern")
        Pattern.ListLit(elems.result(), start.span.merge(end.span))
      case TokenKind.Ident(first) =>
        val startTok = advance()
        if (current.kind == TokenKind.Dot) {
          advance()
          val (ctorName, ctorSpan) = expectIdent("constructor name in pattern")
          val (args, endSpan) = parsePatternArgs(ctorSpan)
          Pattern.Ctor(Some(first), ctorName, args, startTok.span.merge(endSpan))
        } else if (current.kind == TokenKind.LParen) {
          val (args, endSpan) = parsePatternArgs(startTok.span)
          Pattern.Ctor(None, first, args, startTok.span.merge(endSpan))
        } else if (first.headOption.exists(_.isUpper)) {
          // Uppercase bare identifier in pattern is a nullary constructor (e.g. Zero, Nil, Refl)
          Pattern.Ctor(None, first, Nil, startTok.span)
        } else {
          Pattern.Var(first, startTok.span)
        }
      case other =>
        fail("P011", s"Expected pattern, found $other")
    }

    private def parsePatternArgs(defaultEnd: Span): (List[Pattern], Span) = {
      if (current.kind != TokenKind.LParen) return (Nil, defaultEnd)
      advance()
      val args = List.newBuilder[Pattern]
      if (current.kind != TokenKind.RParen) {
        var more = true
        while (more) {
          args += parsePattern()
          if (current.kind == TokenKind.Comma) advance()
          else more = false
        }
      }
      val end = expect(TokenKind.RParen, "')' in pattern arguments")
      (args.result(), end.span)
    }

    private def parseAtom(): SurfaceExpr = current.kind match {
      case TokenKind.KwProp =>
        val tok = advance()
        SurfaceExpr.SortExpr(isProp = true, level = 0, tok.span)

      case TokenKind.KwType =>
        val tok = advance()
        SurfaceExpr.SortExpr(isProp = false, level = 0, tok.span)

      case TokenKind.TypeLevel(level) =>
        val tok = advance()
        SurfaceExpr.SortExpr(isProp = false, level = level, tok.span)

      case TokenKind.Ident("do") if peek(1).kind == TokenKind.LBrace =>
        parseDoBlock()

      case TokenKind.Ident(name) =>
        val tok = advance()
        SurfaceExpr.VarExpr(name, tok.span)

      case TokenKind.Underscore =>
        val tok = advance()
        SurfaceExpr.HoleExpr(None, tok.span)

      case TokenKind.IntLit(v) =>
        val tok = advance()
        SurfaceExpr.IntLitExpr(v, tok.span)

      case TokenKind.KwTrue =>
        val tok = advance()
        SurfaceExpr.BoolLitExpr(true, tok.span)

      case TokenKind.KwFalse =>
        val tok = advance()
        SurfaceExpr.BoolLitExpr(false, tok.span)

      case TokenKind.Hole(name) =>
        val tok = advance()
        SurfaceExpr.HoleExpr(name, tok.span)

      case TokenKind.KwSorry =>
        val tok = advance()
        SurfaceExpr.SorryExpr(tok.span)

      case TokenKind.LParen =>
        val start = advance()
        val inner = expr()
        val result =
          if (current.kind == TokenKind.Colon) {
            advance()
            val ascribedTy = expr()
            SurfaceExpr.AscribeExpr(inner, ascribedTy, start.span.merge(ascribedTy.span))
          } else inner
        expect(TokenKind.RParen, "')'")
        result

      case TokenKind.LBracket =>
        val start = advance()
        val elems = List.newBuilder[SurfaceExpr]
        if (current.kind != TokenKind.RBracket) {
          var more = true
          while (more) {
            elems += expr()
            if (current.kind == TokenKind.Comma) advance()
            else more = false
          }
        }
        val end = expect(TokenKind.RBracket, "']' closing list literal")
        SurfaceExpr.ListLitExpr(elems.result(), start.span.merge(end.span))

      case TokenKind.LBrace =>
        parseBlockExpr()

      case TokenKind.KwIf =>
        parseIfExpr()

      case TokenKind.KwBy =>
        parseTacticBlock()

      case TokenKind.KwCalc =>
        parseCalcBlock()

      case other =>
        fail("P012", s"Expected expression, found $other")
    }

    private sealed trait DoStep {
      def span: Span
    }
    private object DoStep {
      final case class Bind(name: String, typeAnn: Option[SurfaceExpr], action: SurfaceExpr, span: Span) extends DoStep
      final case class LetVal(name: String, typeAnn: Option[SurfaceExpr], value: SurfaceExpr, span: Span) extends DoStep
      final case class Action(expr: SurfaceExpr, span: Span) extends DoStep
    }

    /**
     * Parse monadic `do { val x <- act; val y = pureExpr; sideEffect; result }` block
     * and desugar cleanly into `bind` calls and `BlockExpr` local `val`s (0 kernel changes!).
     */
    private def parseDoBlock(): SurfaceExpr = {
      val start = advance() // 'do'
      expect(TokenKind.LBrace, "'{' after 'do'")
      val steps = List.newBuilder[DoStep]
      skipSemis()
      while (current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
        if (current.kind == TokenKind.KwVal) {
          val valTok = advance()
          val (rawName, _) =
            if (current.kind == TokenKind.Underscore) {
              val u = advance()
              ("_", u.span)
            } else expectIdent("variable name in 'do' block")
          val typeAnn =
            if (current.kind == TokenKind.Colon) {
              advance()
              Some(expr())
            } else None
          if (current.kind == TokenKind.LeftArrow) {
            advance()
            val action = expr()
            steps += DoStep.Bind(rawName, typeAnn, action, valTok.span.merge(action.span))
          } else {
            expect(TokenKind.Eq, "'<-' or '=' after 'val' in 'do' block")
            val rhs = expr()
            steps += DoStep.LetVal(rawName, typeAnn, rhs, valTok.span.merge(rhs.span))
          }
        } else {
          val e = expr()
          steps += DoStep.Action(e, e.span)
        }
        skipSemis()
      }
      val end = expect(TokenKind.RBrace, "'}' closing 'do' block")
      val stepList = steps.result()
      if (stepList.isEmpty) {
        fail("P020", "'do' block cannot be empty", start.span.merge(end.span))
      }

      def desugar(rem: List[DoStep], idx: Int): SurfaceExpr = rem match {
        case List(DoStep.Action(finalExpr, _)) =>
          finalExpr
        case List(last) =>
          fail("P021", "Last statement in 'do' block must be an expression (not a 'val' binding)", last.span)
        case DoStep.LetVal(rawName, typeAnn, value, sp) :: rest =>
          val binderName = if (rawName == "_") s"_doLet$idx" else rawName
          val tailExpr = desugar(rest, idx + 1)
          SurfaceExpr.BlockExpr(List(BlockStatement.LocalVal(binderName, typeAnn, value, sp)), tailExpr, sp.merge(tailExpr.span))
        case DoStep.Bind(rawName, typeAnn, action, sp) :: rest =>
          val binderName = if (rawName == "_") s"_doBind$idx" else rawName
          val tailExpr = desugar(rest, idx + 1)
          val contLam = SurfaceExpr.ArrowExpr(
            List(ParamBinder(binderName, typeAnn, sp)),
            tailExpr,
            alwaysPi = false,
            sp.merge(tailExpr.span)
          )
          SurfaceExpr.CallExpr(SurfaceExpr.VarExpr("bind", sp), List(action, contLam), sp.merge(tailExpr.span))
        case DoStep.Action(action, sp) :: rest =>
          val binderName = s"_doIgnored$idx"
          val tailExpr = desugar(rest, idx + 1)
          val contLam = SurfaceExpr.ArrowExpr(
            List(ParamBinder(binderName, None, sp)),
            tailExpr,
            alwaysPi = false,
            sp.merge(tailExpr.span)
          )
          SurfaceExpr.CallExpr(SurfaceExpr.VarExpr("bind", sp), List(action, contLam), sp.merge(tailExpr.span))
        case Nil =>
          fail("P020", "'do' block cannot be empty", start.span.merge(end.span))
      }

      desugar(stepList, 0)
    }

    private def parseBlockExpr(): SurfaceExpr = {
      val start = expect(TokenKind.LBrace, "'{'")
      val statements = List.newBuilder[BlockStatement]
      skipSemis()
      while (current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
        if (current.kind == TokenKind.KwVal) {
          val valStart = advance()
          val (name, _) = expectIdent("local val name")
          val typeAnn =
            if (current.kind == TokenKind.Colon) {
              advance()
              Some(expr())
            } else None
          expect(TokenKind.Eq, "'=' in local val")
          val value = expr()
          statements += BlockStatement.LocalVal(name, typeAnn, value, valStart.span.merge(value.span))
        } else {
          val e = expr()
          statements += BlockStatement.ExprStmt(e)
        }
        skipSemis()
      }
      val end = expect(TokenKind.RBrace, "'}'")
      val allStmts = statements.result()
      allStmts match {
        case Nil =>
          fail("P013", "Empty block expression '{}' is not allowed", start.span.merge(end.span))
        case list =>
          list.last match {
            case BlockStatement.ExprStmt(finalExpr) =>
              val prefix = list.init
              if (prefix.isEmpty) finalExpr
              else SurfaceExpr.BlockExpr(prefix, finalExpr, start.span.merge(end.span))
            case BlockStatement.LocalVal(_, _, _, valSpan) =>
              fail("P014", "Block must end with a result expression, not a 'val' binding", valSpan)
          }
      }
    }

    private def parseIfExpr(): SurfaceExpr.IfExpr = {
      val start = expect(TokenKind.KwIf, "'if'")
      expect(TokenKind.LParen, "'(' after 'if'")
      val condition = expr()
      expect(TokenKind.RParen, "')' after if condition")
      val thenBranch = expr()
      expect(TokenKind.KwElse, "'else'")
      val elseBranch = expr()
      SurfaceExpr.IfExpr(condition, thenBranch, elseBranch, start.span.merge(elseBranch.span))
    }

    // =========================================================================
    // Tactic Block Grammar: `by { ... }` (100% Brace-Delimited)
    // =========================================================================

    private def parseTacticBlock(): SurfaceExpr.TacticBlockExpr = {
      val start = expect(TokenKind.KwBy, "'by'")
      expect(TokenKind.LBrace, "'{' to open tactic block")
      val tactics = parseTacticsUntil(TokenKind.RBrace)
      val end = expect(TokenKind.RBrace, "'}' to close tactic block")
      SurfaceExpr.TacticBlockExpr(tactics, start.span.merge(end.span))
    }

    private def parseCalcBlock(): SurfaceExpr.CalcExpr = {
      val start = expect(TokenKind.KwCalc, "'calc'")
      expect(TokenKind.LBrace, "'{' to open calc block")
      skipSemis()
      val initialExpr = parseComparison()
      val steps = List.newBuilder[CalcStep]
      skipSemis()
      while (current.kind == TokenKind.EqEqEq) {
        val eqTok = advance()
        val nextRhs = parseComparison()
        val proofExpr = current.kind match {
          case TokenKind.KwBy => parseTacticBlock()
          case TokenKind.Eq =>
            advance()
            parseComparison()
          case TokenKind.Ident("using") =>
            advance()
            parseComparison()
          case TokenKind.LBrace => parseBlockExpr()
          case TokenKind.EqEqEq | TokenKind.RBrace | TokenKind.Semi =>
            SurfaceExpr.VarExpr("refl", eqTok.span)
          case other =>
            fail("P018", s"Expected 'by {{ ... }}', 'using proof', '= proof', or next '===' after calc step, found $other")
        }
        steps += CalcStep(nextRhs, proofExpr, eqTok.span.merge(proofExpr.span))
        skipSemis()
      }
      val end = expect(TokenKind.RBrace, "'}' to close calc block")
      val stepList = steps.result()
      if (stepList.isEmpty) {
        fail("P019", "'calc' block must contain at least one '=== rhs by { ... }' step", start.span.merge(end.span))
      }
      SurfaceExpr.CalcExpr(initialExpr, stepList, start.span.merge(end.span))
    }

    private def parseTacticsUntil(endToken: TokenKind): List[TacticStmt] = {
      val stmts = List.newBuilder[TacticStmt]
      skipSemis()
      while (current.kind != endToken && current.kind != TokenKind.Eof) {
        stmts += parseTacticStmt()
        skipSemis()
      }
      stmts.result()
    }

    private def parseOptionalInTarget(): Option[String] = {
      current.kind match {
        case TokenKind.Ident("in") =>
          advance()
          if (current.kind == TokenKind.Star) {
            advance()
            Some("*")
          } else {
            Some(expectIdent("hypothesis name or '*' after 'in'")._1)
          }
        case _ => None
      }
    }

    private def parseTacticBlockOrSingle(): List[TacticStmt] = {
      if (current.kind == TokenKind.LBrace) {
        advance()
        val inner = parseTacticsUntil(TokenKind.RBrace)
        expect(TokenKind.RBrace, "'}' closing tactic block")
        inner
      } else {
        List(parseTacticStmt())
      }
    }

    private def parseTacticStmt(): TacticStmt = {
      var left = parseAtomicTacticStmt()
      while (current.kind == TokenKind.SeqAll) {
        advance()
        val right = parseAtomicTacticStmt()
        left = TacticStmt.SeqAll(left, right, left.span.merge(right.span))
      }
      left
    }

    private def parseAtomicTacticStmt(): TacticStmt = current.kind match {
      case TokenKind.LBrace =>
        val start = advance()
        val inner = parseTacticsUntil(TokenKind.RBrace)
        val end = expect(TokenKind.RBrace, "'}' closing tactic block")
        TacticStmt.Block(inner, start.span.merge(end.span))

      case TokenKind.KwSorry =>
        val tok = advance()
        TacticStmt.Sorry(tok.span)

      case TokenKind.Hole(name) =>
        val tok = advance()
        TacticStmt.Hole(name, tok.span)

      case TokenKind.Ident(tacticName) =>
        val start = advance()
        tacticName match {
          case "intro" | "intros" =>
            val names =
              if (current.kind == TokenKind.LParen) parseParenIdentList()
              else Nil
            TacticStmt.Intro(names, start.span.merge(peek(-1).span))

          case "exact" =>
            val arg = parseSingleParenExpr("exact")
            TacticStmt.Exact(arg, start.span.merge(peek(-1).span))

          case "apply" =>
            val arg = parseSingleParenExpr("apply")
            TacticStmt.Apply(arg, start.span.merge(peek(-1).span))

          case "refl" | "reflexivity" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Refl(start.span)

          case "symmetry" | "sym" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Symmetry(start.span)

          case "trans" | "transitivity" =>
            val mid = parseSingleParenExpr("trans")
            TacticStmt.Trans(mid, start.span.merge(peek(-1).span))

          case "rewrite" =>
            val lemmas = parseParenExprList()
            if (lemmas.isEmpty) fail("P015", "'rewrite' requires at least one lemma argument", start.span)
            val target = parseOptionalInTarget()
            TacticStmt.Rewrite(lemmas, reverse = false, target, start.span.merge(peek(-1).span))

          case "rewriteRev" | "rewriteBack" =>
            val lemmas = parseParenExprList()
            if (lemmas.isEmpty) fail("P015", "'rewriteRev' requires at least one lemma argument", start.span)
            val target = parseOptionalInTarget()
            TacticStmt.Rewrite(lemmas, reverse = true, target, start.span.merge(peek(-1).span))

          case "congr" | "congruence" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Congr(start.span)

          case "induction" =>
            val target = parseSingleParenExpr("induction")
            val cases = if (current.kind == TokenKind.LBrace) parseTacticCasesBlock() else Nil
            TacticStmt.Induction(target, cases, start.span.merge(peek(-1).span))

          case "cases" | "destruct" =>
            expect(TokenKind.LParen, "'(' for cases")
            val target = expr()
            val eqName =
              if (current.kind == TokenKind.Comma) {
                advance()
                Some(expectIdent("equation hypothesis name")._1)
              } else None
            expect(TokenKind.RParen, "')' for cases")
            val cases = if (current.kind == TokenKind.LBrace) parseTacticCasesBlock() else Nil
            TacticStmt.Cases(target, eqName, cases, start.span.merge(peek(-1).span))

          case "by_cases" | "byCases" =>
            expect(TokenKind.LParen, "'(' for by_cases")
            val cond = expr()
            val eqName =
              if (current.kind == TokenKind.Comma) {
                advance()
                Some(expectIdent("equation hypothesis name")._1)
              } else None
            expect(TokenKind.RParen, "')' for by_cases")
            val cases = if (current.kind == TokenKind.LBrace) parseTacticCasesBlock() else Nil
            TacticStmt.ByCases(cond, eqName, cases, start.span.merge(peek(-1).span))

          case "obtain" =>
            val binders = parseParenIdentList()
            if (binders.isEmpty) fail("P015", "'obtain' requires at least one binder name", start.span)
            expect(TokenKind.Eq, "'=' in obtain(x, y) = expr")
            val src = expr()
            TacticStmt.Obtain(binders, src, start.span.merge(src.span))

          case "revert" | "generalize" =>
            val names = parseParenIdentList()
            TacticStmt.Revert(names, start.span.merge(peek(-1).span))

          case "rename" =>
            expect(TokenKind.LParen, "'(' for rename")
            val (oldName, _) = expectIdent("existing hypothesis name")
            expect(TokenKind.Comma, "',' in rename(oldName, newName)")
            val (newName, _) = expectIdent("new hypothesis name")
            val end = expect(TokenKind.RParen, "')' for rename")
            TacticStmt.Rename(oldName, newName, start.span.merge(end.span))

          case "exfalso" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Exfalso(start.span)

          case "subst" =>
            val hyp = parseSingleParenExpr("subst")
            TacticStmt.Subst(hyp, start.span.merge(peek(-1).span))

          case "specialize" =>
            expect(TokenKind.LParen, "'(' for specialize")
            val (hypName, _) = expectIdent("hypothesis name")
            val args = List.newBuilder[SurfaceExpr]
            while (current.kind == TokenKind.Comma) {
              advance()
              args += expr()
            }
            val end = expect(TokenKind.RParen, "')' for specialize")
            TacticStmt.Specialize(hypName, args.result(), start.span.merge(end.span))

          case "split" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Split(start.span)

          case "left" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.LeftBranch(start.span)

          case "right" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.RightBranch(start.span)

          case "exists" | "witness" =>
            val witness = parseSingleParenExpr("exists")
            TacticStmt.ExistsWitness(witness, start.span.merge(peek(-1).span))

          case "contradiction" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Contradiction(start.span)

          case "discriminate" =>
            val hyp =
              if (current.kind == TokenKind.LParen) {
                val args = parseParenExprList()
                args.headOption
              } else None
            TacticStmt.Discriminate(hyp, start.span.merge(peek(-1).span))

          case "injection" =>
            expect(TokenKind.LParen, "'(' for injection")
            val hyp = expr()
            val names = List.newBuilder[String]
            while (current.kind == TokenKind.Comma) {
              advance()
              val (n, _) = expectIdent("injected hypothesis name")
              names += n
            }
            val end = expect(TokenKind.RParen, "')' for injection")
            TacticStmt.Injection(hyp, names.result(), start.span.merge(end.span))

          case "have" =>
            expect(TokenKind.LParen, "'(' for have")
            val (hypName, _) = expectIdent("have hypothesis name")
            expect(TokenKind.Colon, "':' in have(name: Type)")
            val propTy = expr()
            expect(TokenKind.RParen, "')' in have")
            expect(TokenKind.LBrace, "'{' for have proof block")
            val proofBody = parseTacticsUntil(TokenKind.RBrace)
            val end = expect(TokenKind.RBrace, "'}' closing have proof block")
            TacticStmt.Have(hypName, propTy, proofBody, start.span.merge(end.span))

          case "unfold" =>
            expect(TokenKind.LParen, "'(' for unfold")
            val (defName, _) = expectIdent("definition name to unfold")
            val end = expect(TokenKind.RParen, "')' for unfold")
            TacticStmt.Unfold(defName, start.span.merge(end.span))

          case "simp" =>
            val (extras, includeLocals) =
              if (current.kind == TokenKind.LParen) {
                expect(TokenKind.LParen, "'('")
                var inc = false
                val ex = List.newBuilder[SurfaceExpr]
                if (current.kind != TokenKind.RParen) {
                  var more = true
                  while (more) {
                    if (current.kind == TokenKind.Star) {
                      advance()
                      inc = true
                    } else {
                      ex += expr()
                    }
                    if (current.kind == TokenKind.Comma) advance()
                    else more = false
                  }
                }
                expect(TokenKind.RParen, "')'")
                (ex.result(), inc)
              } else (Nil, false)
            val target = parseOptionalInTarget()
            TacticStmt.Simp(extras, includeLocals, target, start.span.merge(peek(-1).span))

          case "arith" | "ring" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Arith(start.span)

          case "omega" | "lia" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Omega(start.span)

          case "cc" | "congruence_closure" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.CongruenceClosure(start.span)

          case "tauto" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Tauto(start.span)

          case "try" =>
            val body = parseTacticBlockOrSingle()
            TacticStmt.Try(body, start.span.merge(peek(-1).span))

          case "repeat" =>
            val maxSteps =
              if (current.kind == TokenKind.LParen) {
                expect(TokenKind.LParen, "'('")
                val n = current.kind match {
                  case TokenKind.IntLit(v) => advance(); Some(v)
                  case other               => fail("P015", s"Expected integer iteration bound in repeat(...), found $other")
                }
                expect(TokenKind.RParen, "')'")
                n
              } else None
            val body = parseTacticBlockOrSingle()
            TacticStmt.Repeat(body, maxSteps, start.span.merge(peek(-1).span))

          case "all" | "all_goals" =>
            val body = parseTacticBlockOrSingle()
            TacticStmt.AllGoals(body, start.span.merge(peek(-1).span))

          case "first" =>
            expect(TokenKind.LBrace, "'{' for first { ... | ... }")
            val branches = List.newBuilder[List[TacticStmt]]
            skipSemis()
            while (current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
              val branch = List.newBuilder[TacticStmt]
              while (current.kind != TokenKind.Pipe && current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
                branch += parseTacticStmt()
                skipSemis()
              }
              val bList = branch.result()
              if (bList.nonEmpty) branches += bList
              if (current.kind == TokenKind.Pipe) {
                advance()
                skipSemis()
              }
            }
            val end = expect(TokenKind.RBrace, "'}' closing first")
            TacticStmt.First(branches.result(), start.span.merge(end.span))

          case "trivial" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Trivial(start.span)

          case "auto" | "samurai" =>
            val depthOpt =
              if (current.kind == TokenKind.LParen) {
                expect(TokenKind.LParen, "'('")
                val d = current.kind match {
                  case TokenKind.IntLit(v) => advance(); Some(v)
                  case TokenKind.RParen    => None
                  case other               => fail("P015", s"Expected optional integer depth in auto(...), found $other")
                }
                expect(TokenKind.RParen, "')'")
                d
              } else None
            TacticStmt.Auto(depthOpt, start.span.merge(peek(-1).span))

          case "decide" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Decide(start.span)

          case "assumption" =>
            if (current.kind == TokenKind.LParen) { advance(); expect(TokenKind.RParen, "')'") }
            TacticStmt.Assumption(start.span)

          case unknown =>
            fail("P016", s"Unknown tactic '$unknown'", start.span)
        }

      case TokenKind.KwExists =>
        val start = advance()
        val witness = parseSingleParenExpr("exists")
        TacticStmt.ExistsWitness(witness, start.span.merge(peek(-1).span))

      case other =>
        fail("P017", s"Expected tactic statement, found $other")
    }

    private def parseSingleParenExpr(tacticName: String): SurfaceExpr = {
      expect(TokenKind.LParen, s"'(' for tactic '$tacticName'")
      val arg = expr()
      expect(TokenKind.RParen, s"')' for tactic '$tacticName'")
      arg
    }

    private def parseParenIdentList(): List[String] = {
      expect(TokenKind.LParen, "'('")
      val names = List.newBuilder[String]
      if (current.kind != TokenKind.RParen) {
        var more = true
        while (more) {
          val (n, _) = expectIdent("identifier")
          names += n
          if (current.kind == TokenKind.Comma) advance()
          else more = false
        }
      }
      expect(TokenKind.RParen, "')'")
      names.result()
    }

    private def parseTacticCasesBlock(): List[TacticCaseBranch] = {
      expect(TokenKind.LBrace, "'{' for tactic cases")
      val branches = List.newBuilder[TacticCaseBranch]
      skipSemis()
      while (current.kind != TokenKind.RBrace && current.kind != TokenKind.Eof) {
        val start = expect(TokenKind.KwCase, "'case'")
        val (firstIdent, _) = expectIdent("constructor name in tactic case")
        // Allow optional qualified name like `Nat.Succ(k, ih)` or unqualified `Succ(k, ih)`
        val ctorName =
          if (current.kind == TokenKind.Dot) {
            advance()
            expectIdent("constructor name")._1
          } else firstIdent
        val binders = if (current.kind == TokenKind.LParen) parseParenIdentList() else Nil
        expect(TokenKind.FatArrow, "'=>' in tactic case")
        val body =
          if (current.kind == TokenKind.LBrace) {
            advance()
            val inner = parseTacticsUntil(TokenKind.RBrace)
            expect(TokenKind.RBrace, "'}' closing tactic case")
            inner
          } else {
            List(parseTacticStmt())
          }
        branches += TacticCaseBranch(ctorName, binders, body, start.span.merge(peek(-1).span))
        skipSemis()
      }
      expect(TokenKind.RBrace, "'}' closing tactic cases")
      branches.result()
    }
  }
}
