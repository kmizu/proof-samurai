package samurai.util

final case class Pos(line: Int, col: Int, offset: Int) {
  override def toString: String = s"$line:$col"
}

final case class Span(file: String, start: Pos, end: Pos) {
  def merge(other: Span): Span = {
    val s = if (start.offset <= other.start.offset) start else other.start
    val e = if (end.offset >= other.end.offset) end else other.end
    Span(file, s, e)
  }

  def toJson: Json = Json.obj(
    "file" -> Json.Str(file),
    "startLine" -> Json.Num(start.line),
    "startCol" -> Json.Num(start.col),
    "endLine" -> Json.Num(end.line),
    "endCol" -> Json.Num(end.col)
  )

  override def toString: String = s"$file:${start.line}:${start.col}"
}

object Span {
  val synthetic: Span = Span("<synthetic>", Pos(0, 0, 0), Pos(0, 0, 0))
}

final case class Diagnostic(
  severity: Diagnostic.Severity,
  code: String,
  message: String,
  span: Span,
  hint: Option[String] = None,
  expected: Option[String] = None,
  found: Option[String] = None
) {
  def formatHuman(source: Option[String] = None): String = {
    val sb = new StringBuilder
    sb.append(s"${severity.label}[$code]: $message\n")
    if (span.start.line > 0) {
      sb.append(s"  --> ${span.file}:${span.start.line}:${span.start.col}\n")
      source.foreach { src =>
        val lines = src.split("\r?\n", -1)
        val lineIdx = span.start.line - 1
        if (lineIdx >= 0 && lineIdx < lines.length) {
          val lineNumStr = span.start.line.toString
          val pad = " " * lineNumStr.length
          val codeLine = lines(lineIdx)
          sb.append(s"  $pad |\n")
          sb.append(s"  $lineNumStr | $codeLine\n")
          val startCol = math.max(1, span.start.col)
          val endCol =
            if (span.end.line == span.start.line) math.max(startCol + 1, span.end.col)
            else math.max(startCol + 1, codeLine.length + 1)
          val caretLen = math.max(1, endCol - startCol)
          sb.append(s"  $pad | ${" " * (startCol - 1)}${"^" * caretLen}\n")
        }
      }
    }
    expected.foreach(e => sb.append(s"  expected: $e\n"))
    found.foreach(f => sb.append(s"  found:    $f\n"))
    hint.foreach(h => sb.append(s"  hint:     $h\n"))
    sb.toString
  }

  def toJson: Json = {
    val fields = List.newBuilder[(String, Json)]
    fields += "severity" -> Json.Str(severity.label)
    fields += "code" -> Json.Str(code)
    fields += "message" -> Json.Str(message)
    fields += "span" -> span.toJson
    expected.foreach(e => fields += "expected" -> Json.Str(e))
    found.foreach(f => fields += "found" -> Json.Str(f))
    hint.foreach(h => fields += "hint" -> Json.Str(h))
    Json.Obj(fields.result())
  }
}

object Diagnostic {
  enum Severity(val label: String) {
    case Error extends Severity("error")
    case Warning extends Severity("warning")
    case Info extends Severity("info")
  }
}
