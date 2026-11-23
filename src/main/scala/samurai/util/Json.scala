package samurai.util

enum Json {
  case Null
  case Bool(value: Boolean)
  case Num(value: Double)
  case Str(value: String)
  case Arr(items: List[Json])
  case Obj(fields: List[(String, Json)])

  def compact: String = {
    val sb = new StringBuilder
    writeTo(sb, indent = -1, depth = 0)
    sb.toString
  }

  def pretty: String = {
    val sb = new StringBuilder
    writeTo(sb, indent = 2, depth = 0)
    sb.toString
  }

  private def writeTo(sb: StringBuilder, indent: Int, depth: Int): Unit = this match {
    case Json.Null => sb.append("null")
    case Json.Bool(b) => sb.append(if (b) "true" else "false")
    case Json.Num(n) =>
      if (n.isWhole && n >= Long.MinValue && n <= Long.MaxValue) sb.append(n.toLong)
      else sb.append(n)
    case Json.Str(s) =>
      sb.append('"')
      var i = 0
      while (i < s.length) {
        s.charAt(i) match {
          case '"'  => sb.append("\\\"")
          case '\\' => sb.append("\\\\")
          case '\b' => sb.append("\\b")
          case '\f' => sb.append("\\f")
          case '\n' => sb.append("\\n")
          case '\r' => sb.append("\\r")
          case '\t' => sb.append("\\t")
          case c if c < 0x20 => sb.append(f"\\u${c.toInt}%04x")
          case c => sb.append(c)
        }
        i += 1
      }
      sb.append('"')
    case Json.Arr(items) =>
      if (items.isEmpty) {
        sb.append("[]")
      } else {
        sb.append('[')
        val it = items.iterator
        var first = true
        while (it.hasNext) {
          if (!first) sb.append(',')
          first = false
          if (indent >= 0) {
            sb.append('\n')
            sb.append(" " * ((depth + 1) * indent))
          }
          it.next().writeTo(sb, indent, depth + 1)
        }
        if (indent >= 0) {
          sb.append('\n')
          sb.append(" " * (depth * indent))
        }
        sb.append(']')
      }
    case Json.Obj(fields) =>
      if (fields.isEmpty) {
        sb.append("{}")
      } else {
        sb.append('{')
        val it = fields.iterator
        var first = true
        while (it.hasNext) {
          val (k, v) = it.next()
          if (!first) sb.append(',')
          first = false
          if (indent >= 0) {
            sb.append('\n')
            sb.append(" " * ((depth + 1) * indent))
          }
          Json.Str(k).writeTo(sb, indent, depth + 1)
          sb.append(if (indent >= 0) ": " else ":")
          v.writeTo(sb, indent, depth + 1)
        }
        if (indent >= 0) {
          sb.append('\n')
          sb.append(" " * (depth * indent))
        }
        sb.append('}')
      }
  }

  def field(key: String): Option[Json] = this match {
    case Json.Obj(fields) => fields.find(_._1 == key).map(_._2)
    case _ => None
  }

  def asString: Option[String] = this match {
    case Json.Str(s) => Some(s)
    case _ => None
  }

  def asInt: Option[Int] = this match {
    case Json.Num(n) => Some(n.toInt)
    case _ => None
  }

  def asBool: Option[Boolean] = this match {
    case Json.Bool(b) => Some(b)
    case _ => None
  }

  def asArr: Option[List[Json]] = this match {
    case Json.Arr(xs) => Some(xs)
    case _ => None
  }
}

object Json {
  def obj(fields: (String, Json)*): Json = Json.Obj(fields.toList)
  def arr(items: Json*): Json = Json.Arr(items.toList)

  def parse(input: String): Either[String, Json] = {
    val p = new Parser(input)
    p.parseRoot()
  }

  private final class Parser(s: String) {
    private var i = 0
    private val len = s.length

    private def skipWs(): Unit = {
      while (i < len && (s.charAt(i) == ' ' || s.charAt(i) == '\t' || s.charAt(i) == '\n' || s.charAt(i) == '\r')) {
        i += 1
      }
    }

    def parseRoot(): Either[String, Json] = {
      skipWs()
      parseValue().flatMap { v =>
        skipWs()
        if (i < len) Left(s"Trailing characters at offset $i")
        else Right(v)
      }
    }

    private def parseValue(): Either[String, Json] = {
      skipWs()
      if (i >= len) return Left("Unexpected end of JSON input")
      s.charAt(i) match {
        case '{' => parseObj()
        case '[' => parseArr()
        case '"' => parseStr().map(Json.Str(_))
        case 't' => expectLiteral("true", Json.Bool(true))
        case 'f' => expectLiteral("false", Json.Bool(false))
        case 'n' => expectLiteral("null", Json.Null)
        case c if c == '-' || c.isDigit => parseNum()
        case c => Left(s"Unexpected character '$c' at offset $i")
      }
    }

    private def expectLiteral(lit: String, value: Json): Either[String, Json] = {
      if (s.startsWith(lit, i)) {
        i += lit.length
        Right(value)
      } else Left(s"Expected '$lit' at offset $i")
    }

    private def parseStr(): Either[String, String] = {
      if (i >= len || s.charAt(i) != '"') return Left(s"Expected '\"' at offset $i")
      i += 1
      val sb = new StringBuilder
      while (i < len) {
        val c = s.charAt(i)
        i += 1
        if (c == '"') return Right(sb.toString)
        if (c == '\\') {
          if (i >= len) return Left("Unterminated escape sequence")
          val esc = s.charAt(i)
          i += 1
          esc match {
            case '"'  => sb.append('"')
            case '\\' => sb.append('\\')
            case '/'  => sb.append('/')
            case 'b'  => sb.append('\b')
            case 'f'  => sb.append('\f')
            case 'n'  => sb.append('\n')
            case 'r'  => sb.append('\r')
            case 't'  => sb.append('\t')
            case 'u' =>
              if (i + 4 > len) return Left("Incomplete unicode escape")
              val hex = s.substring(i, i + 4)
              i += 4
              sb.append(Integer.parseInt(hex, 16).toChar)
            case other => return Left(s"Invalid escape '\\$other'")
          }
        } else {
          sb.append(c)
        }
      }
      Left("Unterminated string literal")
    }

    private def parseNum(): Either[String, Json] = {
      val start = i
      if (i < len && s.charAt(i) == '-') i += 1
      while (i < len && s.charAt(i).isDigit) i += 1
      if (i < len && s.charAt(i) == '.') {
        i += 1
        while (i < len && s.charAt(i).isDigit) i += 1
      }
      if (i < len && (s.charAt(i) == 'e' || s.charAt(i) == 'E')) {
        i += 1
        if (i < len && (s.charAt(i) == '+' || s.charAt(i) == '-')) i += 1
        while (i < len && s.charAt(i).isDigit) i += 1
      }
      val raw = s.substring(start, i)
      raw.toDoubleOption.map(Json.Num(_)).toRight(s"Invalid number '$raw'")
    }

    private def parseArr(): Either[String, Json] = {
      i += 1 // '['
      skipWs()
      if (i < len && s.charAt(i) == ']') {
        i += 1
        return Right(Json.Arr(Nil))
      }
      val buf = List.newBuilder[Json]
      var done = false
      while (!done) {
        parseValue() match {
          case Left(err) => return Left(err)
          case Right(v) => buf += v
        }
        skipWs()
        if (i < len && s.charAt(i) == ',') {
          i += 1
        } else if (i < len && s.charAt(i) == ']') {
          i += 1
          done = true
        } else {
          return Left(s"Expected ',' or ']' at offset $i")
        }
      }
      Right(Json.Arr(buf.result()))
    }

    private def parseObj(): Either[String, Json] = {
      i += 1 // '{'
      skipWs()
      if (i < len && s.charAt(i) == '}') {
        i += 1
        return Right(Json.Obj(Nil))
      }
      val buf = List.newBuilder[(String, Json)]
      var done = false
      while (!done) {
        skipWs()
        val key = parseStr() match {
          case Left(err) => return Left(err)
          case Right(k) => k
        }
        skipWs()
        if (i >= len || s.charAt(i) != ':') return Left(s"Expected ':' at offset $i")
        i += 1
        parseValue() match {
          case Left(err) => return Left(err)
          case Right(v) => buf += (key -> v)
        }
        skipWs()
        if (i < len && s.charAt(i) == ',') {
          i += 1
        } else if (i < len && s.charAt(i) == '}') {
          i += 1
          done = true
        } else {
          return Left(s"Expected ',' or '}' at offset $i")
        }
      }
      Right(Json.Obj(buf.result()))
    }
  }
}
