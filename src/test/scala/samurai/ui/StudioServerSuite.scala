package samurai.ui

import java.net.URI
import java.net.http.{HttpClient, HttpRequest, HttpResponse}
import munit.FunSuite
import samurai.util.Json

class StudioServerSuite extends FunSuite {

  private val client = HttpClient.newHttpClient()

  private def httpGet(url: String): HttpResponse[String] = {
    val req = HttpRequest.newBuilder(URI.create(url)).GET().build()
    client.send(req, HttpResponse.BodyHandlers.ofString())
  }

  private def httpPostJson(url: String, body: Json): HttpResponse[String] = {
    val req = HttpRequest
      .newBuilder(URI.create(url))
      .header("Content-Type", "application/json")
      .POST(HttpRequest.BodyPublishers.ofString(body.compact))
      .build()
    client.send(req, HttpResponse.BodyHandlers.ofString())
  }

  test("Proof Samurai Studio serves UI assets, examples, live kernel check, hole inspection, extraction, prover, and docs") {
    val server = StudioServer.start(port = 0)
    try {
      // 1. Static UI assets
      val indexRes = httpGet(s"${server.url}/")
      assertEquals(indexRes.statusCode(), 200)
      assert(indexRes.body().contains("Proof Samurai Studio"))

      val cssRes = httpGet(s"${server.url}/styles.css")
      assertEquals(cssRes.statusCode(), 200)

      val jsRes = httpGet(s"${server.url}/app.js")
      assertEquals(jsRes.statusCode(), 200)

      val iconRes = httpGet(s"${server.url}/favicon.svg")
      assertEquals(iconRes.statusCode(), 200)
      assert(iconRes.body().contains("<svg"))

      // 2. Curated examples & stdlib
      val exJson = Json.parse(httpGet(s"${server.url}/api/examples").body()).toOption.get
      assertEquals(exJson.field("ok"), Some(Json.Bool(true)))
      assert(exJson.field("examples").flatMap(_.asArr).exists(_.length >= 8))

      // 3. Documentation endpoint (English and Japanese)
      val docsEnJson = Json.parse(httpGet(s"${server.url}/api/docs").body()).toOption.get
      assertEquals(docsEnJson.field("ok"), Some(Json.Bool(true)))
      assertEquals(docsEnJson.field("lang"), Some(Json.Str("en")))
      assert(docsEnJson.field("docs").flatMap(_.asArr).exists(_.length == 11))
      assert(
        docsEnJson
          .field("docs")
          .flatMap(_.asArr)
          .exists(_.exists(_.field("id") == Some(Json.Str("coc-cic"))))
      )

      val docsJaJson = Json.parse(httpGet(s"${server.url}/api/docs?lang=ja").body()).toOption.get
      assertEquals(docsJaJson.field("ok"), Some(Json.Bool(true)))
      assertEquals(docsJaJson.field("lang"), Some(Json.Str("ja")))
      assert(docsJaJson.field("docs").flatMap(_.asArr).exists(_.length == 11))
      assert(
        docsJaJson
          .field("docs")
          .flatMap(_.asArr)
          .flatMap(_.headOption)
          .flatMap(_.field("title"))
          .flatMap(_.asString)
          .exists(_.contains("はじめに"))
      )

      // 4. Live /api/check with valid axiom-free code
      val checkOk = Json
        .parse(
          httpPostJson(
            s"${server.url}/api/check",
            Json.obj(
              "file" -> Json.Str("Demo.samurai"),
              "source" -> Json.Str("import Prelude.*\nimport Nat.*\ntheorem t(a: Nat, b: Nat): a + b === b + a = by { arith }\n#eval 2 + 3")
            )
          ).body()
        )
        .toOption
        .get
      assertEquals(checkOk.field("ok"), Some(Json.Bool(true)))
      assertEquals(checkOk.field("isAxiomFree"), Some(Json.Bool(true)))

      // 5. Live /api/check with ?hole collects hole + suggestions
      val checkHole = Json
        .parse(
          httpPostJson(
            s"${server.url}/api/check",
            Json.obj(
              "file" -> Json.Str("Hole.samurai"),
              "source" -> Json.Str("import Prelude.*\nimport Nat.*\ntheorem h(a: Nat, b: Nat): a + b === b + a = by { ?help }")
            )
          ).body()
        )
        .toOption
        .get
      assertEquals(checkHole.field("hasHoles"), Some(Json.Bool(true)))
      assert(checkHole.field("holes").flatMap(_.asArr).exists(_.length == 1))

      // 6. Live /api/check with kernel error returns kindful hint
      val checkBad = Json
        .parse(
          httpPostJson(
            s"${server.url}/api/check",
            Json.obj(
              "file" -> Json.Str("Bad.samurai"),
              "source" -> Json.Str("import Prelude.*\nimport Nat.*\ndef loop(n: Nat): False = { loop(n) }")
            )
          ).body()
        )
        .toOption
        .get
      assertEquals(checkBad.field("ok"), Some(Json.Bool(false)))
      assert(checkBad.field("kindHint").flatMap(_.asString).exists(_.contains("Termination safety")))

      // 7. Live /api/extract to Scala 3, Haskell, and OCaml
      val extRes = Json
        .parse(
          httpPostJson(
            s"${server.url}/api/extract",
            Json.obj(
              "source" -> Json.Str("import Prelude.*\nimport Nat.*\ndef doubleN(n: Nat): Nat = n + n"),
              "target" -> Json.Str("scala3"),
              "strict" -> Json.Bool(true)
            )
          ).body()
        )
        .toOption
        .get
      assertEquals(extRes.field("ok"), Some(Json.Bool(true)))
      assert(extRes.field("code").flatMap(_.asString).exists(_.contains("def doubleN")))

      val extHs = Json
        .parse(
          httpPostJson(
            s"${server.url}/api/extract",
            Json.obj(
              "source" -> Json.Str("import Prelude.*\nimport Nat.*\ndef doubleN(n: Nat): Nat = n + n"),
              "target" -> Json.Str("haskell"),
              "strict" -> Json.Bool(true)
            )
          ).body()
        )
        .toOption
        .get
      assertEquals(extHs.field("ok"), Some(Json.Bool(true)))
      assert(extHs.field("code").flatMap(_.asString).exists(_.contains("doubleN :: Nat -> Nat")))

      val extMl = Json
        .parse(
          httpPostJson(
            s"${server.url}/api/extract",
            Json.obj(
              "source" -> Json.Str("import Prelude.*\nimport Nat.*\ndef doubleN(n: Nat): Nat = n + n"),
              "target" -> Json.Str("ocaml"),
              "strict" -> Json.Bool(true)
            )
          ).body()
        )
        .toOption
        .get
      assertEquals(extMl.field("ok"), Some(Json.Bool(true)))
      assert(extMl.field("code").flatMap(_.asString).exists(_.contains("let doubleN (n : nat) : nat =")))

      // 8. Live /api/proof interactive session
      val startProof = Json
        .parse(
          httpPostJson(
            s"${server.url}/api/proof",
            Json.obj(
              "method" -> Json.Str("startProof"),
              "params" -> Json.obj(
                "name" -> Json.Str("studioDemo"),
                "statement" -> Json.Str("forall (a: Nat, b: Nat) => a + b === b + a")
              )
            )
          ).body()
        )
        .toOption
        .get
      val sid = startProof.field("sessionId").flatMap(_.asString).get
      val rootState = startProof.field("rpc").flatMap(_.field("result")).flatMap(_.field("stateId")).flatMap(_.asInt).get

      val step1 = Json
        .parse(
          httpPostJson(
            s"${server.url}/api/proof",
            Json.obj(
              "sessionId" -> Json.Str(sid),
              "method" -> Json.Str("step"),
              "params" -> Json.obj("stateId" -> Json.Num(rootState), "tactic" -> Json.Str("intros(a, b)"))
            )
          ).body()
        )
        .toOption
        .get
      val state2 = step1.field("rpc").flatMap(_.field("result")).flatMap(_.field("stateId")).flatMap(_.asInt).get

      val step2 = Json
        .parse(
          httpPostJson(
            s"${server.url}/api/proof",
            Json.obj(
              "sessionId" -> Json.Str(sid),
              "method" -> Json.Str("step"),
              "params" -> Json.obj("stateId" -> Json.Num(state2), "tactic" -> Json.Str("arith"))
            )
          ).body()
        )
        .toOption
        .get
      assertEquals(step2.field("rpc").flatMap(_.field("result")).flatMap(_.field("kernelVerified")), Some(Json.Bool(true)))
    } finally {
      server.stop()
    }
  }
}
